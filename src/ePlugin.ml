open CErrors
open Pp
open Util
open Names
open Term
open Decl_kinds
open Libobject
open Globnames
open Proofview.Notations

(** Utilities *)

let translate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵉ")

(** Record of translation between globals *)

type effect = Libnames.reference

type translator = ETranslate.translator

let translator : translator MPmap.t ref =
  Summary.ref ~name:"Effect Global Table" MPmap.empty

type translator_obj =
| NewEffect of ModPath.t
| ExtendEffect of ModPath.t * (global_reference * global_reference) list

let declare_translator tr mp =
  let open ETranslate in
  assert (not (MPmap.mem mp tr));
  let empty = { effs = mp; refs = Refmap.empty } in
  MPmap.add mp empty tr

let extend_translator tr mp l =
  let open ETranslate in
  let defs = try MPmap.find mp tr with Not_found -> assert false in
  let refs = defs.refs in
  let fold accu (src, dst) = Refmap.add src dst accu in
  let refs = List.fold_left fold refs l in
  MPmap.update mp { defs with refs } tr

let cache_translator (_, l) = match l with
| NewEffect mp ->
  translator := declare_translator !translator mp
| ExtendEffect (mp, l) ->
  translator := extend_translator !translator mp l

let load_translator _ obj = cache_translator obj
let open_translator _ obj = cache_translator obj

let subst_translator (subst, obj) = match obj with
| NewEffect mp ->
  let mp' = Mod_subst.subst_mp subst mp in
  if mp' == mp then obj else NewEffect mp'
| ExtendEffect (mp, l) ->
  let mp' = Mod_subst.subst_mp subst mp in
  let map (src, dst) = (subst_global_reference subst src, subst_global_reference subst dst) in
  let l' = List.smartmap map l in
  if mp' == mp && l' == l then obj else ExtendEffect (mp', l')

let in_translator : translator_obj -> obj =
  declare_object { (default_object "FORCING TRANSLATOR") with
    cache_function = cache_translator;
    load_function = load_translator;
    open_function = open_translator;
    discharge_function = (fun (_, o) -> Some o);
    classify_function = (fun o -> Substitute o);
  }

(** Tactic *)

let empty_translator = Refmap.empty

let solve_evars env sigma c =
  let evdref = ref sigma in
  let c = Typing.e_solve_evars env evdref c in
  (!evdref, c)

let get_translator eff =
  let fail () = errorlabstrm ""
    (str "Effect " ++ Libnames.pr_reference eff ++ str " not found")
  in
  let (_, qid) = Libnames.qualid_of_reference eff in
  let eff = try Nametab.locate_module qid with Not_found -> fail () in
  let data = try MPmap.find eff !translator with Not_found -> fail () in
  (eff, data)

let translate_constant (eff, translator) cst ids =
  let id = match ids with
  | None -> translate_name (Nametab.basename_of_global (ConstRef cst))
  | Some [id] -> id
  | Some _ -> error "Not the right number of provided names"
  in
  (** Translate the type *)
  let typ = Universes.unsafe_type_of_global (ConstRef cst) in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, typ) = ETranslate.translate_type translator env sigma typ in
  let (sigma, typ) = solve_evars env sigma typ in
  let sigma, _ = Typing.type_of env sigma typ in
  let _uctx = Evd.evar_universe_context sigma in
  (** Define the term by tactic *)
  let body = Option.get (Global.body_of_constant cst) in
  let (sigma, body) = ETranslate.translate translator env sigma body in
  let (sigma, body) = solve_evars env sigma body in
(*   msg_info (Termops.print_constr body); *)
  let evdref = ref sigma in
  let () = Typing.e_check env evdref body typ in
  let sigma = !evdref in
  let (_, uctx) = Evd.universe_context sigma in
  let ce = Declare.definition_entry ~types:typ ~univs:uctx body in
  let cd = Entries.DefinitionEntry ce in
  let decl = (cd, IsProof Lemma) in
  let cst_ = Declare.declare_constant id decl in
  [ConstRef cst, ConstRef cst_]

let translate eff gr ids =
  let gr = Nametab.global gr in
  let (eff, translator) = get_translator eff in
  let ans = match gr with
  | ConstRef cst -> translate_constant (eff, translator) cst ids
  | _ -> error "Translation not handled."
  in
  let () = Lib.add_anonymous_leaf (in_translator (ExtendEffect (eff, ans))) in
  let msg_translate (src, dst) =
    Feedback.msg_info (str "Global " ++ Printer.pr_global src ++
    str " has been translated as " ++ Printer.pr_global dst ++ str ".")
  in
  List.iter msg_translate ans

(** Implementation in the forcing layer *)

let implement eff id typ idopt =
  let (eff, translator) = get_translator eff in
  let env = Global.env () in
  let id_ = match idopt with
  | None -> translate_name id
  | Some id -> id
  in
  let kind = Global, false, DefinitionBody Definition in
  let sigma = Evd.from_env env in
  let (typ, uctx) = Constrintern.interp_type env sigma typ in
  let sigma = Evd.from_ctx uctx in
  let (sigma, typ_) = ETranslate.translate_type translator env sigma typ in
  let (sigma, _) = Typing.type_of env sigma typ_ in
  let hook _ dst =
    (** Declare the original term as an axiom *)
    let param = (None, false, (typ, Evd.evar_context_universe_context uctx), None) in
    let cb = Entries.ParameterEntry param in
    let cst = Declare.declare_constant id (cb, IsDefinition Definition) in
    (** Attach the axiom to the forcing implementation *)
    Lib.add_anonymous_leaf (in_translator (ExtendEffect (eff, [ConstRef cst, dst])))
  in
  let hook ctx = Lemmas.mk_hook hook in
  let sigma, _ = Typing.type_of env sigma typ_ in
  let () = Lemmas.start_proof_univs id_ kind sigma typ_ hook in
  ()

(** Declaring a new effect *)

let declare_effect eff =
  let eff =
    try Nametab.locate_module (snd (Libnames.qualid_of_reference eff))
    with Not_found ->
      errorlabstrm "" (str "Unknown module " ++ Libnames.pr_reference eff)
  in
  Lib.add_anonymous_leaf (in_translator (NewEffect eff))

(** Error handling *)

let pr_global = function
| VarRef id -> str "Variable " ++ Nameops.pr_id id
| ConstRef cst -> str "Constant " ++ Constant.print cst
| IndRef (ind, _) -> str "Inductive " ++ MutInd.print ind
| ConstructRef ((ind, _), _) -> str "Inductive " ++ MutInd.print ind

let _ = register_handler begin function
| ETranslate.MissingGlobal gr ->
  let ref = Nametab.shortest_qualid_of_global Id.Set.empty gr in
  str "No translation for global " ++ Libnames.pr_qualid ref ++ str "."
| ETranslate.MissingPrimitive gr ->
  let ref = pr_global gr in
  str "Missing primitive: " ++ ref ++ str "."
| _ -> raise Unhandled
end
