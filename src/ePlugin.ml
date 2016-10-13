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

let translator : ETranslate.translator ref =
  Summary.ref ~name:"Forcing Global Table" Refmap.empty

type translator_obj = (global_reference * global_reference) list

let add_translator translator l =
  List.fold_left (fun accu (src, dst) -> Refmap.add src dst accu) translator l
							    
let cache_translator (_, l) =
  translator := add_translator !translator l

let load_translator _ l = cache_translator l
let open_translator _ l = cache_translator l
let subst_translator (subst, l) =
  let map (src, dst) = (subst_global_reference subst src, subst_global_reference subst dst) in
  List.map map l

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

let translate_constant cst ids =
  let id = match ids with
  | None -> translate_name (Nametab.basename_of_global (ConstRef cst))
  | Some [id] -> id
  | Some _ -> error "Not the right number of provided names"
  in
  (** Translate the type *)
  let typ = Universes.unsafe_type_of_global (ConstRef cst) in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, typ) = ETranslate.translate_type !translator env sigma typ in
  let (sigma, typ) = solve_evars env sigma typ in
  let sigma, _ = Typing.type_of env sigma typ in
  let _uctx = Evd.evar_universe_context sigma in
  (** Define the term by tactic *)
  let body = Option.get (Global.body_of_constant cst) in
  let (sigma, body) = ETranslate.translate !translator env sigma body in
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

let translate gr ids =
  let r = gr in
  let gr = Nametab.global gr in
  let ans = match gr with
  | ConstRef cst -> translate_constant cst ids
  | _ -> error "Translation not handled."
  in
  let () = Lib.add_anonymous_leaf (in_translator ans) in
  let msg_translate (src, dst) =
    Feedback.msg_info (str "Global " ++ Printer.pr_global src ++
    str " has been translated as " ++ Printer.pr_global dst ++ str ".")
  in
  List.iter msg_translate ans

(** Implementation in the forcing layer *)

let implement id typ idopt =
  let env = Global.env () in
  let id_ = match idopt with
  | None -> translate_name id
  | Some id -> id
  in
  let kind = Global, false, DefinitionBody Definition in
  let sigma = Evd.from_env env in
  let (typ, uctx) = Constrintern.interp_type env sigma typ in
  let sigma = Evd.from_ctx uctx in
  let (sigma, typ_) = ETranslate.translate_type !translator env sigma typ in
  let (sigma, _) = Typing.type_of env sigma typ_ in
  let hook _ dst =
    (** Declare the original term as an axiom *)
    let param = (None, false, (typ, Evd.evar_context_universe_context uctx), None) in
    let cb = Entries.ParameterEntry param in
    let cst = Declare.declare_constant id (cb, IsDefinition Definition) in
    (** Attach the axiom to the forcing implementation *)
    Lib.add_anonymous_leaf (in_translator [ConstRef cst, dst])
  in
  let hook ctx = Lemmas.mk_hook hook in
  let sigma, _ = Typing.type_of env sigma typ_ in
  let () = Lemmas.start_proof_univs id_ kind sigma typ_ hook in
  ()

(** Error handling *)

let _ = register_handler begin function
| ETranslate.MissingGlobal gr ->
  let ref = Nametab.shortest_qualid_of_global Id.Set.empty gr in
  str "No translation for global " ++ Libnames.pr_qualid ref ++ str "."
| _ -> raise Unhandled
end
