open CErrors
open Pp
open Util
open Names
open Context
open Term
open Decl_kinds
open Libobject
open Globnames
open Proofview.Notations

(** Utilities *)

let translate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵉ")

let translate_internal_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵒ")

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

let declare_constant id uctx c t =
  let ce = Declare.definition_entry ~types:t ~univs:uctx c in
  let cd = Entries.DefinitionEntry ce in
  let decl = (cd, IsProof Lemma) in
  let cst_ = Declare.declare_constant id decl in
  cst_

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
  let (sigma, translator) = ETranslate.make_context translator env sigma in
  let (sigma, typ) = ETranslate.translate_type translator sigma typ in
  let (sigma, typ) = solve_evars env sigma typ in
  let sigma, _ = Typing.type_of env sigma typ in
  let _uctx = Evd.evar_universe_context sigma in
  (** Define the term by tactic *)
  let body = Option.get (Global.body_of_constant cst) in
  let (sigma, body) = ETranslate.translate translator sigma body in
  let (sigma, body) = solve_evars env sigma body in
(*   msg_info (Termops.print_constr body); *)
  let evdref = ref sigma in
  let () = Typing.e_check env evdref body typ in
  let sigma = !evdref in
  let (_, uctx) = Evd.universe_context sigma in
  let cst_ = declare_constant id uctx body typ in
  [ConstRef cst, ConstRef cst_]

let sort_of_elim sigma body =
  let open Declarations in
  if List.mem Sorts.InType body.mind_kelim then
    let (sigma, s) = Evd.new_sort_variable Evd.univ_flexible sigma in
    let sigma =
      if Array.length body.mind_consnames > 1 then
        Evd.set_leq_sort Environ.empty_env sigma (Prop Pos) s
      else sigma
    in
    (sigma, mkSort s)
  else (sigma, mkProp)

let sort_of env sigma c =
  let evdref = ref sigma in
  let sort = Typing.e_sort_of env evdref c in
  (!evdref, sort)

let substl_rel_context subst ctx =
  let ctx = Vars.substl subst (it_mkProd_or_LetIn mkProp ctx) in
  let (ctx, _) = Term.decompose_prod_assum ctx in
  ctx


(** From a kernel inductive body construct an entry for the inductive. There
    are slight mismatches in the representation, in particular in the handling
    of contexts. See {!Declarations} and {!Entries}. *)
let translate_inductive_aux translator ind =
  let open Declarations in
  let open Entries in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (mib, _) = Global.lookup_inductive ind in
  let (sigma, info) = ETranslate.make_context translator env sigma in
  let params = mib.mind_params_ctxt in
  let (sigma, params_) = ETranslate.translate_context info sigma params in
  (** First pass: translate the inductive types *)
  let map_ind body (sigma, accu) =
    let arity = body.mind_arity_ctxt in
    let arity, _ = List.chop (List.length arity - List.length params) arity in
    let info = ETranslate.push_context (params, params_) info in
    let (sigma, s) = sort_of_elim sigma body in
    let (sigma, s_) = sort_of_elim sigma body in
    let (sigma, arity_) = ETranslate.translate_context info sigma arity in
    let arity = Termops.it_mkProd_or_LetIn s arity in
    let arity_ = Termops.it_mkProd_or_LetIn s_ arity_ in
    let (sigma, _) = Typing.type_of (Environ.push_rel_context params_ env) sigma arity_ in
    (sigma, (arity, arity_, body) :: accu)
  in
  let (sigma, bodies) = Array.fold_right map_ind mib.mind_packets (sigma, []) in
  (** Build the constructors context *)
  let map_arities (t, t_, body) =
    let open Rel.Declaration in
    let ind = it_mkProd_or_LetIn t params in
    let ind_ = it_mkProd_or_LetIn t_ params_ in
    let typename_ = translate_internal_name body.mind_typename in
    (LocalAssum (Name body.mind_typename, ind), LocalAssum (Name typename_, ind_))
  in
  let all_arities = List.map map_arities bodies in
  let (arities, arities_) = List.split all_arities in
  let cparams = Termops.lift_rel_context (List.length arities) params @ List.rev arities in
  let cparams_ = Termops.lift_rel_context (List.length arities_) params_ @ List.rev arities_ in
  let (sigma, info) = ETranslate.make_context translator env sigma in
  let cinfo = ETranslate.push_context (cparams, cparams_) info in
  (** Second pass: translate the constructors *)
  let map_body (_, arity_, body) (sigma, accu) =
    let template = match body.mind_arity with
    | RegularArity _ -> false
    | TemplateArity _ -> true
    in
    let consnames = CArray.map_to_list translate_internal_name body.mind_consnames in
    let fold_cstr c (sigma, accu) =
      let (_, c) = Term.decompose_prod_n_assum (List.length params) c in
      (** Handle specially the return type of the constructor *)
      let (ctx, c) = Term.decompose_prod_assum c in
      let (sigma, ctx_) = ETranslate.otranslate_context cinfo sigma ctx in
      (** Mangle the argument types to replace self by Free (self) *)
      let relparams = List.mapi (fun i _ -> mkRel (i + 1)) params_ in
      let map_indparams c (sigma, accu) =
        let free = ETranslate.free_algebra cinfo in
        let (sigma, free) = Evd.fresh_global (Environ.push_rel_context cparams_ env) sigma free in
        (** FIXME for mutual inductives *)
        let ind = mkRel (2 * List.length params_ + 1) in
        let args = List.mapi (fun i _ -> mkRel (i + 1)) params_ in
        let head = mkApp (free, [| applist (ind, args) |]) in
        let ind = it_mkLambda_or_LetIn head params_ in
        (sigma, ind :: accu)
      in
      let (sigma, indparams) = List.fold_right map_indparams arities_ (sigma, []) in
      (** Leave parameters unchanged, but replace inductives by their free variant *)
      let subst = relparams @ indparams in
      let ctx_ = substl_rel_context subst ctx_ in
      let hinfo = ETranslate.push_context (ctx, ctx_) cinfo in
      let (sigma, c_) = ETranslate.otranslate hinfo sigma c in
      let c_ = it_mkProd_or_LetIn c_ ctx_ in
      (** Retypecheck for universe constraints *)
      let (sigma, sc) = sort_of (Environ.push_rel_context cparams_ env) sigma c_ in
      let (_, s_) = Term.destArity arity_ in
      let sigma = Evd.set_leq_sort Environ.empty_env sigma sc s_ in
      (sigma, c_ :: accu)
    in
    let (sigma, constructors_) = Array.fold_right fold_cstr body.mind_nf_lc (sigma, []) in
    let body_ = {
      mind_entry_typename = translate_internal_name body.mind_typename;
      mind_entry_arity = arity_;
      mind_entry_template = template;
      mind_entry_consnames = consnames;
      mind_entry_lc = constructors_;
    } in
    (sigma, body_ :: accu)
  in
  (** Wrap up *)
  let (sigma, bodies_) = List.fold_right map_body bodies (sigma, []) in
  let map_param = function
  | Rel.Declaration.LocalAssum (Name na, t) -> (na, Entries.LocalAssumEntry t)
  | Rel.Declaration.LocalDef (Name na, b, t) -> (na, Entries.LocalDefEntry b)
  | _ -> assert false
  in
  let params_ = List.map map_param params_ in
  let (_, uctx) = Evd.universe_context sigma in
  let record = match mib.mind_record with
  | None -> None
  | Some None -> Some None
  | Some (Some (id, _, _)) -> Some (Some (translate_internal_name id))
  in
  {
    mind_entry_record = record;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = params_;
    mind_entry_inds = bodies_;
    mind_entry_polymorphic = mib.mind_polymorphic;
    mind_entry_universes = uctx;
    mind_entry_private = mib.mind_private;
  }

(** Build the wrapper around an inductive type *)
let get_inductive_type (eff, translator) ind ind_ i body body_ =
  let open Declarations in
  let name = translate_name body.mind_typename in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, info) = ETranslate.make_context translator env sigma in
  (** From [I] produce [fun params indices => Free (I params indices)] *)
  let ctx = body_.mind_arity_ctxt in
  let tenv = Environ.push_rel_context ctx env in
  let args = List.mapi (fun i _ -> mkRel (i + 1)) ctx in
  let args = List.rev args in
  let free = ETranslate.free_algebra info in
  let (sigma, free) = Evd.fresh_global tenv sigma free in
  let (sigma, pind) = Evd.fresh_inductive_instance env sigma (ind_, i) in
  let c_ = applist (mkIndU pind, args) in
  let c_ = it_mkLambda_or_LetIn (mkApp (free, [|c_|])) ctx in
  let (sigma, t_) = Typing.type_of env sigma c_ in
  let (_, uctx) = Evd.universe_context sigma in
  (name, uctx, c_, t_)

(** Build the wrapper around the constructors of an inductive type *)
let get_constructors (eff, translator) ind ind_ i body body_ =
  let open Declarations in
  let map_constructor j id =
    let src = (ind, i), succ j in
    let name = translate_name id in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let (sigma, info) = ETranslate.make_context translator env sigma in
    (** FIXME: handle mutual inductives *)
    let subst = [mkInd (ind_, 0)] in
    let t_ = Vars.substl subst body_.mind_nf_lc.(j) in
    let (ctx, concl) = Term.decompose_prod_assum t_ in
    let (sigma, info) = ETranslate.make_context translator env sigma in
    let args = List.mapi (fun i _ -> mkRel (i + 1)) ctx in
    let args = List.rev args in
    let (sigma, constr) = Evd.fresh_constructor_instance env sigma ((ind_, i), succ j) in
    let c_ = applist (mkConstructU constr, args) in
    let (sigma, ret) = Evd.fresh_global env sigma (ETranslate.ret info) in
    let c_ = mkApp (ret, [| concl; c_ |]) in
    let c_ = it_mkLambda_or_LetIn c_ ctx in
    let (sigma, t_) = Typing.type_of env sigma c_ in
    let (_, uctx) = Evd.universe_context sigma in
    (src, name, uctx, c_, t_)
  in
  Array.to_list (Array.mapi map_constructor body.mind_consnames)

(** Register the wrapping of the inductive type and its constructors *)
let translate_inductive_defs (eff, translator) ind ind_ mind mind_ =
  let open Declarations in
  (** Declare the wrapped inductive types *)
  let map_types i b b_ = get_inductive_type (eff, translator) ind ind_ i b b_ in
  let types = Array.map2_i map_types mind.mind_packets mind_.mind_packets in
  let map_types i (id, uctx, c, t) =
    let cst_ = declare_constant id uctx c t in
    (IndRef (ind, i), ConstRef cst_)
  in
  let types = Array.to_list (Array.mapi map_types types) in
  (** Declare the wrapped inductive constructors *)
  let fold accu (src, tgt) = Refmap.add src tgt accu in
  let refs = List.fold_left fold translator.ETranslate.refs types in
  let translator = { translator with ETranslate.refs } in
  let map_constructors i b b_ = get_constructors (eff, translator) ind ind_ i b b_ in
  let constructors = Array.map2_i map_constructors mind.mind_packets mind_.mind_packets in
  let constructors = List.concat (Array.to_list constructors) in
  let map_constructors (src, id, uctx, c, t) =
    let cst_ = declare_constant id uctx c t in
    (ConstructRef src, ConstRef cst_)
  in
  let constructors = List.map map_constructors constructors in
  types @ constructors

let translate_inductive (eff, translator) ind =
  let open Declarations in
  let (mind, _) = Global.lookup_inductive ind in
  let mind_ = translate_inductive_aux translator ind in
  let ((_, kn), _) = Declare.declare_mind mind_ in
  let ind_ = Global.mind_of_delta_kn kn in
  let mind_ = Global.lookup_mind ind_ in
  translate_inductive_defs (eff, translator) (fst ind) ind_ mind mind_

let translate eff gr ids =
  let gr = Nametab.global gr in
  let (eff, translator) = get_translator eff in
  let ans = match gr with
  | ConstRef cst -> translate_constant (eff, translator) cst ids
  | IndRef ind -> translate_inductive (eff, translator) ind
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
  let (sigma, translator) = ETranslate.make_context translator env sigma in
  let (sigma, typ_) = ETranslate.translate_type translator sigma typ in
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
