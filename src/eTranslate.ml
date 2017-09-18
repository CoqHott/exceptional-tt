open Util
open Context
open Rel.Declaration
open Names
open Term
open EConstr
open Entries
open Declarations
open Environ
open Globnames
open Pp

exception MissingGlobal of global_reference
exception MissingPrimitive of global_reference

type translator = {
  refs : global_reference Refmap.t;
}

type context = {
  translator : translator;
  env_src : Environ.env;
  env_tgt : Environ.env;
}

let push_assum na (t, te) env = { env with
  env_src = EConstr.push_rel (LocalAssum (na, t)) env.env_src;
  env_tgt = EConstr.push_rel (LocalAssum (na, te)) env.env_tgt;
}

let push_def na (c, ce) (t, te) env = { env with
  env_src = EConstr.push_rel (LocalDef (na, c, t)) env.env_src;
  env_tgt = EConstr.push_rel (LocalDef (na, ce, te)) env.env_tgt;
}

let check_type env sigma c t =
  let evdref = ref sigma in
  let () = Typing.e_check env.env_tgt evdref c t in
  !evdref

(** Coq-defined values *)

let effect_path =
  DirPath.make (List.map Id.of_string ["Effects"; "Effects"])

let make_kn name =
  KerName.make2 (MPfile effect_path) (Label.make name)

let type_e = ConstRef (Constant.make1 (make_kn "Typeᵉ"))
let el_e = ConstRef (Constant.make1 (make_kn "El"))
let prod_e = ConstRef (Constant.make1 (make_kn "Prodᵉ"))

let dummy = mkProp

(** Handling of globals *) 

let apply_global env sigma gr =
  let gr =
    try Refmap.find gr env.translator.refs
    with Not_found -> raise (MissingGlobal gr)
  in
  let (sigma, c) = Evd.fresh_global env.env_tgt sigma gr in
  let c = EConstr.of_constr c in
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  (sigma, mkApp (c, [|e|]))

let fresh_global env sigma gr =
  try
    let (sigma, c) = Evd.fresh_global env.env_tgt sigma gr in
    (sigma, EConstr.of_constr c)
  with Not_found -> raise (MissingPrimitive gr)

(** Effect translation core *)

let element env sigma c =
  let (sigma, el) = fresh_global env sigma el_e in
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  (sigma, mkApp (el, [|e; c|]))

let mkType t err = assert false

let rec otranslate env sigma c = match EConstr.kind sigma c with
| Rel n ->
  (sigma, mkRel n)
| Sort s ->
  begin match EConstr.ESorts.kind sigma s with
  | Prop Null ->
    CErrors.user_err (str "Prop not handled yet")
  | Prop Pos ->
    assert false
  | Type _ ->
    let e = mkRel (Environ.nb_rel env.env_tgt) in
    let (sigma, t) = fresh_global env sigma type_e in
    sigma, mkApp (t, [|e|])
  end
| Cast (c, k, t) ->
  let (sigma, ce) = otranslate env sigma c in
  let (sigma, te) = otranslate_type env sigma t in
  let r = mkCast (ce, k, te) in
  (sigma, r)
| Prod (na, t, u) ->
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  let (sigma, p) = fresh_global env sigma prod_e in
  let (sigma, te) = otranslate env sigma t in
  let (sigma, tTe) = element env sigma te in
  let env = push_assum na (t, tTe) env in
  let (sigma, ue) = otranslate env sigma u in
  let ue = mkLambda (na, tTe, ue) in
  let r = mkApp (p, [|e; te; ue|]) in
  (sigma, r)
| Lambda (na, t, u) ->
  let (sigma, te) = otranslate_type env sigma t in
  let env = push_assum na (t, te) env in
  let (sigma, ue) = otranslate env sigma u in
  let r = mkLambda (na, te, ue) in
  (sigma, r)
| LetIn (na, c, t, u) ->
  let (sigma, ce) = otranslate env sigma c in
  let (sigma, te) = otranslate_type env sigma t in
  let env = push_def na (c, ce) (t, te) env in
  let (sigma, ue) = otranslate env sigma u in
  let r = mkLetIn (na, ce, te, ue) in
  (sigma, r)
| App (t, args) ->
  let (sigma, te) = otranslate env sigma t in
  let fold (sigma, argse) arg =
    let (sigma, arge) = otranslate env sigma arg in
    (sigma, arge :: argse)
  in
  let (sigma, argse) = Array.fold_left fold (sigma, []) args in
  let r = mkApp (te, Array.rev_of_list argse) in
  (sigma, r)
| Var id ->
  let (sigma, c) = apply_global env sigma (VarRef id) in
  (sigma, c)
| Const (p, _) ->
  let (sigma, c) = apply_global env sigma (ConstRef p) in
  (sigma, c)
| Ind (ind, _) ->
  let (sigma, c) = apply_global env sigma (IndRef ind) in
  (sigma, c)
| Construct (c, _) ->
  let (sigma, c) = apply_global env sigma (ConstructRef c) in
  (sigma, c)
| Case (ci, r, c, p) ->
  assert false
| Fix f -> assert false
| CoFix f -> assert false
| Proj (p, c) -> assert false
| Meta _ -> assert false
| Evar _ -> assert false

(** Special handling of types not to clutter the translation *)
and otranslate_type env sigma t = match EConstr.kind sigma t with
| App (c, args) when isInd sigma c ->
  let (ind, _) = destInd sigma c in
  let fold sigma c = otranslate env sigma c in
  let (sigma, args) = Array.fold_map fold sigma args in
  let (sigma, c) = apply_global env sigma (IndRef ind) in
  (sigma, mkApp (c, args))
| Prod (na, t, u) ->
  let (sigma, te) = otranslate_type env sigma t in
  let env = push_assum na (t, te) env in
  let (sigma, ue) = otranslate_type env sigma u in
  (sigma, mkProd (na, te, ue))
| _ ->
  let (sigma, t_) = otranslate env sigma t in
  let (sigma, t_) = element env sigma t_ in
  (sigma, t_)

let make_context translator env sigma =
  let (sigma, s) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env sigma InType in
  let e = Id.of_string "E" in
  let env_tgt = Environ.push_rel (LocalAssum (Name e, Constr.mkSort s)) env in
  let env = {
    translator;
    env_src = env;
    env_tgt;
  } in
  (sigma, env)

let push_context (ctx, ctx_) env =
  let env_src = Environ.push_rel_context ctx env.env_src in
  let env_tgt = Environ.push_rel_context ctx_ env.env_tgt in
  { env with env_src; env_tgt }

let get_exception env =
  let rels = EConstr.rel_context env.env_tgt in
  List.last rels

let translate translator env sigma c =
  let (sigma, env) = make_context translator env sigma in
  let (sigma, c_) = otranslate env sigma c in
  let decl = get_exception env in
  let c_ = mkLambda_or_LetIn decl c_ in
  let (sigma, _) = Typing.type_of env.env_src sigma c_ in
  (sigma, c_)

let translate_type translator env sigma c =
  let (sigma, env) = make_context translator env sigma in
  let (sigma, c_) = otranslate_type env sigma c in
  let decl = get_exception env in
  let c_ = mkProd_or_LetIn decl c_ in
  let (sigma, _) = Typing.type_of env.env_src sigma c_ in
  (sigma, c_)

let translate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵉ")

let translate_internal_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵒ")

let rec translate_context env sigma = function
| [] -> sigma, env, []
| LocalAssum (na, t) :: params ->
  let t = EConstr.of_constr t in
  let (sigma, env, ctx) = translate_context env sigma params in
  let (sigma, te) = otranslate_type env sigma t in
  let (sigma, _) = Typing.type_of env.env_tgt sigma te in
  (sigma, push_assum na (t, te) env, LocalAssum (na, te) :: ctx)
| LocalDef (na, b, t) :: params ->
  let b = EConstr.of_constr b in
  let t = EConstr.of_constr t in
  let (sigma, env, ctx) = translate_context env sigma params in
  let (sigma, te) = otranslate_type env sigma t in
  let (sigma, be) = otranslate env sigma b in
  let (sigma, _) = Typing.type_of env.env_tgt sigma te in
  let sigma = check_type env sigma be te in
  (sigma, push_def na (b, be) (t, te) env, LocalDef (na, be, te) :: ctx)

let to_local_entry = function
| LocalAssum (Name id, t) -> (id, Entries.LocalAssumEntry t)
| LocalDef (Name id, b, t) -> (id, Entries.LocalDefEntry b)
| _ -> assert false

(** Locally extend a translator to fake an inductive definition *)
let extend_inductive env mind0 mind =
  let open Univ in
  let univs = match mind0.mind_universes with
  | Monomorphic_ind _ -> Monomorphic_ind UContext.empty
  | Polymorphic_ind _ -> Polymorphic_ind AUContext.empty
  | Cumulative_ind _ -> Polymorphic_ind AUContext.empty (** FIXME *)
  in
  (** Dummy inductive. It is only used for its universe context, that we set to
      be empty. *)
  let mbi = { mind0 with mind_universes = univs } in
  let ind_name = Lib.make_kn (translate_internal_name mind0.mind_packets.(0).mind_typename) in
  let mind = MutInd.make1 ind_name in
  let env_tgt = Environ.add_mind mind mbi env.env_tgt in
  let fold (n, accu) _ =
    let gr = IndRef (mind, n) in
    let accu = { refs = Refmap.add gr gr accu.refs } in
    (succ n, accu)
  in
  let _, translator = Array.fold_left fold (0, env.translator) mind0.mind_packets in 
  mind, { env with translator; env_tgt }

let abstract_mind sigma mind n k c =
  let rec aux k c = match EConstr.kind sigma c with
  | Rel m ->
    if m <= k then c
    else mkRel (k + m)
  | Ind ((ind, m), _) when MutInd.equal mind ind ->
    mkRel (k + m + 1)
  | _ ->
    map_with_binders sigma succ aux k c
  in
  aux k c

let translate_constructors env sigma mind0 mind ind0 ind =
  let mutind, env = extend_inductive env mind0 mind in
  let mk_ind n = mkInd (mutind, n) in
  let nblock = Array.length mind0.mind_packets in
  let subst0 = List.init nblock mk_ind in
  let map sigma t =
    (** A bit of term mangling: indices in the context referring to the
        inductive types we're building do not have the right type. *)
    let t = EConstr.of_constr t in
    let t = Vars.substnl subst0 (Environ.nb_rel env.env_src) t in
    let (sigma, te) = otranslate_type env sigma t in
    let te = abstract_mind sigma mutind nblock (Environ.nb_rel env.env_tgt) te in
    (sigma, te)
  in
  List.fold_left_map map sigma ind.mind_entry_lc

let translate_inductive_body env sigma mind0 mind ind0 ind =
  let typename = translate_internal_name ind.mind_entry_typename in
  let constructors = List.map translate_name ind.mind_entry_consnames in
  let nindices = List.length ind0.mind_arity_ctxt - List.length mind0.mind_params_ctxt in
  let arity_ctx, _ = List.chop nindices ind0.mind_arity_ctxt in
  let (sigma, _, arity_ctx') = translate_context env sigma arity_ctx in
  let (sigma, sort) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.env_tgt sigma InType in
  let arity = it_mkProd_or_LetIn (mkSort sort) arity_ctx' in
  let (sigma, _) = Typing.type_of env.env_tgt sigma arity in
  let (sigma, lc) = translate_constructors env sigma mind0 mind ind0 ind in
(*   let fold sigma c = check_type env sigma c (mkSort sort) in *)
(*   let sigma = List.fold_left fold sigma lc in *)
  let lc = List.map (fun c -> EConstr.to_constr sigma c) lc in
  let ind = { ind with
    mind_entry_typename = typename;
    mind_entry_arity = EConstr.to_constr sigma arity;
    mind_entry_consnames = constructors;
    mind_entry_lc = lc;
  } in
  (sigma, ind)

(** Infer the universe constraints for constructors *)
let retype_inductive env sigma params inds =
  let env = Environ.pop_rel_context (Environ.nb_rel env) env in
  let mk_arities sigma ind =
    let arity = it_mkProd_or_LetIn (EConstr.of_constr ind.mind_entry_arity) params in
    let (sigma, _) = Typing.type_of env sigma arity in
    (sigma, arity)
  in
  let (sigma, arities) = List.fold_left_map mk_arities sigma inds in
  let env = List.fold_left (fun env c -> EConstr.push_rel (LocalAssum (Anonymous, c)) env) env arities in
  let env = EConstr.push_rel_context params env in
  (** Check that all constructors have the corresponding type from their block *)
  let fold sigma ind =
    Feedback.msg_notice (Printer.pr_constr ind.mind_entry_arity);
(*     let t = EConstr.of_constr ind.mind_entry_arity in *)
    let fold sigma c =
      let c = EConstr.of_constr c in
(*       let evdref = ref sigma in *)
(*       let () = Typing.e_check env evdref c t in *)
(*       !evdref *)
      let (sigma, _) = Typing.type_of env sigma c in
      sigma
    in
    List.fold_left fold sigma ind.mind_entry_lc
  in
  List.fold_left fold sigma inds

let translate_inductive translator env mind0 (mind : Entries.mutual_inductive_entry) =
  let sigma = Evd.from_env env in
  let (sigma, env) = make_context translator env sigma in
  let (sigma, env, _) = translate_context env sigma mind0.mind_params_ctxt in
  let inds = List.combine (Array.to_list mind0.mind_packets) mind.mind_entry_inds in
  let map sigma (ind0, ind) = translate_inductive_body env sigma mind0 mind ind0 ind in
  let sigma, inds = List.fold_left_map map sigma inds in
  let sigma = retype_inductive env.env_tgt sigma (EConstr.rel_context env.env_tgt) inds in
  let params = List.map to_local_entry (Environ.rel_context env.env_tgt) in
  let (_, uctx) = Evd.universe_context sigma in
  let univs = match mind.mind_entry_universes with
  | Monomorphic_ind_entry _ -> Monomorphic_ind_entry uctx
  | Polymorphic_ind_entry _ -> Polymorphic_ind_entry uctx
  | Cumulative_ind_entry _ -> Polymorphic_ind_entry uctx (** FIXME *)
  in
  let mind = { mind with
    mind_entry_inds = inds;
    mind_entry_params = params;
    mind_entry_universes = univs;
  } in
  mind
