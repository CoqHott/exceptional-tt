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
  refs : global_reference Cmap.t;
  inds : MutInd.t Mindmap.t
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

type pcontext = {
  ptranslator : translator;
  penv_src : Environ.env;
  (** ⊢ Γ *)
  penv_tgt : Environ.env;
  (** ⊢ ⟦Γ⟧ *)
  penv_ptgt : Environ.env;
  (** ⊢ ⟦Γ⟧ε *)
}

let pname = function
| Anonymous -> Anonymous
| Name id -> Name (Id.of_string (Id.to_string id ^ "ε"))

let plift env t =
  let n = Environ.nb_rel env.penv_tgt - 1 in
  let subst = List.init n (fun i -> mkRel (2 * i + 2)) in
  Vars.substl subst (Vars.liftn (2 * n) (n + 1) t)

(* (Γ, x : A | ⟦Γ⟧, x : ⟦A⟧ | ⟦Γ⟧ε, x : ⟦A⟧, xε : ⟦A⟧ε x). *)
let push_passum na (t, te, tr) env =
  { env with
    penv_src = EConstr.push_rel (LocalAssum (na, t)) env.penv_src;
    penv_tgt = EConstr.push_rel (LocalAssum (na, te)) env.penv_tgt;
    penv_ptgt = EConstr.push_rel (LocalAssum (pname na, tr)) (EConstr.push_rel (LocalAssum (na, plift env te)) env.penv_ptgt);
  }

let push_pdef na (c, ce, cr) (t, te, tr) env = { env with
  penv_src = EConstr.push_rel (LocalDef (na, c, t)) env.penv_src;
  penv_tgt = EConstr.push_rel (LocalDef (na, ce, te)) env.penv_tgt;
  penv_ptgt = EConstr.push_rel (LocalDef (pname na, cr, tr)) (EConstr.push_rel (LocalDef (na, plift env ce, plift env te)) env.penv_ptgt);
}

let lift_rel_context n ctx =
  let fold k d accu =
    let d = Context.Rel.Declaration.map_constr (fun c -> Vars.liftn n k c) d in
    d :: accu
  in
  List.fold_right_i fold 1 ctx []

let check_type env sigma c t =
  let evdref = ref sigma in
  let () = Typing.e_check env.env_tgt evdref c t in
  !evdref

(** Coq-defined values *)

let effect_path =
  DirPath.make (List.map Id.of_string ["Effects"; "Effects"])

let make_kn name =
  KerName.make2 (MPfile effect_path) (Label.make name)

let prop_e = ConstRef (Constant.make1 (make_kn "Propᵉ"))
let type_e = ConstRef (Constant.make1 (make_kn "Typeᵉ"))
let el_e = ConstRef (Constant.make1 (make_kn "El"))
let prod_e = ConstRef (Constant.make1 (make_kn "Prodᵉ"))
let err_e = ConstRef (Constant.make1 (make_kn "Err"))
let typeval_e = ConstructRef ((MutInd.make1 (make_kn "type"), 0), 1)

let dummy = mkProp

let name_errtype = Id.of_string "E"
let name_err = Id.of_string "e"

(** Handling of globals *) 

let get_cst env cst =
  try Cmap.find cst env.translator.refs
  with Not_found -> raise (MissingGlobal (ConstRef cst))

let get_ind env (ind, n) =
  try (Mindmap.find ind env.translator.inds, n)
  with Not_found -> raise (MissingGlobal (IndRef (ind, n)))

let apply_global env sigma gr =
  let gr = match gr with
  | ConstructRef (ind, n) ->
    let ind = get_ind env ind in
    ConstructRef (ind, n)
  | IndRef ind -> IndRef (get_ind env ind)
  | ConstRef cst -> get_cst env cst
  | VarRef _ -> CErrors.user_err (str "Variables not handled")
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

let pfresh_global env sigma gr =
  try
    let (sigma, c) = Evd.fresh_global env.penv_ptgt sigma gr in
    (sigma, EConstr.of_constr c)
  with Not_found -> raise (MissingPrimitive gr)

(** Effect translation core *)

let element env sigma c =
  let (sigma, el) = fresh_global env sigma el_e in
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  (sigma, mkApp (el, [|e; c|]))

let translate_case_info env sigma ci mip =
  let nrealdecls = mip.mind_nrealdecls in
  let ci_ind = get_ind env ci.ci_ind in
  let ci_npar = ci.ci_npar + 1 in
  let ci_cstr_ndecls = Array.append ci.ci_cstr_ndecls [|1 + nrealdecls|] in
  let ci_cstr_nargs = Array.append ci.ci_cstr_nargs [|1 + mip.mind_nrealargs|] in
  let tags =
    false :: (** additional exception argument *)
    Context.Rel.to_tags (List.firstn nrealdecls mip.mind_arity_ctxt)
  in
  let ci_pp_info = { ci.ci_pp_info with
    cstr_tags = Array.append ci.ci_pp_info.cstr_tags [|tags|];
  } in
  { ci_ind; ci_npar; ci_cstr_ndecls; ci_cstr_nargs; ci_pp_info; }

let mk_default_ind env sigma (ind, u) =
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  let (_, mip) = Inductive.lookup_mind_specif env.env_src ind in
  let err = Array.length mip.mind_consnames + 1 in
  let ind = get_ind env ind in
  let (sigma, (ind, u)) = Evd.fresh_inductive_instance env.env_tgt sigma ind in
  let r = mkApp (mkConstructU ((ind, err), EInstance.make u), [|e|]) in
  (sigma, r)

(* From Γ ⊢ M : A produce [M] s.t. ⟦Γ⟧ ⊢ [M] : ⟦A⟧. *)
let rec otranslate env sigma c = match EConstr.kind sigma c with
| Rel n ->
  (sigma, mkRel n)
| Sort s ->
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  let (sigma, t) = fresh_global env sigma type_e in
  sigma, mkApp (t, [|e|])
| Cast (c, k, t) ->
  let (sigma, ce) = otranslate env sigma c in
  let (sigma, te) = otranslate_type env sigma t in
  let r = mkCast (ce, k, te) in
  (sigma, r)
| Prod (na, t, u) ->
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  let (sigma, p) = fresh_global env sigma prod_e in
  let (sigma, te) = otranslate_type env sigma t in
  let env = push_assum na (t, te) env in
  let (sigma, ue) = otranslate env sigma u in
  let ue = mkLambda (na, te, ue) in
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
| App (t, args) when isInd sigma t ->
  otranslate_ind env sigma (destInd sigma t) args
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
| Ind (ind, u) ->
  otranslate_ind env sigma (ind, u) [||]
| Construct (c, _) ->
  let (sigma, c) = apply_global env sigma (ConstructRef c) in
  (sigma, c)
| Case (ci, r, c, p) ->
  let (_, mip) = Inductive.lookup_mind_specif env.env_src ci.ci_ind in
  let cie = translate_case_info env sigma ci mip in
  let (ctx, r) = EConstr.decompose_lam_assum sigma r in
  let (sigma, env', ctxe) = otranslate_context env sigma ctx in
  let (sigma, ce) = otranslate env sigma c in
  let map sigma p = otranslate env sigma p in
  let (sigma, pe) = Array.fold_left_map map sigma p in
  let nE = Environ.nb_rel env'.env_tgt in
  (** The default constructor has as arguments the indices of the block plus an error *)
  let default_ctx = LocalAssum (Name name_err, mkRel (nE - 1)) :: List.tl ctxe in
  let default_case =
    (** Transform [Ind{I} params indices] into [Cstr{Iᴱ} params indices] *)
    let (ind, args) = Termops.decompose_app_vect sigma (get_type (List.hd ctxe)) in
    let (ind, u) = destInd sigma ind in
    let err = Array.length mip.mind_consnames + 1 in
    let args = Array.map (fun c -> Vars.lift 1 c) args in
    mkApp (mkConstructU ((ind, err), u), Array.append args [|mkRel 1|])
  in
  let (sigma, re, default) = otranslate_type_and_err env' sigma r in
  let re = it_mkLambda_or_LetIn re ctxe in
  let default = Vars.subst1 default_case (Vars.liftn 1 2 default) in
  let default = mkApp (default, [|mkRel 1|]) in
  let default = it_mkLambda_or_LetIn default default_ctx in
  let pe = Array.append pe [|default|] in
  let r = mkCase (cie, re, ce, pe) in
  (sigma, r)
| Fix (fi, recdef) ->
  let (sigma, recdefe) = otranslate_recdef env sigma recdef in
  let r = mkFix (fi, recdefe) in
  (sigma, r)
| CoFix (fi, recdef) ->
  let (sigma, recdefe) = otranslate_recdef env sigma recdef in
  let r = mkCoFix (fi, recdefe) in
  (sigma, r)
| Proj (p, c) -> assert false
| Meta _ -> assert false
| Evar _ -> assert false

and otranslate_recdef env sigma (nas, tys, bodies) =
  let fold i (env, sigma, ans) na t =
    let t = Vars.lift i t in
    let (sigma, te) = otranslate_type env sigma t in
    let env = push_assum na (t, te) env in
    (env, sigma, te :: ans)
  in
  let (env, sigma, tyse) = Array.fold_left2_i fold (env, sigma, []) nas tys in
  let tyse = Array.rev_of_list tyse in
  let (sigma, bodiese) = Array.fold_left_map (fun sigma c -> otranslate env sigma c) sigma bodies in
  (sigma, (nas, tyse, bodiese))

(* Special handling of types not to clutter the translation.
   From Γ ⊢ A : Type produce ⟦A⟧ s.t. ⟦Γ⟧ ⊢ ⟦A⟧ : Type. *)
and otranslate_type env sigma t = match EConstr.kind sigma t with
| App (c, args) when isInd sigma c ->
  let (ind, _) = destInd sigma c in
  let fold sigma c = otranslate env sigma c in
  let (sigma, args) = Array.fold_map fold sigma args in
  let (sigma, c) = apply_global env sigma (IndRef ind) in
  (sigma, mkApp (c, args))
| Ind (ind, _) ->
  let (sigma, c) = apply_global env sigma (IndRef ind) in
  (sigma, c)
| Prod (na, t, u) ->
  let (sigma, te) = otranslate_type env sigma t in
  let env = push_assum na (t, te) env in
  let (sigma, ue) = otranslate_type env sigma u in
  (sigma, mkProd (na, te, ue))
| _ ->
  let (sigma, t_) = otranslate env sigma t in
  let (sigma, t_) = element env sigma t_ in
  (sigma, t_)

(* From Γ ⊢ A : Type produce
   - ⟦A⟧ s.t. ⟦Γ⟧ ⊢ ⟦A⟧ : Type
   - [A]ᴱ s.t. ⟦Γ⟧ ⊢ [A]ᴱ : E → ⟦A⟧ *)
and otranslate_type_and_err env sigma t = match EConstr.kind sigma t with
| App (c, args) when isInd sigma c ->
  let (ind, u) = destInd sigma c in
  let fold sigma c = otranslate env sigma c in
  let (sigma, args) = Array.fold_map fold sigma args in
  let (sigma, c) = apply_global env sigma (IndRef ind) in
  let (sigma, ind_def) = mk_default_ind env sigma (ind, u) in
  let ind_def = mkApp (ind_def, args) in
  (sigma, mkApp (c, args), ind_def)
| Ind (ind, u) ->
  let (sigma, c) = apply_global env sigma (IndRef ind) in
  let (sigma, ind_def) = mk_default_ind env sigma (ind, u) in
  (sigma, c, ind_def)
| Prod (na, t, u) ->
  let (sigma, te) = otranslate_type env sigma t in
  let env = push_assum na (t, te) env in
  let (sigma, ue, def) = otranslate_type_and_err env sigma u in
  let def = mkApp (Vars.liftn 1 2 def, [| mkRel 2 |]) in
  let e = mkRel (Environ.nb_rel env.env_tgt - 1) in
  let prod_def = mkLambda (Name name_err, e, mkLambda (na, Vars.lift 1 te, def)) in
  (sigma, mkProd (na, te, ue), prod_def)
| _ ->
  let (sigma, t_) = otranslate env sigma t in
  let (sigma, err) = fresh_global env sigma err_e in
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  let t_def = mkApp (err, [|e; t_|]) in
  let (sigma, t_) = element env sigma t_ in
  (sigma, t_, t_def)

(** Special handling of potentially partially applied inductive types not to
    clutter the translation *)
and otranslate_ind env sigma (ind, u) args =
  let (mib, mip) = Inductive.lookup_mind_specif env.env_src ind in
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  let (sigma, c) = apply_global env sigma (IndRef ind) in
  let (sigma, typeval) = fresh_global env sigma typeval_e in
  let fold sigma c = otranslate env sigma c in
  let (sigma, args) = Array.fold_map fold sigma args in
  let (sigma, def) = mk_default_ind env sigma (ind, u) in
  if Int.equal (Array.length args) (mib.mind_nparams + mip.mind_nrealargs) then
    (** Fully applied *)
    let r = mkApp (typeval, [| e; mkApp (c, args); mkApp (def, args) |]) in
    (sigma, r)
  else
    (** Partially applied, we need to eta-expand it. *)
    assert false

(* From ⊢ Γ produce ⊢ ⟦Γ⟧ *)
and otranslate_context env sigma = function
| [] -> sigma, env, []
| LocalAssum (na, t) :: params ->
  let (sigma, env, ctx) = otranslate_context env sigma params in
  let (sigma, te) = otranslate_type env sigma t in
  (sigma, push_assum na (t, te) env, LocalAssum (na, te) :: ctx)
| LocalDef (na, b, t) :: params ->
  let (sigma, env, ctx) = otranslate_context env sigma params in
  let (sigma, te) = otranslate_type env sigma t in
  let (sigma, be) = otranslate env sigma b in
  (sigma, push_def na (b, be) (t, te) env, LocalDef (na, be, te) :: ctx)

let project env = {
  translator = env.ptranslator;
  env_src = env.penv_src;
  env_tgt = env.penv_tgt;
}

let top_decls env =
  List.firstn 2 (EConstr.rel_context env.penv_ptgt)

(* From Γ ⊢ M : A produce [M]ε s.t. ⟦Γ⟧ε ⊢ [M]ε : ⟦A⟧ [M]. *)
let rec ptranslate env sigma c = match EConstr.kind sigma c with
| Rel n ->
  (sigma, mkRel (2 * n - 1))
| Sort _ | Prod _ ->
  let (sigma, c_) = otranslate_type (project env) sigma c in
  let c_ = plift env c_ in
  let (sigma, r) = ptranslate_type env sigma c in
  let r = mkLambda (Anonymous, c_, r) in
  sigma, r
| Cast (c, k, t) ->
  assert false
| Lambda (na, t, u) ->
  let (sigma, t_) = otranslate_type (project env) sigma t in
  let (sigma, tr) = ptranslate_type env sigma t in
  let nenv = push_passum na (t, t_, tr) env in
  let ctx = top_decls nenv in
  let (sigma, ur) = ptranslate nenv sigma u in
  let r = it_mkLambda_or_LetIn ur ctx in
  (sigma, r)
| LetIn (na, c, t, u) ->
  assert false
| App (t, args) when isInd sigma t ->
  assert false
| App (t, args) ->
  let (sigma, tr) = ptranslate env sigma t in
  let fold t (sigma, accu) =
    let (sigma, t_) = otranslate (project env) sigma t in
    let t_ = plift env t_ in
    let (sigma, tr) = ptranslate env sigma t in
    (sigma, t_ :: tr :: accu)
  in
  let (sigma, argsr) = Array.fold_right fold args (sigma, []) in
  let r = applist (tr, argsr) in
  (sigma, r)
| Var id ->
  assert false
| Const (p, _) ->
  assert false
| Ind (ind, u) ->
  assert false
| Construct (c, _) ->
  assert false
| Case (ci, r, c, p) ->
  assert false
| Fix (fi, recdef) ->
  assert false
| CoFix (fi, recdef) ->
  assert false
| Proj (p, c) -> assert false
| Meta _ -> assert false
| Evar _ -> assert false

(* From Γ ⊢ A : Type produce ⟦A⟧ε s.t. ⟦Γ⟧ε, x : ⟦A⟧ ⊢ ⟦A⟧ε : Type. *)
and ptranslate_type env sigma c = match EConstr.kind sigma c with
| Sort s ->
  let (sigma, el) = pfresh_global env sigma el_e in
  let e = mkRel (Environ.nb_rel env.penv_ptgt + 1) in
  let (sigma, s) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.penv_ptgt sigma InType in
  let r = mkArrow (mkApp (el, [|e; mkRel 1|])) (mkSort s) in
  (sigma, r)
| Prod (na, t, u) ->
  let (sigma, t_) = otranslate_type (project env) sigma t in
  let (sigma, tr) = ptranslate_type env sigma t in
  let nenv = push_passum na (t, t_, tr) env in
  let (sigma, ur) = ptranslate_type nenv sigma u in
  let ur = Vars.liftn 1 4 ur in
  let ur = Vars.subst1 (mkApp (mkRel 3, [| mkRel 2 |])) ur in
  let ctx = lift_rel_context 1 (top_decls nenv) in
  let r = it_mkProd_or_LetIn ur ctx in
  (sigma, r)
| _ ->
  let (sigma, cr) = ptranslate env sigma c in
  (sigma, mkApp (Vars.lift 1 cr, [| mkRel 1 |]))

let make_context translator env sigma =
  let (sigma, s) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env sigma InType in
  let e = name_errtype in
  let env_tgt = Environ.push_rel (LocalAssum (Name e, Constr.mkSort s)) env in
  let env = {
    translator;
    env_src = env;
    env_tgt;
  } in
  (sigma, env)

let make_pcontext ptranslator env sigma =
  let (sigma, s) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env sigma InType in
  let e = name_errtype in
  let env_tgt = Environ.push_rel (LocalAssum (Name e, Constr.mkSort s)) env in
  let env = {
    ptranslator;
    penv_src = env;
    penv_tgt = env_tgt;
    penv_ptgt = env_tgt;
  } in
  (sigma, env)

let push_context (ctx, ctx_) env =
  let env_src = Environ.push_rel_context ctx env.env_src in
  let env_tgt = Environ.push_rel_context ctx_ env.env_tgt in
  { env with env_src; env_tgt }

let get_exception env =
  let rels = EConstr.rel_context env.env_tgt in
  List.last rels

let get_pexception env =
  let rels = EConstr.rel_context env.penv_ptgt in
  List.last rels

let translate translator env0 sigma c =
  let (sigma, env) = make_context translator env0 sigma in
  let (sigma, c_) = otranslate env sigma c in
  let decl = get_exception env in
  let c_ = mkLambda_or_LetIn decl c_ in
  let (sigma, _) = Typing.type_of env.env_src sigma c_ in
  (*
  let () =
    try
      let (sigma, env) = make_pcontext translator env0 sigma in
      let (sigma, c_) = ptranslate env sigma c in
      let decl = get_pexception env in
      let c_ = mkLambda_or_LetIn decl c_ in
      Feedback.msg_notice (Printer.pr_econstr_env env.penv_src sigma c_)
    with _ -> ()
  in
  *)
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

let translate_failure id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᴱ")

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
  let translator = { env.translator with inds = Mindmap.add mind mind env.translator.inds } in
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

let translate_inductive_body env sigma mind0 mind n ind0 ind =
  let typename = translate_internal_name ind.mind_entry_typename in
  let constructors = List.map translate_name ind.mind_entry_consnames in
  let nindices = List.length ind0.mind_arity_ctxt - List.length mind0.mind_params_ctxt in
  let arity_ctx, _ = List.chop nindices ind0.mind_arity_ctxt in
  let (sigma, arity_env, arity_ctx') = translate_context env sigma arity_ctx in
  let (sigma, sort) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.env_tgt sigma InType in
  let arity = it_mkProd_or_LetIn (mkSort sort) arity_ctx' in
  let (sigma, _) = Typing.type_of env.env_tgt sigma arity in
  let (sigma, lc) = translate_constructors env sigma mind0 mind ind0 ind in
  let lc = List.map (fun c -> EConstr.to_constr sigma c) lc in
  let fail_name = translate_failure ind.mind_entry_typename in
  let fail_arg (n, accu) = function
  | LocalAssum _ -> (succ n, mkRel n :: accu)
  | LocalDef _ -> (succ n, accu)
  in
  let (_, fail_args) = List.fold_left fail_arg (2, []) (Environ.rel_context arity_env.env_tgt) in
  let n = 2 + n + Environ.nb_rel arity_env.env_tgt in
  let fail_case = applist (mkRel n, fail_args) in
  let fail_ctx = LocalAssum (Anonymous, mkRel (1 + List.length ind0.mind_arity_ctxt)) :: arity_ctx' in
  let fail_case = it_mkProd_or_LetIn fail_case fail_ctx in
  let ind = { ind with
    mind_entry_typename = typename;
    mind_entry_arity = EConstr.to_constr sigma arity;
    mind_entry_consnames = constructors @ [fail_name];
    mind_entry_lc = lc @ [EConstr.to_constr sigma fail_case];
  } in
  (sigma, ind)

let sign_level env evd sign =
  let fold d (lev, env) = match d with
  | LocalDef _ -> lev, push_rel d env
  | LocalAssum (_, t) ->
    let s = Retyping.get_type_of env evd (EConstr.of_constr t) in
    let s = destSort evd (Reductionops.clos_whd_flags CClosure.all env evd s) in
    let u = univ_of_sort (ESorts.kind evd s) in
    (Univ.sup u lev, push_rel d env)
  in
  fst (List.fold_right fold sign (Univ.type0m_univ, env))

let extract_level env evd min tys =
  let map ty =
    let ctx, concl = Reduction.dest_prod_assum env ty in
    sign_level env evd (LocalAssum (Anonymous, concl) :: ctx)
  in
  let sorts = List.map map tys in
  List.fold_left Univ.sup min sorts

let is_impredicative env u =
  u = Prop Null || (is_impredicative_set env && u = Prop Pos)

let is_flexible_sort evd u =
  match Univ.Universe.level u with
  | Some l -> Evd.is_flexible_level evd l
  | None -> false

let inductive_levels env sigma arities inds =
  let destarities = List.map (fun x -> x, Reduction.dest_arity env x) arities in
  let levels = List.map (fun (x,(ctx,a)) ->
    if a = Prop Null then None
    else Some (univ_of_sort a)) destarities
  in
  let map tys (arity, (ctx, du)) =
    let len = List.length tys in
    let minlev = Sorts.univ_of_sort du in
    let minlev =
      if len > 1 && not (is_impredicative env du) then
        Univ.sup minlev Univ.type0_univ
      else minlev
    in
    let minlev =
      (** Indices contribute. *)
      if Indtypes.is_indices_matter () && List.length ctx > 0 then (
        let ilev = sign_level env sigma ctx in
          Univ.sup ilev minlev)
      else minlev
    in
    let clev = extract_level env sigma minlev tys in
    (clev, minlev, len)
  in
  let cstrs_levels, min_levels, sizes = CList.split3 (List.map2 map inds destarities) in
  (* Take the transitive closure of the system of constructors *)
  (* level constraints and remove the recursive dependencies *)
  let levels' = Universes.solve_constraints_system (Array.of_list levels)
    (Array.of_list cstrs_levels) (Array.of_list min_levels)
  in
  let sigma, arities =
    CList.fold_left3 (fun (sigma, arities) cu (arity,(ctx,du)) len ->
      if is_impredicative env du then
        (** Any product is allowed here. *)
        sigma, arity :: arities
      else (** If in a predicative sort, or asked to infer the type,
               we take the max of:
               - indices (if in indices-matter mode)
               - constructors
               - Type(1) if there is more than 1 constructor
           *)
        (** Constructors contribute. *)
        let sigma =
          if Sorts.is_set du then
            if not (Evd.check_leq sigma cu Univ.type0_univ) then
              raise (Indtypes.InductiveError Indtypes.LargeNonPropInductiveNotInType)
            else sigma
          else sigma
            (* Evd.set_leq_sort env sigma (Type cu) du *)
        in
        let sigma =
          if len >= 2 && Univ.is_type0m_univ cu then
           (** "Polymorphic" type constraint and more than one constructor,
               should not land in Prop. Add constraint only if it would
               land in Prop directly (no informative arguments as well). *)
            Evd.set_leq_sort env sigma (Prop Pos) du
          else sigma
        in
        let duu = Sorts.univ_of_sort du in
        let sigma =
          if not (Univ.is_small_univ duu) && Univ.Universe.equal cu duu then
            if is_flexible_sort sigma duu && not (Evd.check_leq sigma Univ.type0_univ duu) then
              Evd.set_eq_sort env sigma (Prop Null) du
            else sigma
          else Evd.set_eq_sort env sigma (Type cu) du
        in
          (sigma, arity :: arities))
    (sigma, []) (Array.to_list levels') destarities sizes
  in
  (sigma, List.rev arities)

(** Infer the universe constraints for constructors *)
let retype_inductive env sigma params inds =
  let env = Environ.pop_rel_context (Environ.nb_rel env) env in
  let mk_arities sigma ind =
    let arity = it_mkProd_or_LetIn (EConstr.of_constr ind.mind_entry_arity) params in
    let (sigma, _) = Typing.type_of env sigma arity in
    (sigma, arity)
  in
  let (sigma, extarities) = List.fold_left_map mk_arities sigma inds in
  let fold env c ind = EConstr.push_rel (LocalAssum (Name ind.mind_entry_typename, c)) env in
  let env = List.fold_left2 fold env extarities inds in
  let env = EConstr.push_rel_context params env in
  let fold sigma ind =
    let fold sigma c =
      let (sigma, _) = Typing.type_of env sigma (EConstr.of_constr c) in
      sigma
    in
    let sigma = List.fold_left fold sigma ind.mind_entry_lc in
    (sigma, ind.mind_entry_lc)
  in
  let sigma, constructors = List.fold_left_map fold sigma inds in
  let arities = List.map (fun ind -> ind.mind_entry_arity) inds in
  let (sigma, arities) = inductive_levels env sigma arities constructors in
  let params = List.map (fun d -> EConstr.to_rel_decl sigma d) params in
  let sigma, nf = Evarutil.nf_evars_and_universes sigma in
  let map ind arity = { ind with
    mind_entry_arity = nf arity;
    mind_entry_lc = List.map nf ind.mind_entry_lc;
  } in
  let inds = List.map2 map inds arities in
  let params = Rel.map nf params in
  sigma, inds, params

let translate_inductive translator env mind0 (mind : Entries.mutual_inductive_entry) =
  let sigma = Evd.from_env env in
  let (sigma, env) = make_context translator env sigma in
  let (sigma, env, _) = translate_context env sigma mind0.mind_params_ctxt in
  let inds = List.combine (Array.to_list mind0.mind_packets) mind.mind_entry_inds in
  let inds = List.mapi (fun i (ind, ind0) -> (i, ind, ind0)) inds in
  let map sigma (n, ind0, ind) = translate_inductive_body env sigma mind0 mind n ind0 ind in
  let sigma, inds = List.fold_left_map map sigma inds in
  let sigma, inds, params = retype_inductive env.env_tgt sigma (EConstr.rel_context env.env_tgt) inds in
  let params = List.map to_local_entry params in
  let uctx = UState.context (Evd.evar_universe_context sigma) in
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
