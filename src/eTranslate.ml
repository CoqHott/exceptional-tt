module CVars = Vars

open Util
open Context
open Rel.Declaration
open Names
open Term
open EConstr
open Entries
open Declarations
open Globnames
open Pp

type effect = global_reference option

exception MissingGlobal of effect * global_reference
exception MissingPrimitive of global_reference

type 'a global_translation =
| GlobGen of 'a
  (** Implementation generic over the type of exceptions *)
| GlobImp of 'a Refmap.t
  (** For every type of exceptions, a specialized implementation. *)

type translator = {
  refs : global_reference global_translation Cmap.t;
  inds : MutInd.t global_translation Mindmap.t;
  prefs : global_reference global_translation Cmap.t;
  pinds : MutInd.t global_translation Mindmap.t;
  wrefs : global_reference global_translation Cmap.t;
  winds : MutInd.t global_translation Mindmap.t;
}

type context = {
  error : global_reference option;
  (** Whether the translation is relativized to a specific error type *)
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
  perror : global_reference option;
  (** Whether the translation is relativized to a specific error type *)
  ptranslator : translator;
  penv_src : Environ.env;
  (** ⊢ Γ *)
  penv_tgt : Environ.env;
  (** ⊢ ⟦Γ⟧ *)
  penv_ptgt : Environ.env;
  (** ⊢ ⟦Γ⟧ε *)
}

let translate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵉ")

let translate_internal_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵒ")

let translate_failure id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᴱ")

let ptranslate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᴿ")

let ptranslate_internal_name = ptranslate_name

let pname = function
| Anonymous -> Anonymous
| Name id -> Name (ptranslate_name id)

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
  penv_ptgt = EConstr.push_rel (LocalDef (pname na, Vars.lift 1 cr, tr)) (EConstr.push_rel (LocalDef (na, plift env ce, plift env te)) env.penv_ptgt);
}

let lift_rel_context n ctx =
  let fold k d accu =
    let d = Context.Rel.Declaration.map_constr (fun c -> Vars.liftn n k c) d in
    d :: accu
  in
  List.fold_right_i fold 1 ctx []

(** Coq-defined values *)

let effect_path =
  DirPath.make (List.map Id.of_string ["Effects"; "Weakly"])

let make_kn name =
  KerName.make2 (MPfile effect_path) (Label.make name)

(* let prop_e = ConstRef (Constant.make1 (make_kn "Propᵉ")) *)
let type_e = ConstRef (Constant.make1 (make_kn "Typeᵉ"))
let el_e = ConstRef (Constant.make1 (make_kn "El"))
let prod_e = ConstRef (Constant.make1 (make_kn "Prodᵉ"))
let err_e = ConstRef (Constant.make1 (make_kn "Err"))
let typeval_e = ConstructRef ((MutInd.make1 (make_kn "type"), 0), 1)

let param_modality =
  let ind = MutInd.make1 (make_kn "ParamMod") in
  IndRef (ind, 0)


let name_errtype = Id.of_string "E"
let name_err = Id.of_string "e"  

(** Handling of globals *) 

let get_instance err = function
| GlobGen x -> true, x
| GlobImp m ->
  match err with
  | None -> raise Not_found (** No generic implementation *)
  | Some gr -> false, Refmap.find gr m

let instantiate_error err env sigma gen c_ = match err with
| None -> (sigma, c_)
| Some err ->
  if gen then
    let (sigma, err) = Evd.fresh_global env sigma err in
    (sigma, mkApp (c_, [| EConstr.of_constr err |]))
  else (sigma, c_)

let get_cst env cst =
  try get_instance env.error (Cmap.find cst env.translator.refs)
  with Not_found -> raise (MissingGlobal (env.error, ConstRef cst))

let get_ind env (ind, n) =
  try
    let gen, ind = get_instance env.error (Mindmap.find ind env.translator.inds) in
    gen, (ind, n)
  with Not_found -> raise (MissingGlobal (env.error, IndRef (ind, n)))

let get_pcst env cst =
  try get_instance env.perror (Cmap.find cst env.ptranslator.prefs)
  with Not_found -> raise (MissingGlobal (env.perror, ConstRef cst))

let get_pind env (ind, n) =
  try
    let gen, ind = get_instance env.perror (Mindmap.find ind env.ptranslator.pinds) in
    gen, (ind, n)
  with Not_found -> raise (MissingGlobal (env.perror, IndRef (ind, n)))

let apply_global env sigma gr =
  let gen, gr = match gr with
  | ConstructRef (ind, n) ->
    let gen, ind = get_ind env ind in
    gen, ConstructRef (ind, n)
  | IndRef ind ->
    let gen, ind = get_ind env ind in
    gen, IndRef ind
  | ConstRef cst -> get_cst env cst
  | VarRef _ -> CErrors.user_err (str "Variables not handled")
  in
  let (sigma, c) = Evd.fresh_global env.env_tgt sigma gr in
  let c = EConstr.of_constr c in
  if gen then
    let e = mkRel (Environ.nb_rel env.env_tgt) in
    (sigma, mkApp (c, [|e|]))
  else
    (sigma, c)

let apply_pglobal env sigma gr =
  let gen, gr = match gr with
  | ConstructRef (ind, n) ->
    let gen, ind = get_pind env ind in
    gen, ConstructRef (ind, n)
  | IndRef ind ->
    let gen, ind = get_pind env ind in
    gen, IndRef ind
  | ConstRef cst -> get_pcst env cst
  | VarRef _ -> CErrors.user_err (str "Variables not handled")
  in
  let (sigma, c) = Evd.fresh_global env.penv_ptgt sigma gr in
  let c = EConstr.of_constr c in
  if gen then
    let e = mkRel (Environ.nb_rel env.penv_ptgt) in
    (sigma, mkApp (c, [|e|]))
  else
    (sigma, c)

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
  let gen, ci_ind = get_ind env ci.ci_ind in
  let nrealdecls = mip.mind_nrealdecls in
  let nrealargs = mip.mind_nrealargs in
  let ci_npar = if gen then 1 + ci.ci_npar else ci.ci_npar in
  let ci_cstr_ndecls = Array.append ci.ci_cstr_ndecls [|1 + nrealdecls|] in
  let ci_cstr_nargs = Array.append ci.ci_cstr_nargs [|1 + nrealargs|] in
  let tags =
    false :: (** additional exception argument *)
    Context.Rel.to_tags (List.firstn nrealdecls mip.mind_arity_ctxt)
  in
  let ci_pp_info = { ci.ci_pp_info with
    ind_tags = (not gen) :: ci.ci_pp_info.ind_tags;
    cstr_tags = Array.append ci.ci_pp_info.cstr_tags [|tags|];
  } in
  { ci_ind; ci_npar; ci_cstr_ndecls; ci_cstr_nargs; ci_pp_info; }

let ptranslate_case_info env sigma ci mip =
  let gen, ci_ind = get_pind env ci.ci_ind in
  let ci_npar = if gen then 1 + 2 * ci.ci_npar else 2 * ci.ci_npar in
  let map n = 2 * n in
  let ci_cstr_ndecls = Array.map map ci.ci_cstr_ndecls in
  let ci_cstr_nargs = Array.map map ci.ci_cstr_nargs in
  let rec dup = function
  | [] -> []
  | x :: l -> x :: x :: (dup l)
  in
  let ci_pp_info = {
    ind_tags = (not gen) :: dup ci.ci_pp_info.ind_tags;
    cstr_tags = Array.map (fun l -> (not gen) :: dup l) ci.ci_pp_info.cstr_tags;
    style = ci.ci_pp_info.style;
  } in
  { ci_ind; ci_npar; ci_cstr_ndecls; ci_cstr_nargs; ci_pp_info; }

let mk_default_ind env sigma (ind, u) =
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  let (_, mip) = Inductive.lookup_mind_specif env.env_src ind in
  let err = Array.length mip.mind_consnames + 1 in
  let gen, ind = get_ind env ind in
  let (sigma, (ind, u)) = Evd.fresh_inductive_instance env.env_tgt sigma ind in
  let r = mkConstructU ((ind, err), EInstance.make u) in
  let r = if gen then mkApp (r, [|e|]) else r in
  (sigma, r)

let mk_default_primitive_record env sigma (ind, u) =
  let (modd, dir, lab) = (MutInd.repr3 (fst ind)) in 
  let cst = Constant.make3 modd dir lab in 
  let (gen, default) = get_cst env cst in 
  let (sigma, r) = fresh_global env sigma default in 
  (sigma, gen, EInstance.kind sigma (snd (destConst sigma r)), r) 

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
  let (sigma, pe) = Array.fold_map map sigma p in
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
| Proj (p, c) ->
  let constant = Names.Projection.constant p in 
  let unfolded = Names.Projection.unfolded p in
  let _, glob_constante = get_cst env constant in
  let constante = Globnames.destConstRef glob_constante in
  let proje = Names.Projection.make constante unfolded in
  let (sigma, ce) = otranslate env sigma c in
  (sigma, mkProj (proje, ce))
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
  let (sigma, bodiese) = Array.fold_map (fun sigma c -> otranslate env sigma c) sigma bodies in
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
  let fold sigma c = otranslate env sigma c in
  let (sigma, args) = Array.fold_map fold sigma args in
  if Inductive.is_primitive_record (mib, mip) then
    (** Primitive default constructor 
        This is wrong *)
    let e_var = mkRel (Environ.nb_rel env.env_tgt) in
    let (sigma, c) = apply_global env sigma (IndRef ind) in
    let (sigma, gen, _, def) = mk_default_primitive_record env sigma (ind, u) in
    let (sigma, typeval) = fresh_global env sigma typeval_e in
    let r = mkApp (typeval, [| e_var; mkApp (c, args); mkApp (def, args) |]) in
    let () = assert false in 
    (sigma, r)
  else if Int.equal (Array.length args) (mib.mind_nparams + mip.mind_nrealargs) then
    (** Fully applied *)
    let e = mkRel (Environ.nb_rel env.env_tgt) in
    let (sigma, c) = apply_global env sigma (IndRef ind) in
    let (sigma, typeval) = fresh_global env sigma typeval_e in
    let (sigma, def) = mk_default_ind env sigma (ind, u) in
    let r = mkApp (typeval, [| e; mkApp (c, args); mkApp (def, args) |]) in
    (sigma, r)
  else
    (** Partially applied, we need to eta-expand it. *)
    let gen, ind = get_ind env ind in
    let (_, mip) = Inductive.lookup_mind_specif env.env_src ind in
    let (sigma, (ind, u)) = Evd.fresh_inductive_instance env.env_tgt sigma ind in
    let subst c = CVars.subst_instance_constr u c in
    let nctx = List.length mip.mind_arity_ctxt in
    let map d =
      let d = Rel.Declaration.map_constr subst d in
      of_rel_decl d
    in
    let ctx = List.map map mip.mind_arity_ctxt in
    let (sigma, typeval) = fresh_global env sigma typeval_e in
    let make_arg (n, accu) = function
    | LocalAssum _ -> (succ n, mkRel n :: accu)
    | LocalDef _ -> (succ n, accu)
    in
    let (_, arity) = List.fold_left make_arg (1, []) mip.mind_arity_ctxt in
    let u = EInstance.make u in
    let typ = applist (mkIndU (ind, u), arity) in
    let def_c = (ind, Array.length mip.mind_consnames) in
    let def = applist (mkConstructU (def_c, u), arity) in 
    let r = mkApp (typeval, [| mkRel nctx; typ; def |]) in
    let r = it_mkLambda_or_LetIn r ctx in
    let r = if gen then mkApp (r, [| mkRel (Environ.nb_rel env.env_tgt) |]) else r in
    let r = mkApp (r, args) in
    (sigma, r)

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
  error = env.perror;
  translator = env.ptranslator;
  env_src = env.penv_src;
  env_tgt = env.penv_tgt;
}

let top_decls env =
  List.firstn 2 (EConstr.rel_context env.penv_ptgt)

(* From Γ ⊢ M : A produce [M]ε s.t. ⟦Γ⟧ε ⊢ [M]ε : ⟦A⟧ [M]. *)
let rec optranslate env sigma c0 = match EConstr.kind sigma c0 with
| Rel n ->
  (sigma, mkRel (2 * n - 1))
| Sort _ | Prod _ ->
  let (sigma, c_) = otranslate_type (project env) sigma c0 in
  let c_ = plift env c_ in
  let (sigma, r) = optranslate_type env sigma c0 in
  let r = mkLambda (Anonymous, c_, r) in
  (sigma, r)
| Cast (c, k, t) ->
  let (sigma, c_) = otranslate (project env) sigma c in
  let (sigma, cr) = optranslate env sigma c in
  let (sigma, tr) = optranslate_type env sigma t in
  let tr = Vars.subst1 (plift env c_) tr in
  let r = mkCast (cr, k, tr) in
  (sigma, r)
| Lambda (na, t, u) ->
  let (sigma, t_) = otranslate_type (project env) sigma t in
  let (sigma, tr) = optranslate_type env sigma t in
  let nenv = push_passum na (t, t_, tr) env in
  let ctx = top_decls nenv in
  let (sigma, ur) = optranslate nenv sigma u in
  let r = it_mkLambda_or_LetIn ur ctx in
  (sigma, r)
| LetIn (na, c, t, u) ->
  let (sigma, c_) = otranslate (project env) sigma c in
  let (sigma, cr) = optranslate env sigma c in
  let (sigma, t_) = otranslate_type (project env) sigma t in
  let (sigma, tr) = optranslate_type env sigma t in
  let nenv = push_pdef na (c, c_, cr) (t, t_, tr) env in
  let ctx = top_decls nenv in
  let (sigma, ur) = optranslate nenv sigma u in
  let r = it_mkLambda_or_LetIn ur ctx in
  (sigma, r)
| App (t, args) ->
  let (sigma, tr) = optranslate env sigma t in
  let (primitive, params) = 
    if isConstruct sigma t then
      let ((ind, c), u) = destConstruct sigma t in
      let specif = Inductive.lookup_mind_specif env.penv_ptgt ind in 
      let primitive = Inductive.is_primitive_record specif in 
      let args = Inductive.inductive_params specif in
      (primitive, args)
    else
      (false, 0)
  in
  let (sigma, te) = 
    if primitive then otranslate (project env) sigma (mkApp (t, args)) else (sigma, mkRel 0) in
  let fold i t (sigma, accu) =
    let (sigma, t_) = otranslate (project env) sigma t in
    let t_ = plift env t_ in
    let (sigma, tr) = optranslate env sigma t in
    let arg = tr :: accu in 
    let arg = 
      if primitive && params < i then 
          arg
      else if primitive &&  params == i then 
          te :: arg
      else
        t_ :: arg
    in
    (sigma, arg)
  in
  let (sigma, argsr) = Array.fold_right_i fold args (sigma, []) in
  let r = applist (tr, argsr) in
  (sigma, r)
| Var id ->
  apply_pglobal env sigma (VarRef id)
| Const (p, _) ->
  let (sigma, c) = apply_pglobal env sigma (ConstRef p) in
  (sigma, c)
| Ind (ind, _) ->
  let (sigma, c) = apply_pglobal env sigma (IndRef ind) in
  (sigma, c)
| Construct (c, _) ->
  let (sigma, c) = apply_pglobal env sigma (ConstructRef c) in
  (sigma, c)
| Case (ci, r, c, p) ->
  let (_, mip) = Inductive.lookup_mind_specif env.penv_src ci.ci_ind in
  let cir = ptranslate_case_info env sigma ci mip in
  let (sigma, cr) = optranslate env sigma c in
  let map sigma p = optranslate env sigma p in
  let (sigma, pr) = Array.fold_map map sigma p in
  let (ctx, r) = EConstr.decompose_lam_assum sigma r in
  let (sigma, nenv, ctxr) = optranslate_context env sigma ctx in
  let (sigma, rr) = optranslate_type nenv sigma r in
  let c0 = Vars.lift (List.length ctx) c0 in
  let (ci, r, _, p) = destCase sigma c0 in
  let c0 = mkCase (ci, r, mkRel 1, p) in
  let (sigma, ce) = otranslate (project nenv) sigma c0 in
  let ce = plift nenv ce in
  let rr = it_mkLambda_or_LetIn (Vars.subst1 ce rr) ctxr in
  let r = mkCase (cir, rr, cr, pr) in
  (sigma, r)
| Fix (fi, recdef) ->
  optranslate_fixpoint env sigma fi recdef
| CoFix (fi, recdef) ->
  CErrors.user_err (str "Cofixpoints not handled yet")
| Proj (p, c) -> assert false
| Meta _ -> assert false
| Evar _ -> assert false

(* From Γ ⊢ A : Type produce ⟦A⟧ε s.t. ⟦Γ⟧ε, x : ⟦A⟧ ⊢ ⟦A⟧ε : Type. *)
and optranslate_type env sigma c = match EConstr.kind sigma c with
| Sort s ->
  let (sigma, el) = pfresh_global env sigma el_e in
  let e = mkRel (Environ.nb_rel env.penv_ptgt + 1) in
  let (sigma, s) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.penv_ptgt sigma InType in
  let r = mkArrow (mkApp (el, [|e; mkRel 1|])) (mkSort s) in
  (sigma, r)
| Prod (na, t, u) ->
  let (sigma, t_) = otranslate_type (project env) sigma t in
  let (sigma, tr) = optranslate_type env sigma t in
  let nenv = push_passum na (t, t_, tr) env in
  let (sigma, ur) = optranslate_type nenv sigma u in
  let ur = Vars.liftn 1 4 ur in
  let ur = Vars.subst1 (mkApp (mkRel 3, [| mkRel 2 |])) ur in
  let ctx = lift_rel_context 1 (top_decls nenv) in
  let r = it_mkProd_or_LetIn ur ctx in
  (sigma, r)
| _ ->
  let (sigma, cr) = optranslate env sigma c in
  (sigma, mkApp (Vars.lift 1 cr, [| mkRel 1 |]))

(* From ⊢ Γ produce ⊢ ⟦Γ⟧ε *)
and optranslate_context env sigma = function
| [] -> sigma, env, []
| LocalAssum (na, t) :: params ->
  let (sigma, env, ctx) = optranslate_context env sigma params in
  let (sigma, t_) = otranslate_type (project env) sigma t in
  let (sigma, tr) = optranslate_type env sigma t in
  let nenv = push_passum na (t, t_, tr) env in
  let decl = top_decls nenv in
  (sigma, nenv, decl @ ctx)
| LocalDef (na, c, t) :: params ->
  let (sigma, env, ctx) = optranslate_context env sigma params in
  let (sigma, c_) = otranslate (project env) sigma c in
  let (sigma, cr) = optranslate env sigma c in
  let (sigma, t_) = otranslate_type (project env) sigma t in
  let (sigma, tr) = optranslate_type env sigma t in
  let nenv = push_pdef na (c, c_, cr) (t, t_, tr) env in
  let decl = top_decls nenv in
  (sigma, nenv, decl @ ctx)

and optranslate_fixpoint env sigma (idx, i) (nas, tys, bds) =
  let fail () = CErrors.user_err (str "Fixpoint not handled yet") in
  let map i f =
    let (ctx, f) = EConstr.decompose_lam_assum sigma f in
    let len = List.length ctx in
    match EConstr.kind sigma f with
    | Case (ci, r, c, p) ->
      let () = match EConstr.kind sigma c with
      | Rel j ->
        if not (Int.equal (len - i) j) then fail ()
      | _ -> fail ()
      in
      (ctx, ci, r, p)
    | _ -> fail ()
  in
  let (sigma, fixe) = otranslate (project env) sigma (mkFix ((idx, i), (nas, tys, bds))) in
  let bds = Array.map2 map idx bds in
  let fold i (env, sigma, ans) na t =
    let t = Vars.lift i t in
    let (sigma, te) = otranslate_type (project env) sigma t in
    let (sigma, tr) = optranslate_type env sigma t in
    let env = push_passum na (t, te, tr) env in
    (env, sigma, tr :: ans)
  in
  let (env, sigma, tysr) = Array.fold_left2_i fold (env, sigma, []) nas tys in
  let fold (n, sigma) (ctx0, ci, r, p) =
    let (sigma, nenv, ctx0r) = optranslate_context env sigma ctx0 in
    let (_, mip) = Inductive.lookup_mind_specif nenv.penv_src ci.ci_ind in
    let cir = ptranslate_case_info nenv sigma ci mip in
    let cr = mkRel 1 in
    let map sigma p = optranslate nenv sigma p in
    let (sigma, pr) = Array.fold_map map sigma p in
    let (ctx, r) = EConstr.decompose_lam_assum sigma r in
    let (sigma, nenv, ctxr) = optranslate_context nenv sigma ctx in
    let (sigma, rr) = optranslate_type nenv sigma r in
    let c0 = mkRel (n - 1 + List.length ctx0 + List.length ctx) in
    let (sigma, ce) = otranslate (project nenv) sigma c0 in
    let ce = plift nenv ce in
    let rr = it_mkLambda_or_LetIn (Vars.subst1 ce rr) ctxr in
    let r = it_mkLambda_or_LetIn (mkCase (cir, rr, cr, pr)) ctx0 in
    Feedback.msg_notice (
      str "CTX " ++
      Printer.pr_rel_context_of env.penv_ptgt sigma ++
      fnl () ++
      str "TRM " ++ 
      Printer.pr_econstr_env env.penv_ptgt sigma r
    );
    ((n + 1, sigma), r)
  in
  let tysr = Array.rev_of_list tysr in
  let idxr = Array.map (fun i -> 2 * i + 1) idx in
  let nasr = Array.map pname nas in
  let ((_, sigma), bdsr) = Array.fold_map fold (0, sigma) bds in
  let r = mkFix ((idxr, i), (nasr, tysr, bdsr)) in
  (sigma, r)

let make_error err env sigma = match err with
| None ->
  let (sigma, s) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env sigma InType in
  let d = LocalAssum (Name name_errtype, Constr.mkSort s) in
  (sigma, d)
| Some gr ->
  let (sigma, s) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env sigma InType in
  let (sigma, c) = Evd.fresh_global env sigma gr in
  let d = LocalDef (Name name_errtype, c, Constr.mkSort s) in
  (sigma, d)

let make_context error translator env sigma =
  let (sigma, decl) = make_error error env sigma in
  let env_tgt = Environ.push_rel decl env in
  let env = {
    error;
    translator;
    env_src = env;
    env_tgt;
  } in
  (sigma, env)

let make_pcontext perror ptranslator env sigma =
  let (sigma, decl) = make_error perror env sigma in
  let env_tgt = Environ.push_rel decl env in
  let env = {
    perror;
    ptranslator;
    penv_src = env;
    penv_tgt = env_tgt;
    penv_ptgt = env_tgt;
  } in
  (sigma, env)

let get_exception env =
  let rels = EConstr.rel_context env.env_tgt in
  List.last rels

let get_pexception env =
  let rels = EConstr.rel_context env.penv_ptgt in
  List.last rels

let translate err translator env0 sigma c =
  let (sigma, env) = make_context err translator env0 sigma in
  let (sigma, c_) = otranslate env sigma c in
  let decl = get_exception env in
  let c_ = mkLambda_or_LetIn decl c_ in
  let (sigma, _) = Typing.type_of env.env_src sigma c_ in
  (sigma, c_)

let ptranslate err translator env0 sigma c =
  let (sigma, env) = make_pcontext err translator env0 sigma in
  let (sigma, cr) = optranslate env sigma c in
  let decl = get_pexception env in
  let cr = mkLambda_or_LetIn decl cr in
  let (sigma, _) = Typing.type_of env.penv_src sigma cr in
  (sigma, cr)

let translate_type err translator env sigma c =
  let (sigma, env) = make_context err translator env sigma in
  let (sigma, c_) = otranslate_type env sigma c in
  let decl = get_exception env in
  let c_ = mkProd_or_LetIn decl c_ in
  let (sigma, _) = Typing.type_of env.env_src sigma c_ in
  (sigma, c_)

(* From ⊢ A : Type produce Ap s.t. (x : forall E : Type, ⟦A⟧) ⊢ Ap : Type. *)
let ptranslate_type err translator env0 sigma c =
  let (sigma, env) = make_pcontext err translator env0 sigma in
  let (sigma, c_) = otranslate_type (project env) sigma c in
  let decl = get_exception (project env) in
  let c_ = mkProd_or_LetIn decl c_ in
  let (sigma, cr) = optranslate_type env sigma c in
  let arg = match err with
  | None -> mkApp (mkRel 2, [| mkRel 1 |])
  | Some _ -> mkRel 2 (** If instantiated to one error type, no need to specialize it *)
  in
  let cr = Vars.subst1 arg (Vars.liftn 1 3 cr) in
  let decl = get_pexception env in
  let cr = mkProd_or_LetIn decl cr in
  let nenv = EConstr.push_rel (LocalAssum (Anonymous, c_)) env.penv_src in
  let (sigma, _) = Typing.type_of nenv sigma cr in
  (sigma, cr)

let to_local_entry = function
| LocalAssum (Name id, t) -> (id, Entries.LocalAssumEntry t)
| LocalDef (Name id, b, t) -> (id, Entries.LocalDefEntry b)
| _ -> assert false

let dummy_kn id =
  KerName.make (MPfile DirPath.empty) DirPath.empty (Label.of_id id)

let trans_name translation_function = function
  | Anonymous as anon -> anon
  | Name id -> Name (translation_function id)

let name_projection_translate sigma translation_function record_builder = 
  let rec aux sigma record_builder = 
    match EConstr.kind sigma record_builder with
    | Prod (na, ty, bd) -> 
       let trans_body = aux sigma bd in 
       mkProd (trans_name translation_function na, ty, trans_body)
    | _ -> record_builder
  in
  aux sigma record_builder

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
  let ind_name = dummy_kn (translate_internal_name mind0.mind_packets.(0).mind_typename) in
  let mind = MutInd.make1 ind_name in
  let env_tgt = Environ.add_mind mind mbi env.env_tgt in
  let ext = match env.error with
  | None -> GlobGen mind
  | Some exn -> GlobImp (Refmap.singleton exn mind)
  in
  let translator = { env.translator with inds = Mindmap.add mind ext env.translator.inds } in
  mind, { env with translator; env_tgt }

let abstract_mind sigma mind n k c =
  let rec aux k c = match EConstr.kind sigma c with
  | Rel m ->
    if m <= k then c
    else mkRel (k + m)
  | Ind ((ind, m), _) when MutInd.equal mind ind ->
    mkRel (k + n - m)
  | _ ->
    map_with_binders sigma succ aux k c
  in
  aux k c

let translate_constructors env sigma mind0 mind ind0 ind =
  let mutind, env = extend_inductive env mind0 mind in
  let nblock = Array.length mind0.mind_packets in
  let mk_ind n = mkInd (mutind, nblock - (n + 1)) in
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
  List.fold_map map sigma ind.mind_entry_lc

let translate_inductive_body env sigma mind0 mind n ind0 ind =
  let typename = translate_internal_name ind.mind_entry_typename in
  let constructors = List.map translate_name ind.mind_entry_consnames in
  let nindices = List.length ind0.mind_arity_ctxt - List.length mind0.mind_params_ctxt in 
  let arity_ctx, _ = List.chop nindices ind0.mind_arity_ctxt in
  let (sigma, arity_env, arity_ctx') = otranslate_context env sigma (List.map EConstr.of_rel_decl arity_ctx) in
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
  (** FIXME, probably wrong indices for mutual inductive blocks *)
  let (_, fail_args) = List.fold_left fail_arg (2, []) (Environ.rel_context arity_env.env_tgt) in
  let n = 1 + (mind0.mind_ntypes - n) + Environ.nb_rel arity_env.env_tgt in
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

let translate_primitive_record env sigma mind_d mind_e =
  let _, env = extend_inductive env mind_d mind_e in
  let ind_e = List.hd mind_e.mind_entry_inds in 
  let ind_d = mind_d.mind_packets.(0) in 
  let ind_name = translate_internal_name ind_e.mind_entry_typename in
  let (sigma, sort) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.env_tgt sigma InType in
  let ar = mkSort sort in
  let cons_name = translate_name (List.hd ind_e.mind_entry_consnames) in
  let (sigma, constr_type) = translate_constructors env sigma mind_d mind_e ind_d ind_e in
  let constr_type = List.hd constr_type in
  let constr_type_name = name_projection_translate sigma translate_name constr_type in
  let ind = { ind_e with 
              mind_entry_typename = ind_name;
              mind_entry_arity = EConstr.to_constr sigma ar;
              mind_entry_consnames = [cons_name];
              mind_entry_lc = [EConstr.to_constr sigma constr_type_name] 
            }
  in
  (sigma, ind)

let translate_inductive err translator env _ mind0 (mind : Entries.mutual_inductive_entry) =
  let sigma = Evd.from_env env in
  let (sigma, env) = make_context err translator env sigma in
  let (sigma, env, _) = otranslate_context env sigma (List.map EConstr.of_rel_decl mind0.mind_params_ctxt) in
  let (sigma, inds) = 
    if Inductive.is_primitive_record (mind0,mind0.mind_packets.(0)) then 
       let (sigma, pind) = translate_primitive_record env sigma mind0 mind in
       (sigma, [pind])
    else 
      let inds = List.combine (Array.to_list mind0.mind_packets) mind.mind_entry_inds in
      let inds = List.mapi (fun i (ind, ind0) -> (i, ind, ind0)) inds in
      let map sigma (n, ind0, ind) = translate_inductive_body env sigma mind0 mind n ind0 ind in
      let sigma, inds = List.fold_map map sigma inds in
      (sigma, inds)
  in
  let sigma, inds, params = EUtil.retype_inductive env.env_tgt sigma (EConstr.rel_context env.env_tgt) inds in
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

(** Locally extend a translator to fake an inductive definition *)
let pextend_inductive env (mutind0, _) mind0 mind =
  let open Univ in
  let univs = match mind0.mind_universes with
  | Monomorphic_ind _ -> Monomorphic_ind UContext.empty
  | Polymorphic_ind _ -> Polymorphic_ind AUContext.empty
  | Cumulative_ind _ -> Polymorphic_ind AUContext.empty (** FIXME *)
  in
  (** Dummy inductive. It is only used for its universe context, that we set to
      be empty. *)
  let mbi = { mind0 with mind_universes = univs } in
  let ind_name = dummy_kn (ptranslate_internal_name mind0.mind_packets.(0).mind_typename) in
  let mind = MutInd.make1 ind_name in
  let penv_tgt = Environ.add_mind mind mbi env.penv_tgt in
  let penv_ptgt = Environ.add_mind mind mbi env.penv_ptgt in
  let ext = Mindmap.find mutind0 env.ptranslator.inds in
  let pext = match env.perror with
  | None -> GlobGen mind
  | Some exn -> GlobImp (Refmap.singleton exn mind)
  in
  let inds = Mindmap.add mind ext env.ptranslator.inds in
  let pinds = Mindmap.add mind pext env.ptranslator.pinds in
  let ptranslator = { env.ptranslator with pinds; inds; } in
  mind, { env with ptranslator; penv_tgt; penv_ptgt }

let ptranslate_constructors env sigma mutind0 mind0 mind ind0 ind =
  let mutind, env = pextend_inductive env mutind0 mind0 mind in
  let tr_pinds = env.ptranslator.pinds in
  let _ = Mindmap.find mutind tr_pinds in
  let nblock = Array.length mind0.mind_packets in
  let mk_ind n = mkInd (mutind, nblock - (n + 1)) in
  let subst0 = List.init nblock mk_ind in
  let map (n, sigma) t =
    (** A bit of term mangling: indices in the context referring to the
        inductive types we're building do not have the right type. *)
    let t = EConstr.of_constr t in
    let t = Vars.substnl subst0 (Environ.nb_rel env.penv_src) t in
    let (sigma, tr) = optranslate_type env sigma t in
    (** Instantiate the parametricity hole with the corresponding effectful constructor *)
    let gen, ind_ = get_ind (project env) mutind0 in
    let (sigma, (c_, u)) = Evd.fresh_constructor_instance env.penv_tgt sigma (ind_, n) in
    let c_ = mkConstructU (c_, EInstance.make u) in
    let make_arg (n, accu) = function
    | LocalAssum _ -> (succ n, mkRel (2 * n) :: accu)
    | LocalDef _ -> (succ n, accu)
    in
    let (_, args) = List.fold_left make_arg (1, []) mind0.mind_params_ctxt in
    let args = if gen then mkRel (Environ.nb_rel env.penv_ptgt) :: args else args in
    let c_ = applist (c_, args) in
    let tr = Vars.subst1 c_ tr in
    (** Unmangle *)
    let tr = abstract_mind sigma mutind nblock (Environ.nb_rel env.penv_ptgt) tr in
    ((succ n, sigma), tr)
  in
  let ((_, sigma), ans) = List.fold_map map (1, sigma) ind.mind_entry_lc in
  (sigma, ans)

let ptranslate_inductive_body err env sigma mutind mind0 mind n ind0 ind =
  let typename = ptranslate_internal_name ind.mind_entry_typename in
  let constructors = List.map ptranslate_name ind.mind_entry_consnames in
  let nindices = List.length ind0.mind_arity_ctxt - List.length mind0.mind_params_ctxt in
  let arity_ctx, _ = List.chop nindices ind0.mind_arity_ctxt in
  let (sigma, arity_env, arity_ctx') = optranslate_context env sigma (List.map EConstr.of_rel_decl arity_ctx) in
  let gen, ind_ = get_ind (project env) (mutind, n) in
  let (sigma, (ind_, u)) = Evd.fresh_inductive_instance env.penv_ptgt sigma ind_ in
  let ind_ = mkIndU (ind_, EInstance.make u) in
  let make_arg (n, accu) = function
  | LocalAssum _ -> (succ n, mkRel (2 * n) :: accu)
  | LocalDef _ -> (succ n, accu)
  in
  let (_, args) = List.fold_left make_arg (1, []) ind0.mind_arity_ctxt in
  let args = if gen then mkRel (Environ.nb_rel arity_env.penv_ptgt) :: args else args in
  let ind_ = applist (ind_, args) in
  let self = LocalAssum (Anonymous, ind_) in
  let (sigma, sort) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.penv_ptgt sigma InType in
  let arity = it_mkProd_or_LetIn (mkSort sort) (self :: arity_ctx') in
  let (sigma, _) = Typing.type_of env.penv_ptgt sigma arity in
  let (sigma, lc) = ptranslate_constructors env sigma (mutind, n) mind0 mind ind0 ind in
  let lc = List.map (fun c -> EConstr.to_constr sigma c) lc in
  let ind = { ind with
    mind_entry_typename = typename;
    mind_entry_arity = EConstr.to_constr sigma arity;
    mind_entry_consnames = constructors;
    mind_entry_lc = lc;
  } in
  (sigma, ind)

let rec split_record_constr sigma term = match EConstr.kind sigma term with
  | Prod (na, ty, bd) ->
      ty :: split_record_constr sigma bd
  | _ -> [term]

let mk_named_proj names field term =
  let current = Names.Projection.make names.(field) false in
  mkProj (current, term)  

let ptranslate_primitive_projs env sigma mutind mind_d mind_e ind_e =
  let ext_mind, env = pextend_inductive env (mutind, 0) mind_d mind_e in
  let record_constructor = EConstr.of_constr (List.hd ind_e.mind_entry_lc) in
  let _,projections_name,_ = Option.get (Option.get mind_d.mind_record) in
  let fold name = 
    let (_,cst) = get_cst (project env) name in
    Globnames.destConstRef cst 
  in
  let projections_name = Array.map fold projections_name in
  let buckets = split_record_constr sigma record_constructor in
  let projections_type = List.firstn (Array.length projections_name) buckets in
  let map (n, sigma, env) t =
    let prev_fields = n - 1 in
    let (sigma, tr) = optranslate_type env sigma t in 
    let tr = Vars.liftn (2*prev_fields + 1) (2*prev_fields + 2) tr in
    let tr = Vars.subst1 (mk_named_proj projections_name (n - 1) (mkRel (4*prev_fields + 1))) tr in
    let projection_subst current_field n = 
      let inverse_field = (n + 1) / 2 in
      if n mod 2 == 0 then
        let record_name = inverse_field + 1 in 
        mk_named_proj projections_name (current_field - record_name) (mkRel (current_field))
      else
        mkRel inverse_field
    in
    let prev_projections = List.init 
                             (2*prev_fields) 
                             (fun i -> projection_subst n (i + 1)) 
    in
    let tr = Vars.substl prev_projections tr in
    let tr = Vars.liftn (- prev_fields) (2*prev_fields + 1) tr in 
    let nenv = push_passum (Names.Name.mk_name (Names.id_of_string "dummy"))  (t, t, t) env in    
    ((succ n, sigma, nenv), tr)
  in
  let ((_, sigma, env), new_projections) = List.fold_map map (1, sigma, env) projections_type in
  (sigma, new_projections)  

let ptranslate_primitive_record env sigma mutind mind_d mind_e =
  let ind_e = List.hd mind_e.mind_entry_inds in 
  let record_name = ind_e.mind_entry_typename in
  let record_build = List.hd ind_e.mind_entry_consnames in
  let (_,record_projs,_) = Option.get (Option.get mind_d.mind_record) in
  let record_num_projs = Array.length record_projs in
  let gen, ind_ = get_ind (project env) (mutind, 0) in
  let (sigma, (ind_, u)) = Evd.fresh_inductive_instance env.penv_ptgt sigma ind_ in
  let ind_ = mkIndU (ind_, EInstance.make u) in
  let make_arg (n, accu) = function
    | LocalAssum _ -> (succ n, mkRel (2 * n) :: accu)
    | LocalDef _ -> (succ n, accu)
  in
  let (_, args) = List.fold_left make_arg (1, []) mind_d.mind_params_ctxt in
  let args = if gen then mkRel (Environ.nb_rel env.penv_ptgt) :: args else args in
  let ind_ = applist (ind_, args) in
  let (sigma, sort) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.penv_ptgt sigma InType in
  let arity = mkSort sort in
  let (sigma, _) = Typing.type_of env.penv_ptgt sigma arity in
  let (sigma, projections) = ptranslate_primitive_projs env sigma mutind mind_d mind_e ind_e in
  let make_arg (n, accu) decl = 
    let rel = 2 * n + record_num_projs + 1 in
    match decl with 
    | LocalAssum _ -> (succ n, mkRel (rel) :: mkRel (rel - 1) :: accu)
    | LocalDef _ -> (succ n, accu)
  in
  let (_, args) = List.fold_left 
                    make_arg 
                    (1, [mkRel (record_num_projs + 1)]) 
                    mind_d.mind_params_ctxt 
  in
  let builder_ctxt = (Environ.nb_rel env.penv_ptgt) + record_num_projs in
  let args = if gen then mkRel (builder_ctxt + 1) :: args else args in
  let pind = builder_ctxt + 2 in
  let cr = applist (mkRel pind, args) in
  let constr_builder (proj_name, proj_type) partial_record =
    let open Names in 
    let name = ptranslate_name (Label.to_id (Constant.label proj_name)) in
    mkProd (Name.mk_name name, proj_type, partial_record) 
  in
  let zip_projections = List.combine (Array.to_list record_projs) projections in 
  let record_constructor = List.fold_right constr_builder zip_projections cr in
  let decl_to_name decl = 
    let open Context.Rel.Declaration in
    match (get_name decl) with Anonymous -> Names.Id.of_string "" | Name t -> t
  in
  let params_name = List.map decl_to_name (Environ.rel_context env.penv_ptgt) in
  let fresh_record = Namegen.next_ident_away (Names.Id.of_string "r") params_name in
  let assum = LocalAssum (Names.Name.mk_name fresh_record, EConstr.to_constr sigma ind_) in
  let env = {env with penv_ptgt = Environ.push_rel assum env.penv_ptgt } in
  let ind = { ind_e with 
              mind_entry_typename = ptranslate_name record_name;
              mind_entry_arity = EConstr.to_constr sigma arity;
              mind_entry_consnames = [ptranslate_name record_build];
              mind_entry_lc = [EConstr.to_constr sigma record_constructor] 
            }
  in
  (sigma, env, ind)

let ptranslate_inductive err translator env mutind mind0 (mind : Entries.mutual_inductive_entry) =
  let sigma = Evd.from_env env in
  let (sigma, env) = make_pcontext err translator env sigma in
  let (sigma, env, _) = optranslate_context env sigma (List.map EConstr.of_rel_decl mind0.mind_params_ctxt) in
  let (sigma, env, inds) = 
    if Inductive.is_primitive_record (mind0,mind0.mind_packets.(0)) then 
      let (sigma, env, pind) = ptranslate_primitive_record env sigma mutind mind0 mind in
      (sigma, env, [pind])
    else 
      let inds = List.combine (Array.to_list mind0.mind_packets) mind.mind_entry_inds in
      let inds = List.mapi (fun i (ind, ind0) -> (i, ind, ind0)) inds in
      let map sigma (n, ind0, ind) = 
        let (sigma, ind) = ptranslate_inductive_body err env sigma mutind mind0 mind n ind0 ind in
        (sigma, ind)
      in
      let sigma, inds = List.fold_map map sigma inds in
      (sigma, env, inds)
  in
  let sigma, inds, params = EUtil.retype_inductive env.penv_ptgt sigma (EConstr.rel_context env.penv_ptgt) inds in
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


(** Weak inductive *)

type wcontext_type = Simple | Double

type wcontext_decl =  wcontext_type list

let wcontext_type_associated_number = function
  | Simple -> 1
  | Double -> 2

let declared_var_in_wcontext wc = 
  let f = (fun accum wc -> wcontext_type_associated_number wc + accum) in
  List.fold_left f 0 wc

let wdebruijn_lookup decl n = 
  let listn = List.firstn n decl in
  let brujin = declared_var_in_wcontext listn in
  brujin + 1 - wcontext_type_associated_number (List.last listn) 

type wcontext = {
  werror : global_reference option;
  (** Whether the translation is relativized to a specific error type *)
  wtranslator : translator;
  wenv_src : Environ.env;
  wenv_tgt : Environ.env;
  wenv_wtgt : Environ.env;
  wcontext : wcontext_decl;
}

let wtop_decls env weakly_check =
  List.firstn (if weakly_check then 1 else 2) (EConstr.rel_context env.wenv_wtgt)

let make_wcontext werror wtranslator env sigma =
  let (sigma, decl) =  make_error werror env sigma in
  let env_tgt = Environ.push_rel decl env in
  let wenv = {
    werror;
    wtranslator;
    wenv_src = env;
    wenv_tgt = env_tgt;
    wenv_wtgt = env_tgt;
    wcontext = []
  } in
  (sigma, wenv)

let wproject env = {
  error = env.werror;
  translator = env.wtranslator;
  env_src = env.wenv_src;
  env_tgt = env.wenv_tgt;
}

let get_wexception env =
  let decls = EConstr.rel_context env.wenv_wtgt in
  List.last decls

let get_wind env (ind, n) = 
  try
    let gen, ind = get_instance env.werror (Mindmap.find ind env.wtranslator.winds) in
    gen, (ind, n)
  with Not_found -> raise (MissingGlobal (env.werror, IndRef (ind, n)))

let get_wcst env cst =
  try get_instance env.werror (Cmap.find cst env.wtranslator.wrefs)
  with Not_found -> raise (MissingGlobal (env.werror, ConstRef cst))

let apply_wglobal env sigma gr =
  let gen, gr = match gr with
  | ConstructRef (ind, n) ->
    let gen, ind = get_wind env ind in
    gen, ConstructRef (ind, n)
  | IndRef ind ->
    let gen, ind = get_wind env ind in
    gen, IndRef ind
  | ConstRef cst -> get_wcst env cst
  | VarRef _ -> CErrors.user_err (str "Variables not handled")
  in
  let (sigma, c) = Evd.fresh_global env.wenv_wtgt sigma gr in
  let c = EConstr.of_constr c in
  if gen then
    let e = mkRel (Environ.nb_rel env.wenv_wtgt) in
    (sigma, mkApp (c, [|e|]))
  else
    (sigma, c)

let wfresh_global env sigma gr =
  try
    let (sigma, c) = Evd.fresh_global env.wenv_wtgt sigma gr in
    (sigma, EConstr.of_constr c)
  with Not_found -> raise (MissingPrimitive gr)

let wtranslate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵂ")

let wtranslate_internal_name = wtranslate_name

let wname = function
  | Anonymous -> Anonymous
  | Name id -> Name (wtranslate_name id)
      
(** Used to lift exceptional terms to the new weakly layer *)
let wlift env t =
  let n = Environ.nb_rel env.wenv_tgt - 1 in
  let lifted_e = declared_var_in_wcontext env.wcontext in
  let subst_f = (fun i -> let j = i + 1 in
                          let wc = (List.firstn j env.wcontext) in
                          let n = declared_var_in_wcontext wc in
                          mkRel n) 
  in
  let subst = List.init n subst_f in
  Vars.substl subst (Vars.liftn lifted_e (n + 1) t)

let push_wassum na (t, te) tw env =
  let (wenv, wtype) = match tw with
    | None -> (EConstr.push_rel (LocalAssum (na, wlift env te)) env.wenv_wtgt, Simple)
    | Some tw ->
      let declw = LocalAssum (wname na, tw) in
      let decl = LocalAssum  (na, wlift env te) in
      (EConstr.push_rel declw (EConstr.push_rel decl env.wenv_wtgt), Double)
  in 
  { env with
    wenv_src = EConstr.push_rel (LocalAssum (na, t)) env.wenv_src;
    wenv_tgt = EConstr.push_rel (LocalAssum (na, te)) env.wenv_tgt;
    wenv_wtgt = wenv;
    wcontext = wtype :: env.wcontext;
  }

let push_wdef na (c, ce) (t, te) aw env = 
  let (wenv, wtype) = match aw with
    | Some cw, Some tw -> 
       let defw = LocalDef (wname na, cw, tw) in
       let def = LocalDef (na, wlift env ce, wlift env te) in
       EConstr.push_rel defw (EConstr.push_rel def env.wenv_wtgt), Double
    | _ -> EConstr.push_rel (LocalDef (na, wlift env ce, wlift env te)) env.wenv_wtgt, Simple
  in
  { env with
    wenv_src = EConstr.push_rel (LocalDef (na, c, t)) env.wenv_src;
    wenv_tgt = EConstr.push_rel (LocalDef (na, ce, te)) env.wenv_tgt;
    wenv_wtgt = wenv;
    wcontext = wtype :: env.wcontext;
  }


let arity_type_prop_check env sigma ty =
  let sort = Typing.e_sort_of env (ref sigma) ty in
  let ty = (EConstr.to_constr sigma ty) in
  is_prop_sort sort || (try (is_prop_sort (snd (Reduction.dest_arity env ty)))
                       with Reduction.NotArity -> false)

let one_ind_in_prop ind = 
  match ind.mind_arity with
  | RegularArity ar -> is_prop_sort ar.mind_sort
  | TemplateArity _ -> false

let wargument_of_prod env sigma prod =
  let weak_dom = arity_type_prop_check env sigma prod in
  let rec arg_calc env' sigma' t accum = match EConstr.kind sigma' t with
    | Prod (n, t, u) -> 
       let weak_cod = arity_type_prop_check env' sigma' t in 
       let env' = EConstr.push_rel (LocalAssum (n, t)) env' in
       if not weak_cod && weak_dom 
       then arg_calc env' sigma' u (Simple :: accum)
       else arg_calc env' sigma' u (Double :: accum)
    | _ -> accum
  in
  List.rev (arg_calc env sigma prod [])


let wtranslate_case_info env sigma ci mip =
  let gen, ci_ind = get_wind env ci.ci_ind in
  Inductiveops.make_case_info env.wenv_wtgt ci_ind ci.ci_pp_info.style
(*
  let mutual_wind = Environ.lookup_mind (fst ci_ind) env in
  let ci_npar = if gen then 1 + 2 * ci.ci_npar else 2 * ci.ci_npar in
  let map n = 2 * n in
  let ci_cstr_ndecls = Array.map map ci.ci_cstr_ndecls in
  let ci_cstr_nargs = Array.map map ci.ci_cstr_nargs in
  let rec dup = function
  | [] -> []
  | x :: l -> x :: x :: (dup l)
  in
  let ci_pp_info = {
    ind_tags = (not gen) :: dup ci.ci_pp_info.ind_tags;
    cstr_tags = Array.map (fun l -> (not gen) :: dup l) ci.ci_pp_info.cstr_tags;
    style = ci.ci_pp_info.style;
  } in
  { ci_ind; ci_npar; ci_cstr_ndecls; ci_cstr_nargs; ci_pp_info; }
 *)

let rec owtranslate env sigma c = match EConstr.kind sigma c with
  | Rel n ->
     let m = wdebruijn_lookup env.wcontext n in
     (sigma, mkRel m) 
  | Sort _ | Prod _ ->
     let (sigma, c_) = otranslate_type (wproject env) sigma c in
     let c_ = wlift env c_ in
     let (sigma, w) = owtranslate_type env sigma c in
     let w = mkLambda (Anonymous, c_, w) in
     (sigma, w)
  | Lambda (na, t, u) ->
     let (sigma, t_) = otranslate_type (wproject env) sigma t in
     let extended_env = EConstr.push_rel (LocalAssum (na, t)) env.wenv_src in
     let cod_prop = arity_type_prop_check env.wenv_src sigma t in
     let (sigma, u_typ) = Typing.type_of extended_env sigma u in
     let dom_prop = arity_type_prop_check extended_env sigma u_typ in
     let weakly_check = not cod_prop && dom_prop in
     let (sigma, tw) =
       if weakly_check then (sigma, None)
       else let (s, o) = owtranslate_type env sigma t in 
            (s, Some o)
     in 
     let nenv = push_wassum na (t, t_) tw env in
     let (sigma, uw) = owtranslate nenv sigma u in
     let ctx = wtop_decls nenv weakly_check in
     let w = it_mkLambda_or_LetIn uw ctx in
     (sigma, w)
  | LetIn (na, c, t, u) ->
     let (sigma, c_) = otranslate (wproject env) sigma c in
     let (sigma, t_) = otranslate_type (wproject env) sigma t in
     let extended_env = EConstr.push_rel (LocalDef (na, c, t)) env.wenv_src in
     let cod_prop = arity_type_prop_check env.wenv_src sigma t in
     let (sigma, u_typ) = Typing.type_of extended_env sigma u in
     let dom_prop = arity_type_prop_check extended_env sigma u_typ in
     let weakly_check = not cod_prop && dom_prop in
     let (sigma, ctw) =
       if weakly_check then (sigma, (None, None))
       else let (s, cw) = owtranslate_type env sigma c in 
            let (s, tw) = owtranslate_type env s t in
            (s, (Some cw, Some tw))
     in 
     let nenv = push_wdef na (c, c_) (t, t_) ctw env in 
     let ctx = wtop_decls nenv weakly_check in
     let (sigma, ur) = owtranslate nenv sigma u in
     let r = it_mkLambda_or_LetIn ur ctx in
     (sigma, r)
  | App (t, args) ->
     let args = Array.to_list args in
     let (sigma, tw) = owtranslate env sigma t in
     let is_primitive = 
       if isConstruct sigma t then
         let ((ind, c), u) = destConstruct sigma t in
         let specif = Inductive.lookup_mind_specif env.wenv_wtgt ind in 
         Inductive.is_primitive_record specif 
       else
         false
     in
     let (sigma, t_typ) = Typing.type_of env.wenv_src sigma t in
     let number_of_args = List.length args in
     let wargs_typ = wargument_of_prod env.wenv_src sigma t_typ in
     let wargs_typn = List.firstn number_of_args wargs_typ in 
     let fold (t, typ) (sigma, accum) = 
       let (sigma, t_) = otranslate (wproject env) sigma t in
       let t_ = wlift env t_ in
       match typ with
       | Simple -> (sigma, t_ :: accum)
       | Double -> 
          let (sigma, tw) = owtranslate env sigma t in
          (sigma, t_ :: tw :: accum)
     in
     let zip = List.combine args wargs_typn in
     let (sigma, argsw) = List.fold_right fold zip (sigma, []) in
     let (sigma, argsw) = 
       if is_primitive then
         let ((ind,c), u) = destConstruct sigma t in
         let _, indw = get_wind env ind in 
         let specifw = Inductive.lookup_mind_specif env.wenv_wtgt indw in 
         let n_params_wo_rec_nor_err = (Inductive.inductive_params specifw) - 2 in 
         let (params,fields) = List.chop n_params_wo_rec_nor_err argsw in
         let fields = List.filteri (fun i _ -> i mod 2 == 1) fields in
         let (sigma, t_) = otranslate (wproject env) sigma (applist (t, args)) in
         (sigma, params @ (t_ :: fields))
       else
         (sigma, argsw)
     in
     let w = applist (tw, argsw) in
     (sigma, w)
  | Var id ->
     apply_wglobal env sigma (VarRef id)
  | Const (p, _) ->
     let (sigma, c) = apply_wglobal env sigma (ConstRef p) in
     (sigma, c)
  | Ind (ind, _) ->
     let (sigma, c) = apply_wglobal env sigma (IndRef ind) in
     (sigma, c)
  | Construct (c, _) ->
     let (sigma, c) = apply_wglobal env sigma (ConstructRef c) in
     (sigma, c)
  | Case (ci, r, d, p) ->
     let (_, mip) = Inductive.lookup_mind_specif env.wenv_src ci.ci_ind in
     let ciw = wtranslate_case_info env sigma ci mip in     
     let (sigma, dw) = owtranslate env sigma d in
     let map sigma p = owtranslate env sigma p in
     let (sigma, pw) = Array.fold_map map sigma p in
     let (ctx, r) = EConstr.decompose_lam_assum sigma r in
     let weakly_dom = one_ind_in_prop mip in
     let (sigma, nenv, ctxw) = owtranslate_context env sigma weakly_dom ctx in
     let (sigma, wr) = owtranslate_type nenv sigma r in
     let c = Vars.lift (List.length ctx) c in
     let (ci, r, _, p) = destCase sigma c in
     let c = mkCase (ci, r, mkRel 1, p) in
     let (sigma, ce) = otranslate (wproject nenv) sigma c in
     let ce = wlift nenv ce in
     let rw = it_mkLambda_or_LetIn (Vars.subst1 ce wr) ctxw in
     let w = mkCase (ciw, rw, dw, pw) in
     (sigma, w)
  | _ ->
     (sigma, c)
and owtranslate_type env sigma c = match EConstr.kind sigma c with
  | Sort s ->
     let (sigma, el) = wfresh_global env sigma el_e in
     let e = mkRel (Environ.nb_rel env.wenv_wtgt + 1) in
     let (sigma, s) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.wenv_wtgt sigma InType in
     let r = mkArrow (mkApp (el, [|e; mkRel 1|])) (mkSort s) in
     (sigma, r)
  | Prod (na,t,u) ->
     let (sigma, t_) = otranslate_type (wproject env) sigma t in
     let ar_prop_cod = arity_type_prop_check env.wenv_src sigma t in
     let extended_env = EConstr.push_rel (LocalAssum (na, t)) env.wenv_src in
     let ar_prop_dom = arity_type_prop_check extended_env sigma u in
     let weakly_check = not ar_prop_cod && ar_prop_dom in
     let (sigma, tw)= 
       if weakly_check then (sigma, None)
       else let (s, o) = owtranslate_type env sigma t in 
            (s, Some o)
     in 
     let nenv = push_wassum na (t, t_) tw env in
     let (sigma, uw) = owtranslate_type nenv sigma u in
     let n = if weakly_check then 2 else 3 in
     let uw = Vars.liftn 1 (if weakly_check then 3 else 4) uw in
     let uw = Vars.subst1 (mkApp (mkRel n, [| mkRel (n - 1) |])) uw in
     let ctx = wtop_decls nenv weakly_check in
     let ctx = lift_rel_context 1 ctx in
     let r = it_mkProd_or_LetIn uw ctx in
     (sigma, r)
  | _ ->
     let (sigma, cr) = owtranslate env sigma c in
     (sigma, mkApp (Vars.lift 1 cr, [| mkRel 1 |]))

and owtranslate_context env sigma weakly_end = function 
| [] -> sigma, env, []
| LocalAssum (na, t) :: params ->
   let (sigma, env, ctx) = owtranslate_context env sigma weakly_end params in
   let (sigma, t_) = otranslate_type (wproject env) sigma t in
   let weakly_current = arity_type_prop_check env.wenv_src sigma t in
   let weakly_check = not weakly_current && weakly_end in
   let (sigma, tw) = if weakly_check 
                     then (sigma, None)
                     else let (sigma, tw) = owtranslate_type env sigma t in 
                          (sigma, Some tw) 
   in
   let nenv = push_wassum na (t, t_) tw env in
   let decl = wtop_decls nenv weakly_check in
   (sigma, nenv, decl @ ctx)
| LocalDef (na, c, t) :: params ->
   let (sigma, env, ctx) = owtranslate_context env sigma weakly_end params in
   let (sigma, c_) = otranslate (wproject env) sigma c in
   let weakly_current = arity_type_prop_check env.wenv_src sigma t in
   let weakly_check = not weakly_current && weakly_end in
   let (sigma, cw) = if weakly_check
                     then (sigma, None)
                     else let (sigma, cw) = owtranslate_type env sigma c in 
                          (sigma, Some cw)
   in
   let (sigma, t_) = otranslate_type (wproject env) sigma t in
   let (sigma, tw) = if weakly_check
                     then (sigma, None)
                     else let (sigma, tw) = owtranslate_type env sigma t in 
                          (sigma, Some tw) 
   in
   let nenv = push_wdef na (c, c_) (t, t_) (cw, tw) env in
   let decl = wtop_decls nenv weakly_check in
   (sigma, nenv, decl @ ctx)
     
let wtranslate err translator env sigma c = 
  let (sigma, env) = make_wcontext err translator env sigma in
  let (sigma, cw) = owtranslate env sigma c in
  let decl = get_wexception env in
  let cw = mkLambda_or_LetIn decl cw in
  (sigma, cw)

let wtranslate_type err translator env sigma c =
  let (sigma, env) = make_wcontext err translator env sigma in
  let (sigma, c_) = otranslate_type (wproject env) sigma c in
  let decl = get_exception (wproject env) in
  let c_ = mkProd_or_LetIn decl c_ in
  let (sigma, cw) = owtranslate_type env sigma c in
  let arg = match err with
    | None -> mkApp (mkRel 2, [| mkRel 1|])
    | Some _ -> mkRel 2
  in
  let cw = Vars.subst1 arg cw in
  let decl = get_wexception env in
  let cw = mkProd_or_LetIn decl cw in
  let nenv = EConstr.push_rel (LocalAssum (Anonymous, c_)) env.wenv_src in
  let (sigma, _) = Typing.type_of nenv sigma cw in
  (sigma, cw)

let wargument_of_context env sigma weak_dom ctx =
  let get_type = Context.Rel.Declaration.get_type in
  let (_, warg) = List.fold_right 
                    (fun d (env, accum) -> 
                      let weak_cod = arity_type_prop_check env sigma (get_type d) in
                      let env = EConstr.push_rel d env in
                      if not weak_cod && weak_dom
                      then (env, Simple :: accum) 
                      else (env, Double :: accum))
                    ctx
                    (env, [])     
  in warg

let wextend_inductive env (mutind0, _) mind0 mind =
  let open Univ in
  let univs = match mind0.mind_universes with
  | Monomorphic_ind _ -> Monomorphic_ind UContext.empty
  | Polymorphic_ind _ -> Polymorphic_ind AUContext.empty
  | Cumulative_ind _ -> Polymorphic_ind AUContext.empty (** FIXME *)
  in
  (** Dummy inductive. It is only used for its universe context, that we set to
      be empty. *)
  let mbi = { mind0 with mind_universes = univs } in
  let ind_name = dummy_kn (wtranslate_internal_name mind0.mind_packets.(0).mind_typename) in
  let mind = MutInd.make1 ind_name in
  let wenv_src = Environ.add_mind mind mbi env.wenv_src in
  let wenv_tgt = Environ.add_mind mind mbi env.wenv_tgt in
  let wenv_wtgt = Environ.add_mind mind mbi env.wenv_wtgt in
  let ext = Mindmap.find mutind0 env.wtranslator.inds in
  let wext = match env.werror with
  | None -> GlobGen mind
  | Some exn -> GlobImp (Refmap.singleton exn mind)
  in
  let inds = Mindmap.add mind ext env.wtranslator.inds in
  let winds = Mindmap.add mind wext env.wtranslator.winds in
  let wtranslator = { env.wtranslator with winds; inds; } in
  mind, { env with wtranslator; wenv_src; wenv_tgt; wenv_wtgt }


let wtranslate_constructors env sigma weak_dom mutind0 mind_d mind_e ind_d ind_e =
  let mutind, env = wextend_inductive env mutind0 mind_d mind_e in
  let nblock = Array.length mind_d.mind_packets in
  let mk_ind n = mkInd (mutind, nblock - (n + 1)) in
  let subst0 = List.init nblock mk_ind in
  let map (n, sigma) t =
    (** A bit of term mangling: indices in the context referring to the
        inductive types we're building do not have the right type. *)
    let t = EConstr.of_constr t in
    let t = Vars.substnl subst0 (Environ.nb_rel env.wenv_src) t in
    let (sigma, tw) = owtranslate_type env sigma t in
    (** Instantiate the parametricity hole with the corresponding effectful constructor *)
    let gen, ind_ = get_ind (wproject env) mutind0 in
    let (sigma, (c_, u)) = Evd.fresh_constructor_instance env.wenv_tgt sigma (ind_, n) in
    let c_ = mkConstructU (c_, EInstance.make u) in
    let params_ctxt = List.map EConstr.of_rel_decl mind_d.mind_params_ctxt in
    let warg_context = wargument_of_context env.wenv_src sigma weak_dom params_ctxt in
    let make_arg (n, accu) (d, wt) = 
      let i = wcontext_type_associated_number wt in
      match d with
      | LocalAssum _ -> (n + i, mkRel (n + i) :: accu)
      | LocalDef _ -> (n + i, accu)
    in
    let (_, args) = List.fold_left make_arg (0, []) (List.combine params_ctxt warg_context) in
    let args = if gen then mkRel (Environ.nb_rel env.wenv_wtgt) :: args else args in
    let c_ = applist (c_, args) in
    let tw = Vars.subst1 c_ tw in
    (** Unmangle *)
    let tw = abstract_mind sigma mutind nblock (Environ.nb_rel env.wenv_wtgt) tw in
    ((succ n, sigma), tw)
  in
  let ((_, sigma), ans) = List.fold_map map (1, sigma) ind_e.mind_entry_lc in
  (sigma, ans)


let wtranslate_inductive_body err env sigma weakly_dom mutind mind_d mind_e n ind_d ind_e = 
  let typename = wtranslate_internal_name ind_e.mind_entry_typename in
  let constructors = List.map wtranslate_name ind_e.mind_entry_consnames in
  let nindices = List.length ind_d.mind_arity_ctxt - List.length mind_d.mind_params_ctxt in
  let mind_arity_ctxt = List.map EConstr.of_rel_decl ind_d.mind_arity_ctxt in
  let arity_ctx, _ = List.chop nindices mind_arity_ctxt in
  let (sigma, arity_env, arity_ctx') = owtranslate_context env sigma weakly_dom arity_ctx in
  let gen, ind_ = get_ind (wproject env) (mutind, n) in
  let (sigma, (ind_, u)) = Evd.fresh_inductive_instance env.wenv_wtgt sigma ind_ in
  let ind_ = mkIndU (ind_, EInstance.make u) in
  let make_arg (n, accu) (d, wt) = 
    let i = wcontext_type_associated_number wt in
    match d with
    | LocalAssum _ -> (n + i, mkRel (n + i) :: accu)
    | LocalDef _ -> (n + i, accu)
  in
  let warg_context = wargument_of_context env.wenv_src sigma weakly_dom mind_arity_ctxt in
  let (_, args) = List.fold_left make_arg (0,[]) (List.combine mind_arity_ctxt warg_context) in
  let args = if gen then mkRel (Environ.nb_rel arity_env.wenv_wtgt) :: args else args in
  let ind_ = applist (ind_, args) in
  let self = LocalAssum (Anonymous, ind_) in
  let (sigma, sort) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.wenv_wtgt sigma InType in
  let arity = it_mkProd_or_LetIn (mkSort sort) (self :: arity_ctx') in
  let (sigma, _) = Typing.type_of env.wenv_wtgt sigma arity in
  let ind = (mutind, n) in
  let (sigma, lc) = wtranslate_constructors env sigma weakly_dom ind mind_d mind_e ind_d ind_e in
  let lc = List.map (fun c -> EConstr.to_constr sigma c) lc in
  let ind = { ind_e with
    mind_entry_typename = typename;
    mind_entry_arity = EConstr.to_constr sigma arity;
    mind_entry_consnames = constructors;
    mind_entry_lc = lc;
  } in 
  (sigma, ind)

let wtranslate_primitive_projs env sigma mutind mind_d mind_e ind_e =
  let ext_mind, env = wextend_inductive env (mutind, 0) mind_d mind_e in
  let record_constructor = EConstr.of_constr (List.hd ind_e.mind_entry_lc) in
  let _,projections_name,_ = Option.get (Option.get mind_d.mind_record) in
  let fold name = 
    let (_,cst) = get_cst (wproject env) name in
    Globnames.destConstRef cst 
  in
  let projections_name = Array.map fold projections_name in
  let buckets = split_record_constr sigma record_constructor in
  let projections_type = List.firstn (Array.length projections_name) buckets in
  let map (n, sigma, env) t =
    let prev_fields = n - 1 in
    let (sigma, te) = otranslate_type (wproject env) sigma t in 
    let (sigma, tr) = owtranslate_type env sigma t in 
    let tr = Vars.liftn (2*prev_fields + 1) (2*prev_fields + 2) tr in
    let tr = Vars.subst1 (mk_named_proj projections_name (n - 1) (mkRel (4*prev_fields + 1))) tr in
    let projection_subst current_field n = 
      let inverse_field = (n + 1) / 2 in
      if n mod 2 == 0 then
        let record_name = inverse_field + 1 in 
        mk_named_proj projections_name (current_field - record_name) (mkRel (current_field))
      else
        mkRel inverse_field
    in
    let prev_projections = List.init 
                             (2*prev_fields) 
                             (fun i -> projection_subst n (i + 1)) 
    in
    let tr = Vars.substl prev_projections tr in
    let tr = Vars.liftn (- prev_fields) (2*prev_fields + 1) tr in 
    let name = (Names.Name.mk_name (Names.id_of_string "dummy")) in 
    let nenv = push_wassum name  (t, te) (Some tr) env in    
    ((succ n, sigma, nenv), tr)
  in
  let ((_, sigma, env), new_projections) = List.fold_map map (1, sigma, env) projections_type in
  (sigma, new_projections)  

let wtranslate_primitive_record env sigma mutind mind_d mind_e =
  let ind_e = List.hd mind_e.mind_entry_inds in 
  let record_name = ind_e.mind_entry_typename in
  let record_build = List.hd ind_e.mind_entry_consnames in
  let (_,record_projs,_) = Option.get (Option.get mind_d.mind_record) in
  let record_num_projs = Array.length record_projs in
  let gen, ind_ = get_ind (wproject env) (mutind, 0) in
  let (sigma, (ind_, u)) = Evd.fresh_inductive_instance env.wenv_wtgt sigma ind_ in
  let ind_ = mkIndU (ind_, EInstance.make u) in
  (*let make_arg (n, accu) = function
    | LocalAssum _ -> (succ n, mkRel (2 * n) :: accu)
    | LocalDef _ -> (succ n, accu)
  in
  let (_, args) = List.fold_left make_arg (1, []) mind_d.mind_params_ctxt in*)
  let init_record_params i decl = 
    let rel = wdebruijn_lookup env.wcontext (i+1) in
    let rel = match decl with Simple -> rel | Double -> rel + 1 in 
    mkRel (rel)
  in
  let args = List.rev (List.map_i init_record_params 0 env.wcontext )in
  let args = if gen then mkRel (Environ.nb_rel env.wenv_wtgt) :: args else args in
  let ind_ = applist (ind_, args) in
  let (sigma, sort) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.wenv_wtgt sigma InType in
  let arity = mkSort sort in
  let (sigma, _) = Typing.type_of env.wenv_wtgt sigma arity in
  let (sigma, projections) = wtranslate_primitive_projs env sigma mutind mind_d mind_e ind_e in
  let make_arg (n, accu) decl = 
    let rel = 2 * n + record_num_projs + 1 in
    match decl with 
    | LocalAssum _ -> (succ n, mkRel (rel) :: mkRel (rel - 1) :: accu)
    | LocalDef _ -> (succ n, accu)
  in
  let (_, args) = List.fold_left 
                    make_arg 
                    (1, [mkRel (record_num_projs + 1)]) 
                    mind_d.mind_params_ctxt 
  in
  let builder_ctxt = (Environ.nb_rel env.wenv_wtgt) + record_num_projs in
  let args = if gen then mkRel (builder_ctxt + 1) :: args else args in
  let pind = builder_ctxt + 2 in
  let cr = applist (mkRel pind, args) in
  let constr_builder (proj_name, proj_type) partial_record =
    let open Names in 
    let name = wtranslate_name (Label.to_id (Constant.label proj_name)) in
    mkProd (Name.mk_name name, proj_type, partial_record) 
  in
  let zip_projections = List.combine (Array.to_list record_projs) projections in 
  let record_constructor = List.fold_right constr_builder zip_projections cr in
  let decl_to_name decl = 
    let open Context.Rel.Declaration in
    match (get_name decl) with Anonymous -> Names.Id.of_string "" | Name t -> t
  in
  let params_name = List.map decl_to_name (Environ.rel_context env.wenv_wtgt) in
  let fresh_record = Namegen.next_ident_away (Names.Id.of_string "r") params_name in
  let assum = LocalAssum (Names.Name.mk_name fresh_record, EConstr.to_constr sigma ind_) in
  let env = {env with wenv_wtgt = Environ.push_rel assum env.wenv_wtgt } in
  let ind = { ind_e with 
              mind_entry_typename = wtranslate_name record_name;
              mind_entry_arity = EConstr.to_constr sigma arity;
              mind_entry_consnames = [wtranslate_name record_build];
              mind_entry_lc = [EConstr.to_constr sigma record_constructor] 
            }
  in
  (sigma, env, ind)

let param_constr err env sigma (gen,ind_trans,params) mind_d mind_e one_d one_e =
  let make_arg (n, accu) = function
    | LocalAssum _ -> (succ n, mkRel n :: accu)
    | LocalDef _ -> (succ n, accu)
  in
  let map sigma (m, cons) =
    let () = Feedback.msg_info (Pp.str "+++++++++++++++") in 
    let () = Feedback.msg_info (Printer.pr_constr cons) in 
    let cons = EConstr.of_constr cons in
    let cons_ctxt, _ = decompose_prod_assum sigma cons in
    let () = Feedback.msg_info (Pp.int (List.length cons_ctxt)) in
    let (sigma, _, cons_trans) = otranslate_context env sigma cons_ctxt in
    let _,cons_args = List.fold_left make_arg (1,[]) cons_trans in
    let e = Environ.nb_rel env.env_tgt + List.length cons_trans in
    let cons_args = if gen then mkRel e :: cons_args else cons_args in
    let fold ty sigma =
      let (sigma, t) = Evarutil.new_evar env.env_tgt sigma ty in
      (t, sigma)
    in
    let (evar_list, sigma) = List.fold_map' fold params sigma in
    (** FIX: wrong index for blocks with >1 inds *)
    let cons_app = mkRel (e + 1) in
    let n_cons_ind_trans = (ind_trans, m) in
    let (sigma, (n_cons_ind, u)) = Evd.fresh_constructor_instance env.env_tgt sigma n_cons_ind_trans in
    let n_cons_ind = mkConstructU (n_cons_ind, EInstance.make u) in 
    let cons = applist (n_cons_ind, cons_args) in
    let () = Feedback.msg_info (Printer.pr_econstr cons) in
    let cons_term = applist (cons_app, evar_list @ [cons]) in
    let cons_term = it_mkProd_or_LetIn cons_term cons_trans in 
    let () = Feedback.msg_info (Printer.pr_econstr cons_term) in
    (sigma, cons_term)
  in
  let constructors = (List.mapi (fun i d -> (i+1,d)) one_e.mind_entry_lc) in
  let (sigma, lc) = List.fold_map map sigma constructors in 
  (sigma, lc)
    
let param_ind err env sigma (block, n as ind) mind_d mind_e one_d one_e =
  let mind_arity_ctxt = List.map EConstr.of_rel_decl one_d.mind_arity_ctxt in
  let nindices = List.length one_d.mind_arity_ctxt - List.length mind_d.mind_params_ctxt in
  let index_ctxt, _ =  List.chop nindices mind_arity_ctxt in
  let (sigma, arity_env, arity_ctx') = otranslate_context env sigma index_ctxt in
  let gen, ind_trans = get_ind env ind in
  let (sigma, (ind_, u)) = Evd.fresh_inductive_instance env.env_tgt sigma ind_trans in
  let ind_ = mkIndU (ind_, EInstance.make u) in
  let make_arg (n, accu) = function
    | LocalAssum _ -> (succ n, mkRel n :: accu)
    | LocalDef _ -> (succ n, accu)
  in
  let (_, args) = List.fold_left make_arg (1,[]) mind_arity_ctxt  in
  let args = if gen then mkRel (Environ.nb_rel arity_env.env_tgt) :: args else args in
  let ind_ = applist (ind_, args) in
  let self = LocalAssum (Anonymous, ind_) in
  let (sigma, sort) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.env_tgt sigma InType in
  let arity = it_mkProd_or_LetIn (mkSort sort) (self :: arity_ctx') in
  let (sigma, _) = Typing.type_of env.env_tgt sigma arity in

  let (sigma, lc) = param_constr err env sigma (gen, ind_trans, args) mind_d mind_e one_d one_e in
  let lc = List.map (fun c -> EConstr.to_constr sigma c) lc in
  let () = Feedback.msg_info (Pp.prlist Printer.pr_constr lc) in

  let ind = { one_e with
    mind_entry_typename = Names.Id.of_string "asd" (*typename*);
    mind_entry_arity = EConstr.to_constr sigma arity;
    mind_entry_consnames = [](*constructors*);
    (*mind_entry_lc = lc;*)
  } in

  (sigma, ind)
  
    
let param_block err translator env block mind_d mind_e =
  let sigma = Evd.from_env env in
  let (sigma, env) = make_context err translator env sigma in
  let param_name = Id.of_string ("param_ind_") in 
  let record = None in
  let finite = Decl_kinds.Finite in

  let of_rel_decl_param_ctxt = List.map EConstr.of_rel_decl mind_d.mind_params_ctxt in
  let (sigma, env, _) = otranslate_context env sigma of_rel_decl_param_ctxt in

  let map sigma (n, ind_d, ind_e) =
    param_ind err env sigma (block, n) mind_d mind_e ind_d ind_e
  in
  let inds = List.combine (Array.to_list mind_d.mind_packets) mind_e.mind_entry_inds in
  let inds = List.mapi (fun i (l,r) -> (i,l,r)) inds in 
  let (sigma, param_inds) = List.fold_map map sigma inds in   
  (*
  let entry = { mind_e with
      mind_entry_record = record;
      mind_entry_finite = finite;
      mind_entry_params = params;
    }
  in
   *)
  ()

    
let wtranslate_inductive err translator env mutind mind_d (mind_e : Entries.mutual_inductive_entry) =
  let sigma = Evd.from_env env in
  let weakly_arities = Array.map one_ind_in_prop mind_d.mind_packets in
  let weakly_dom = Array.get weakly_arities 0 in
  let _ = if Array.for_all (fun pr -> pr == weakly_dom) weakly_arities 
          then () 
          else let msg = "Incoherent translation: Mutual inductive arity is Prop and Type" in
               CErrors.user_err (str msg)
  in
  let (sigma, env) = make_wcontext err translator env sigma in
  let of_rel_decl_param_ctxt = List.map EConstr.of_rel_decl mind_d.mind_params_ctxt in
  let (sigma, env, _) = owtranslate_context env sigma weakly_dom of_rel_decl_param_ctxt in
  let (sigma, env, inds) = 
    if Inductive.is_primitive_record (mind_d,mind_d.mind_packets.(0)) then 
      let (sigma, env, pind) = wtranslate_primitive_record env sigma mutind mind_d mind_e in
      (sigma, env, [pind])
    else 
      let inds = List.combine (Array.to_list mind_d.mind_packets) mind_e.mind_entry_inds in
      let inds = List.mapi (fun i (ind, ind0) -> (i, ind, ind0)) inds in
      let map sigma (n, ind0, ind) = 
        let partial = wtranslate_inductive_body err env sigma weakly_dom in 
        let (sigma, ind) =  partial mutind mind_d mind_e n ind0 ind in
        (sigma, ind)
      in
      let sigma, inds = List.fold_map map sigma inds in
      (sigma, env, inds)
  in
  let wenv_context = EConstr.rel_context env.wenv_wtgt in
  let sigma, inds, params = EUtil.retype_inductive env.wenv_wtgt sigma wenv_context inds in
  let params = List.map to_local_entry params in
  let uctx = UState.context (Evd.evar_universe_context sigma) in
  let univs = match mind_e.mind_entry_universes with
  | Monomorphic_ind_entry _ -> Monomorphic_ind_entry uctx
  | Polymorphic_ind_entry _ -> Polymorphic_ind_entry uctx
  | Cumulative_ind_entry _ -> Polymorphic_ind_entry uctx (** FIXME *)
  in
  let mind = { mind_e with
    mind_entry_inds = inds;
    mind_entry_params = params;
    mind_entry_universes = univs;
  } in
  mind
