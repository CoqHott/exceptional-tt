open Util
open Context
open Names
open Term
open EConstr
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
  env_src = EConstr.push_rel (Rel.Declaration.LocalAssum (na, t)) env.env_src;
  env_tgt = EConstr.push_rel (Rel.Declaration.LocalAssum (na, te)) env.env_tgt;
}

let push_def na (c, ce) (t, te) env = { env with
  env_src = EConstr.push_rel (Rel.Declaration.LocalDef (na, c, t)) env.env_src;
  env_tgt = EConstr.push_rel (Rel.Declaration.LocalDef (na, ce, te)) env.env_tgt;
}

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
  (sigma, c)

let mkHole env sigma =
  let sigma, (typ, _) = Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
  let sigma, c = Evarutil.new_evar env sigma typ in
  (sigma, c)

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
| Prod (na, t, u) ->
  let (sigma, te) = otranslate_type env sigma t in
  let env = push_assum na (t, te) env in
  let (sigma, ue) = otranslate_type env sigma u in
  (sigma, mkProd (na, te, ue))
| _ ->
  let (sigma, t_) = otranslate env sigma t in
  let (sigma, t_) = element env sigma t_ in
  (sigma, t_)

let otranslate_context env sigma ctx =
  let open Rel.Declaration in
  let fold decl (sigma, env, accu) = match decl with
  | LocalAssum (na, t) ->
    let (sigma, t_) = otranslate env sigma t in
    let (sigma, t_) = element env sigma t_ in
    (sigma, push_assum na (t, t_) env, LocalAssum (na, t_) :: accu)
  | LocalDef (na, c, t) ->
    let (sigma, t_) = otranslate env sigma t in
    let (sigma, t_) = element env sigma t_ in
    let (sigma, c_) = otranslate env sigma c in
    (sigma, push_def na (c, c_) (t, t_) env, LocalDef (na, c_, t_) :: accu)
  in
  let (sigma, _, ctx) = List.fold_right fold ctx (sigma, env, []) in
  (sigma, ctx)

(** The toplevel option allows to close over the topmost forcing condition *)

let make_context translator env sigma =
  let (sigma, s) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env sigma InType in
  let e = Id.of_string "E" in
  let env_tgt = Environ.push_rel (Rel.Declaration.LocalAssum (Name e, Constr.mkSort s)) env in
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

let translate env sigma c =
  let (sigma, c_) = otranslate env sigma c in
  let decl = get_exception env in
  let c_ = mkLambda_or_LetIn decl c_ in
  let (sigma, _) = Typing.type_of env.env_src sigma c_ in
  (sigma, c_)

let translate_type env sigma c =
  let (sigma, c_) = otranslate_type env sigma c in
  let decl = get_exception env in
  let c_ = mkProd_or_LetIn decl c_ in
  let (sigma, _) = Typing.type_of env.env_src sigma c_ in
  (sigma, c_)

let translate_context env sigma ctx =
  let open Rel.Declaration in
  let fold decl (sigma, env, accu) = match decl with
  | LocalAssum (na, t) ->
    let (sigma, t_) = otranslate env sigma t in
    let (sigma, t_) = element env sigma t_ in
    let (sigma, _) = Typing.type_of env.env_tgt sigma t_ in
    (sigma, push_assum na (t, t_) env, LocalAssum (na, t_) :: accu)
  | LocalDef (na, c, t) ->
    let (sigma, t_) = otranslate env sigma t in
    let (sigma, t_) = element env sigma t_ in
    let (sigma, _) = Typing.type_of env.env_tgt sigma t_ in
    let (sigma, c_) = otranslate env sigma c in
    let (sigma, _) = Typing.type_of env.env_tgt sigma c_ in
    (sigma, push_def na (c, c_) (t, t_) env, LocalDef (na, c_, t_) :: accu)
  in
  let (sigma, _, ctx) = List.fold_right fold ctx (sigma, env, []) in
  (sigma, ctx)
