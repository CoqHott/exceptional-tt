open Util
open Context
open Names
open Term
open Declarations
open Environ
open Globnames
open Pp

exception MissingGlobal of global_reference
exception MissingPrimitive of global_reference

type effect = ModPath.t

type translator = {
  effs : effect;
  refs : global_reference Refmap.t;
}

type context = {
  translator : translator;
  env_src : Environ.env;
  env_tgt : Environ.env;
}

let push_assum na (t, te) env = { env with
  env_src = Environ.push_rel (Rel.Declaration.LocalAssum (na, t)) env.env_src;
  env_tgt = Environ.push_rel (Rel.Declaration.LocalAssum (na, te)) env.env_tgt;
}

let push_def na (c, ce) (t, te) env = { env with
  env_src = Environ.push_rel (Rel.Declaration.LocalDef (na, c, t)) env.env_src;
  env_tgt = Environ.push_rel (Rel.Declaration.LocalDef (na, ce, te)) env.env_tgt;
}

(** Coq-defined values *)

let effect_path =
  DirPath.make (List.map Id.of_string ["Effects"; "Effects"])

let proj1 =
  let kn = KerName.make2 (MPfile effect_path) (Label.make "wit") in
  let const = Constant.make1 kn in
  Projection.make const false

let make_kn eff name =
  KerName.make2 eff (Label.make name)

let prop_e eff = ConstRef (Constant.make1 (make_kn eff "Propᵉ"))
let set_e eff = ConstRef (Constant.make1 (make_kn eff "Setᵉ"))
let type_e eff = ConstRef (Constant.make1 (make_kn eff "Typeᵉ"))
let prod_e eff = ConstRef (Constant.make1 (make_kn eff "Prodᵉ"))
let el_e eff = ConstRef (Constant.make1 (make_kn eff "El"))

let dummy = mkProp
let free_algebra eff = ConstRef (Constant.make1 (make_kn eff.translator.effs "Free"))


(** Handling of globals *) 

let apply_global env sigma gr =
  let gr =
    try Refmap.find gr env.translator.refs
    with Not_found -> raise (MissingGlobal gr)
  in
  let (sigma, c) = Evd.fresh_global env.env_tgt sigma gr in
  (sigma, c)

let mkHole env sigma =
  let open Sigma.Notations in
  let sigma = Sigma.Unsafe.of_evar_map sigma in
  let Sigma ((typ, _), sigma, _) = Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
  let Sigma (c, sigma, _) = Evarutil.new_evar env sigma typ in
  (Sigma.to_evar_map sigma, c)

let fresh_global env sigma global =
  let gr = global env.translator.effs in
  try Evd.fresh_global env.env_tgt sigma gr
  with Not_found -> raise (MissingPrimitive gr)

(** Effect translation core *)

let element env sigma c =
  let (sigma, el) = fresh_global env sigma el_e in
  (sigma, mkProj (proj1, mkApp (el, [|c|])))

let rec otranslate env sigma c = match kind_of_term c with
| Rel n ->
  (sigma, mkRel n)
| Sort (Prop Null) ->
  let (sigma, c) = fresh_global env sigma prop_e in
  (sigma, c)
| Sort (Prop Pos) ->
  let (sigma, c) = fresh_global env sigma set_e in
  (sigma, c)
| Sort (Type _) ->
  let (sigma, c) = fresh_global env sigma type_e in
  (sigma, c)
| Cast (c, k, t) ->
  let (sigma, ce) = otranslate env sigma c in
  let (sigma, te) = otranslate env sigma t in
  let (sigma, tTe) = element env sigma te in
  let r = mkCast (ce, k, tTe) in
  (sigma, r)
| Prod (na, t, u) ->
  let (sigma, p) = fresh_global env sigma prod_e in
  let (sigma, te) = otranslate env sigma t in
  let (sigma, tTe) = element env sigma te in
  let env = push_assum na (t, tTe) env in
  let (sigma, ue) = otranslate env sigma u in
  let ue = mkLambda (na, tTe, ue) in
  let r = mkApp (p, [|te; ue|]) in
  (sigma, r)
| Lambda (na, t, u) ->
  let (sigma, te) = otranslate env sigma t in
  let (sigma, el_te) = element env sigma te in
  let env = push_assum na (t, el_te) env in
  let (sigma, ue) = otranslate env sigma u in
  let r = mkLambda (na, el_te, ue) in
  (sigma, r)
| LetIn (na, c, t, u) ->
  let (sigma, ce) = otranslate env sigma c in
  let (sigma, te) = otranslate env sigma t in
  let (sigma, el_te) = element env sigma te in
  let env = push_def na (c, ce) (t, el_te) env in
  let (sigma, ue) = otranslate env sigma u in
  let r = mkLetIn (na, ce, el_te, ue) in
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

and otranslate_type env sigma t =
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
  let env = {
    translator;
    env_src = env;
    env_tgt = env;
  } in
  (sigma, env)

let push_context (ctx, ctx_) env =
  let env_src = Environ.push_rel_context ctx env.env_src in
  let env_tgt = Environ.push_rel_context ctx_ env.env_tgt in
  { env with env_src; env_tgt }

let translate env sigma c =
  let (sigma, c_) = otranslate env sigma c in
  let (sigma, _) = Typing.type_of env.env_tgt sigma c_ in
  (sigma, c_)

let translate_type env sigma c =
  let (sigma, c_) = otranslate env sigma c in
  let (sigma, c_) = element env sigma c_ in
  let (sigma, _) = Typing.type_of env.env_tgt sigma c_ in
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
