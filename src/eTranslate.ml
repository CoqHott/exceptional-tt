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

let make_kn eff name =
  KerName.make2 eff (Label.make name)

let prop_e eff = ConstRef (Constant.make1 (make_kn eff "Propᵉ"))
let set_e eff = ConstRef (Constant.make1 (make_kn eff "Setᵉ"))
let type_e eff = ConstRef (Constant.make1 (make_kn eff "Typeᵉ"))
let prod_e eff = ConstRef (Constant.make1 (make_kn eff "Prodᵉ"))
let el_e eff = ConstRef (Constant.make1 (make_kn eff "El"))

let dummy = mkProp

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
  (sigma, mkApp (el, [|c|]))

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
  let (sigma, el) = fresh_global env sigma el_e in
  let (sigma, te) = otranslate env sigma t in
  let el_te = mkApp (el, [|te|]) in
  let env = push_assum na (t, el_te) env in
  let (sigma, ue) = otranslate env sigma u in
  let r = mkLambda (na, el_te, ue) in
  (sigma, r)
| LetIn (na, c, t, u) ->
  let (sigma, el) = fresh_global env sigma el_e in
  let (sigma, ce) = otranslate env sigma c in
  let (sigma, te) = otranslate env sigma t in
  let el_te = mkApp (el, [|te|]) in
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

(** The toplevel option allows to close over the topmost forcing condition *)

let translate translator env sigma c =
  let env = {
    translator;
    env_src = env;
    env_tgt = env;
  } in
  otranslate env sigma c

let translate_type translator env sigma c =
  let env = {
    translator;
    env_src = env;
    env_tgt = env;
  } in
  let (sigma, el) = fresh_global env sigma el_e in
  let (sigma, ce) = otranslate env sigma c in
  (sigma, mkApp (el, [|ce|]))

let translate_context translator env sigma ctx =
  assert false
