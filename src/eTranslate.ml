open Context
open Names
open Term
open Declarations
open Environ
open Globnames
open Pp

type translator = global_reference Refmap.t
exception MissingGlobal of global_reference

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

let exception_path =
  let dp = ["Exception"; "Exception"] in
  let dp = DirPath.make (List.rev_map Id.of_string dp) in
  ModPath.MPfile dp

let make_kn name =
  KerName.make2 exception_path (Label.make name)

let prop_e = Constant.make1 (make_kn "Propᵉ")
let set_e = Constant.make1 (make_kn "Setᵉ")
let type_e = Constant.make1 (make_kn "Typeᵉ")
let prod_e = Constant.make1 (make_kn "Prodᵉ")
let lambda_e = Constant.make1 (make_kn "Lamᵉ")
let app_e = Constant.make1 (make_kn "Appᵉ")
let el_e = Constant.make1 (make_kn "El")

let dummy = mkProp

(** Handling of globals *) 

let get_inductive fctx ind =
  let gr = IndRef ind in
  let gr_ =
    try Refmap.find gr fctx.translator
    with Not_found -> raise (MissingGlobal gr)
  in
  match gr_ with
  | IndRef ind_ -> ind_
  | _ -> assert false

let apply_global env sigma gr u fctx =
  (** FIXME *)
  let p' =
    try Refmap.find gr fctx.translator
    with Not_found -> raise (MissingGlobal gr)
  in
  let (sigma, c) = Evd.fresh_global env sigma p' in
  (sigma, c)

let mkHole env sigma =
  let open Sigma.Notations in
  let sigma = Sigma.Unsafe.of_evar_map sigma in
  let Sigma ((typ, _), sigma, _) = Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
  let Sigma (c, sigma, _) = Evarutil.new_evar env sigma typ in
  (Sigma.to_evar_map sigma, c)

(** Forcing translation core *)

let rec otranslate env sigma c = match kind_of_term c with
| Rel n ->
  (sigma, mkRel n)
| Sort (Prop Null) ->
  let (sigma, c) = Evd.fresh_constant_instance env.env_tgt sigma prop_e in
  (sigma, mkConstU c)
| Sort (Prop Pos) ->
  let (sigma, c) = Evd.fresh_constant_instance env.env_tgt sigma set_e in
  (sigma, mkConstU c)
| Sort (Type _) ->
  let (sigma, c) = Evd.fresh_constant_instance env.env_tgt sigma type_e in
  (sigma, mkConstU c)
| Cast (c, k, t) ->
  assert false
| Prod (na, t, u) ->
  let (sigma, p) = Evd.fresh_constant_instance env.env_tgt sigma prod_e in
  let (sigma, el) = Evd.fresh_constant_instance env.env_tgt sigma el_e in
  let (sigma, te) = otranslate env sigma t in
  let el_te = mkApp (mkConstU el, [|te|]) in
  let env = push_assum na (t, el_te) env in
  let (sigma, ue) = otranslate env sigma u in
  let p = mkConstU p in
  let ue = mkLambda (na, el_te, ue) in
  let r = mkApp (p, [|te; ue|]) in
  (sigma, r)
| Lambda (na, t, u) ->
  let (sigma, p) = Evd.fresh_constant_instance env.env_tgt sigma lambda_e in
  let (sigma, el) = Evd.fresh_constant_instance env.env_tgt sigma el_e in
  let (sigma, te) = otranslate env sigma t in
  let el_te = mkApp (mkConstU el, [|te|]) in
  let env = push_assum na (t, el_te) env in
  let (sigma, ue) = otranslate env sigma u in
  let ue = mkLambda (na, el_te, ue) in
  let uT = Retyping.get_type_of env.env_src sigma u in
  let (sigma, uTe) = otranslate env sigma uT in
  let uTe = mkLambda (na, el_te, uTe) in
  let r = mkApp (mkConstU p, [|te; uTe; ue|]) in
  (sigma, r)
| LetIn (na, c, t, u) ->
  let (sigma, el) = Evd.fresh_constant_instance env.env_tgt sigma el_e in
  let (sigma, ce) = otranslate env sigma c in
  let (sigma, te) = otranslate env sigma t in
  let el_te = mkApp (mkConstU el, [|te|]) in
  let env = push_def na (c, ce) (t, el_te) env in
  let (sigma, ue) = otranslate env sigma u in
  let r = mkLetIn (na, ce, el_te, ue) in
  (sigma, r)
| App (t, args) ->
  let (sigma, te) = otranslate env sigma t in
  let fold (sigma, r, re) arg =
(*     let (sigma, el) = Evd.fresh_constant_instance env.env_tgt sigma el_e in *)
    let (sigma, app) = Evd.fresh_constant_instance env.env_tgt sigma app_e in
(*     let argT = Retyping.get_type_of env.env_src sigma arg in *)
(*     let (sigma, argTe) = otranslate env sigma arg in *)
    let (sigma, arge) = otranslate env sigma arg in
    let r = mkApp (r, [|t|]) in
    let (sigma, h0) = mkHole env.env_tgt sigma in
    let (sigma, h1) = mkHole env.env_tgt sigma in
    let re = mkApp (mkConstU app, [|h0; h1; re; arge|]) in
    (sigma, r, re)
  in
  let (sigma, _, re) = Array.fold_left fold (sigma, t, te) args in
  (sigma, re)
| Var id ->
  assert false
| Const (p, u) ->
  assert false
| Ind (ind, u) ->
  assert false
| Construct (c, u) ->
  assert false
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
  let (sigma, el) = Evd.fresh_constant_instance env.env_tgt sigma el_e in
  let (sigma, ce) = otranslate env sigma c in
  (sigma, mkApp (mkConstU el, [|ce|]))

let translate_context translator env sigma ctx =
  assert false
