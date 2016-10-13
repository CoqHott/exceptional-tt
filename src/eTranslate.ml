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
}

(** We assume that there is a hidden topmost variable [p : Obj] in the context *)

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

(** Forcing translation core *)

let rec otranslate env fctx sigma c = match kind_of_term c with
| Rel n -> mkRel n
| Sort s ->
  assert false
| Cast (c, k, t) ->
  assert false
| Prod (na, t, u) ->
  assert false
| Lambda (na, t, u) ->
  assert false
| LetIn (na, c, t, u) ->
  assert false
| App (t, args) when isInd t ->
  assert false
| App (t, args) ->
  assert false
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

let translate ?(toplevel = true) ?lift translator env sigma c =
  assert false

let translate_type ?(toplevel = true) ?lift translator env sigma c =
  assert false

let translate_context ?(toplevel = true) ?lift translator env sigma ctx =
  assert false
