open Names
open Libnames
open Proofview

val force_translate : reference -> Id.t list option -> unit

val force_implement : Id.t -> Constrexpr.constr_expr -> Id.t option -> unit
