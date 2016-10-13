open Names
open Libnames
open Proofview

val translate : reference -> Id.t list option -> unit

val implement : Id.t -> Constrexpr.constr_expr -> Id.t option -> unit
