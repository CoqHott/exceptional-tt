open Names
open Libnames

val translate : ?exn:reference -> ?names:Id.t list -> reference -> unit

val implement : ?exn:reference -> Id.t -> Constrexpr.constr_expr -> unit

(** Translate of list *)
val list_translate : ?exn:reference -> reference list -> unit
