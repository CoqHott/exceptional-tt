open Names
open Libnames

val translate : ?exn:reference -> ?names:Id.t list -> reference -> unit
val ptranslate : ?exn:reference -> ?names:Id.t list -> reference -> unit

val implement : ?exn:reference -> Id.t -> Constrexpr.constr_expr -> unit
val pimplement : ?exn:reference -> reference -> unit

val wtranslate : ?exn:reference -> ?names:Id.t list -> reference -> unit
val wimplement : ?exn:reference -> reference -> unit
