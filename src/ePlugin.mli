open Names
open Libnames
open ETranslate

val translate : ?exn:reference -> ?names:Id.t list -> reference -> unit
val ptranslate : ?exn:reference -> ?names:Id.t list -> reference -> unit

val implement : ?exn:reference -> Id.t -> Constrexpr.constr_expr -> unit
val pimplement : ?exn:reference -> reference -> unit
