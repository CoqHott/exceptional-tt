open Names
open Libnames

val translate : ?exn:reference -> ?names:Id.t list -> reference -> unit
val ptranslate : ?exn:reference -> ?names:Id.t list -> reference -> unit

val implement : ?exn:reference -> Id.t -> Constrexpr.constr_expr -> unit
val pimplement : ?exn:reference -> reference -> unit

val wtranslate : ?exn:reference -> ?names:Id.t list -> reference -> unit
val wimplement : ?exn:reference -> reference -> unit

(** Translate of list *)
val list_translate : ?exn:reference -> reference list -> unit
val list_ptranslate : ?exn:reference -> reference list -> unit
val list_wtranslate : ?exn:reference -> reference list -> unit

