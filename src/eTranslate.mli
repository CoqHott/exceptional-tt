open Globnames

exception MissingGlobal of global_reference

type translator = global_reference Refmap.t

val translate : translator ->
  Environ.env -> Evd.evar_map -> Constr.t -> Evd.evar_map * Constr.t

val translate_type : translator ->
  Environ.env -> Evd.evar_map -> Constr.t -> Evd.evar_map * Constr.t

val translate_context : translator ->
  Environ.env -> Evd.evar_map -> Context.Rel.t -> Evd.evar_map * Context.Rel.t