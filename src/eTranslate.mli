open Names
open Globnames
open Context

exception MissingGlobal of global_reference
exception MissingPrimitive of global_reference

type translator = {
  refs : global_reference Refmap.t;
}

val translate :
  translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val translate_type :
  translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val translate_inductive :
  translator -> Environ.env -> Declarations.mutual_inductive_body ->
    Entries.mutual_inductive_entry -> Entries.mutual_inductive_entry
