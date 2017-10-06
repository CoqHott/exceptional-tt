open Names
open Globnames

type effect = global_reference option

exception MissingGlobal of effect * global_reference
exception MissingPrimitive of global_reference

type 'a global_translation =
| GlobGen of 'a
  (** Implementation generic over the type of exceptions *)
| GlobImp of 'a Refmap.t
  (** For every type of exceptions, a specialized implementation. *)

val get_instance : effect -> 'a global_translation -> bool * 'a

type translator = {
  refs : global_reference global_translation Cmap.t;
  inds : MutInd.t global_translation Mindmap.t;
  prefs : global_reference global_translation Cmap.t;
  pinds : MutInd.t global_translation Mindmap.t;
}

val translate :
  effect -> translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val translate_type :
  effect -> translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val translate_inductive :
  effect -> translator -> Environ.env -> Declarations.mutual_inductive_body ->
    Entries.mutual_inductive_entry -> Entries.mutual_inductive_entry

val ptranslate :
  effect -> translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val ptranslate_type :
  effect -> translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t
