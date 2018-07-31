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

val instantiate_error : effect -> Environ.env -> Evd.evar_map -> bool -> EConstr.t -> Evd.evar_map * EConstr.t

type translator = {
  refs : global_reference global_translation Cmap.t;
  inds : MutInd.t global_translation Mindmap.t;
  prefs : global_reference global_translation Cmap.t;
  pinds : MutInd.t global_translation Mindmap.t;
  wrefs : global_reference global_translation Cmap.t;
  winds : MutInd.t global_translation Mindmap.t;
}

val translate :
  effect -> translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val translate_type :
  effect -> translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val translate_inductive :
  effect -> translator -> Environ.env -> MutInd.t -> Declarations.mutual_inductive_body ->
    Entries.mutual_inductive_entry -> Entries.mutual_inductive_entry

val ptranslate :
  effect -> translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val ptranslate_type :
  effect -> translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val ptranslate_inductive :
  effect -> translator -> Environ.env -> MutInd.t -> Declarations.mutual_inductive_body ->
    Entries.mutual_inductive_entry -> Entries.mutual_inductive_entry

val wtranslate :
  effect -> translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val wtranslate_type :
  effect -> translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val wtranslate_inductive :
  effect -> translator -> Environ.env -> MutInd.t -> Declarations.mutual_inductive_body ->
    Entries.mutual_inductive_entry -> Entries.mutual_inductive_entry

val param_block :
  effect -> translator -> Environ.env -> MutInd.t -> Declarations.mutual_inductive_body ->
  Entries.mutual_inductive_entry -> unit(*Entries.mutual_inductive_entry*)
