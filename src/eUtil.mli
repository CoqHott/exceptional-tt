open Entries
open Declarations
open Environ
open Evd

val retype_inductive :
  env -> evar_map -> EConstr.rel_context ->
  one_inductive_entry list ->
  evar_map * one_inductive_entry list * Context.Rel.t

val process_inductive : mutual_inductive_body -> mutual_inductive_entry
