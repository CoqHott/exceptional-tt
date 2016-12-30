open Names
open Globnames
open Context

exception MissingGlobal of global_reference
exception MissingPrimitive of global_reference

type effect = ModPath.t

type context

type translator = {
  effs : effect;
  refs : global_reference Refmap.t;
}

val make_context : translator -> Environ.env -> Evd.evar_map -> Evd.evar_map * context

val push_context : Context.Rel.t * Context.Rel.t -> context -> context
(** Push source / translated context *)

val translate :
  context -> Evd.evar_map -> Constr.t -> Evd.evar_map * Constr.t

val translate_type :
  context -> Evd.evar_map -> Constr.t -> Evd.evar_map * Constr.t

val translate_context :
  context -> Evd.evar_map -> Context.Rel.t -> Evd.evar_map * Context.Rel.t

val free_algebra : context -> global_reference
(** The function producing the free type algebra *)

(** Variants that do not typecheck *)

val otranslate :
  context -> Evd.evar_map -> Constr.t -> Evd.evar_map * Constr.t

val otranslate_type :
  context -> Evd.evar_map -> Constr.t -> Evd.evar_map * Constr.t

val otranslate_context :
  context -> Evd.evar_map -> Context.Rel.t -> Evd.evar_map * Context.Rel.t
