open Stdarg
open Ltac_plugin.Extraargs

DECLARE PLUGIN "exception"

let wit_lconstr = Obj.magic wit_lconstr
(** FUCK YOU API *)

VERNAC COMMAND EXTEND EffectTranslation CLASSIFIED AS SIDEFF
| [ "Effect" "Translate" global(gr) ] ->
  [ EPlugin.translate gr ]
| [ "Effect" "Translate" global(gr) "as" ne_ident_list(names) ] ->
  [ EPlugin.translate ~names gr ]
| [ "Effect" "Translate" global(gr) "using" global(exn) ] ->
  [ EPlugin.translate ~exn gr ]

| [ "Effect" "List" "Translate" global_list(gr) ] ->
  [ EPlugin.list_translate gr ]
| [ "Effect" "List" "Translate" global_list(gr) "using" global(exn) ] ->
  [ EPlugin.list_translate ~exn gr ]

END

let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)

VERNAC COMMAND EXTEND EffectImplementation CLASSIFIED BY classify_impl
| [ "Effect" "Definition" ident(id) ":" lconstr(typ) ] ->
  [ EPlugin.implement id typ ]
| [ "Effect" "Definition" ident(id) ":" lconstr(typ) "using" reference(exn) ] ->
  [ EPlugin.implement ~exn id typ ]

END

