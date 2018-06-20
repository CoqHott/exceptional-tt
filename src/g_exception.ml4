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

| [ "Parametricity" "Translate" global(gr) ] ->
  [ EPlugin.ptranslate gr ]
| [ "Parametricity" "Translate" global(gr) "as" ne_ident_list(names) ] ->
  [ EPlugin.ptranslate ~names gr ]
| [ "Parametricity" "Translate" global(gr) "using" global(exn) ] ->
  [ EPlugin.ptranslate ~exn gr ]

| [ "Weakly" "Translate" global(gr) ] ->
  [ EPlugin.wtranslate gr ]
| [ "Weakly" "Translate" global(gr) "using" global(exn)] ->
  [ EPlugin.wtranslate ~exn gr ]

| [ "Effect" "List" "Translate" global_list(gr) ] ->
  [ EPlugin.list_translate gr ]
| [ "Effect" "List" "Translate" global_list(gr) "using" global(exn) ] ->
  [ EPlugin.list_translate ~exn gr ]
| [ "Weakly" "List" "Translate" global_list(gr) ] ->
  [ EPlugin.list_wtranslate gr ]
| [ "Weakly" "List" "Translate" global_list(gr) "using" global(exn) ] ->
  [ EPlugin.list_wtranslate ~exn gr ]
| [ "Parametricity" "List" "Translate" global_list(gr) ] ->
  [ EPlugin.list_ptranslate gr ]
| [ "Parametricity" "List" "Translate" global_list(gr) "using" global(exn) ] ->
  [ EPlugin.list_ptranslate ~exn gr ]

END

let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)

VERNAC COMMAND EXTEND EffectImplementation CLASSIFIED BY classify_impl
| [ "Effect" "Definition" ident(id) ":" lconstr(typ) ] ->
  [ EPlugin.implement id typ ]
| [ "Effect" "Definition" ident(id) ":" lconstr(typ) "using" reference(exn) ] ->
  [ EPlugin.implement ~exn id typ ]

| [ "Weakly" "Definition" global(gr) ] ->
  [ EPlugin.wimplement gr ]
| [ "Weakly" "Definition" global(gr)  "using" reference(exn) ] ->
  [ EPlugin.wimplement ~exn gr ]

| [ "Parametricity" "Definition" global(gr) ] ->
  [ EPlugin.pimplement gr ]
| [ "Parametricity" "Definition" global(gr) "using" reference(exn) ] ->
  [ EPlugin.pimplement ~exn gr ]
END

