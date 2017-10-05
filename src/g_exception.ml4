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
| [ "Effect" "Definition" ident(id) ":" lconstr(typ) "using" reference(exn) ] ->
  [ EPlugin.implement ~exn id typ ]
| [ "Parametricity" "Translate" global(gr) ] ->
  [ EPlugin.ptranslate gr ]
| [ "Parametricity" "Translate" global(gr) "as" ne_ident_list(names) ] ->
  [ EPlugin.ptranslate ~names gr ]
| [ "Parametricity" "Translate" global(gr) "using" global(exn) ] ->
  [ EPlugin.ptranslate ~exn gr ]
END
