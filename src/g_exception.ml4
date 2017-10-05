open Stdarg
open Extraargs

DECLARE PLUGIN "exception"

VERNAC COMMAND EXTEND EffectTranslation CLASSIFIED AS SIDEFF
| [ "Effect" "Translate" global(gr) ] ->
  [ EPlugin.translate gr None ]
| [ "Effect" "Translate" global(gr) "as" ne_ident_list(id) ] ->
  [ EPlugin.translate gr (Some id) ]
| [ "Parametricity" "Translate" global(gr) ] ->
  [ EPlugin.ptranslate gr None ]
| [ "Parametricity" "Translate" global(gr) "as" ne_ident_list(id) ] ->
  [ EPlugin.ptranslate gr (Some id) ]
END
