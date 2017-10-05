open Stdarg
open Extraargs

DECLARE PLUGIN "exception"

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
END
