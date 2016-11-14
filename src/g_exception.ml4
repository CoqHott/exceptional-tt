open Constrarg
open Extraargs

DECLARE PLUGIN "exception"

VERNAC COMMAND EXTEND EffectDeclare CLASSIFIED AS SIDEFF
| [ "Declare" "Effect" reference(eff) ] -> [ EPlugin.declare_effect eff ]
END

VERNAC COMMAND EXTEND EffectTranslation CLASSIFIED AS SIDEFF
| [ "Effect" "Translate" global(gr) "using" reference(eff) ] ->
  [ EPlugin.translate eff gr None ]
| [ "Effect" "Translate" global(gr) "as" ne_ident_list(id) "using" reference(eff) ] ->
  [ EPlugin.translate eff gr (Some id) ]
END

let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)

VERNAC COMMAND EXTEND EffectImplementation CLASSIFIED BY classify_impl
| [ "Effect" "Definition" ident(id) ":" lconstr(typ) "using" reference(eff) ] ->
  [ EPlugin.implement eff id typ None ]
| [ "Effect" "Definition" ident(id) ":" lconstr(typ) "as" ident(id') "using" reference(eff) ] ->
  [ EPlugin.implement eff id typ (Some id') ]
END

