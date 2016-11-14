open Constrarg
open Extraargs

DECLARE PLUGIN "exception"

VERNAC COMMAND EXTEND EffectTranslation CLASSIFIED AS SIDEFF
| [ "Effect" "Translate" global(gr) ] ->
  [ EPlugin.translate gr None ]
| [ "Effect" "Translate" global(gr) "as" ne_ident_list(id) ] ->
  [ EPlugin.translate gr (Some id) ]
END

let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)

VERNAC COMMAND EXTEND EffectImplementation CLASSIFIED BY classify_impl
| [ "Effect" "Definition" ident(id) ":" lconstr(typ) ] ->
  [ EPlugin.implement id typ None ]
| [ "Effect" "Definition" ident(id) ":" lconstr(typ) "as" ident(id') ] ->
  [ EPlugin.implement id typ (Some id') ]
END
