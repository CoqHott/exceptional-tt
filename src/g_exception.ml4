open Constrarg
open Extraargs

DECLARE PLUGIN "exception"

VERNAC COMMAND EXTEND ForcingTranslation CLASSIFIED AS SIDEFF
| [ "Exception" "Translate" global(gr) ] ->
  [ EPlugin.force_translate gr None ]
| [ "Exception" "Translate" global(gr) "as" ne_ident_list(id) ] ->
  [ EPlugin.force_translate gr (Some id) ]
END

let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)

VERNAC COMMAND EXTEND ForcingImplementation CLASSIFIED BY classify_impl
| [ "Exception" "Definition" ident(id) ":" lconstr(typ) ] ->
  [ EPlugin.force_implement id typ None ]
| [ "Exception" "Definition" ident(id) ":" lconstr(typ) "as" ident(id') ] ->
  [ EPlugin.force_implement id typ (Some id') ]
END
