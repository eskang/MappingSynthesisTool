package synthesis

import constraints.ImplConstraints
import mapping.Mapping
import types.MappingExplorer
import types.Store
import mapping.OAuth1Mapping

object SynthesizerOAuth1Spin extends MappingExplorer(OAuth1Mapping.mapping2){ 
  val DIR_MODEL = "models/spin/oauth/"
  val DIR_GENERATED = "models/spin/generated/"
  val PREFIX_GENERATED = "gen_mapping"
  val PATH_TEMPLATE = "models/spin/oauth/oauth1-to-http-template.pml"
  val MODE = "SPIN" 
}
