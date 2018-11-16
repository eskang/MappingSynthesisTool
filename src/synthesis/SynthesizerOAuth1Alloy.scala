package synthesis

import constraints.ImplConstraints
import mapping.Mapping
import types.MappingExplorer
import types.Store
import mapping.OAuth1Mapping

object SynthesizerOAuth1Alloy extends MappingExplorer {
 
  val mapping = OAuth1Mapping.mapping1;
  
  val DIR_MODEL = "models/alloy/oauth/"
  val DIR_GENERATED = "models/alloy/generated/"
  val PREFIX_GENERATED = "gen_mapping"
  val PATH_TEMPLATE = "models/alloy/oauth/oauth1-to-http-template.als"
  val MODE = "ALLOY"
}