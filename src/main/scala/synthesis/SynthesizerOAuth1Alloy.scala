package synthesis

import constraints.ImplConstraints
import mapping.Mapping
import types.MappingExplorer
import types.Store
import types.Config
import mapping.OAuth1Mapping

object SynthesizerOAuth1Alloy extends MappingExplorer(OAuth1Mapping.mapping1) { 
  def setConfig = {
    Config.DIR_MODEL = "models/alloy/oauth/"
    Config.DIR_GENERATED = "models/alloy/generated/"
    Config.PREFIX_GENERATED = "gen_mapping"
    Config.PATH_TEMPLATE = "models/alloy/oauth/oauth1-to-http-template.als"
    Config.MODE = "ALLOY"
  }
}
