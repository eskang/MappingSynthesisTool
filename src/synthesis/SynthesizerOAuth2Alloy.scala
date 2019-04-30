/**
 * Construction of mappings from the OAuth to HTTP model
 *
 * Created by: Eunsuk Kang
 */

package synthesis

import constraints.ImplConstraints
import mapping.Mapping
import types.MappingExplorer
import types.Store
import types.Config
import mapping.OAuth2Mapping

object SynthesizerOAuthAlloy extends MappingExplorer(OAuth2Mapping.mapping){
  def setConfig = {
    Config.DIR_MODEL = "models/alloy/oauth/"
    Config.DIR_GENERATED = "models/alloy/generated/"
    Config.PREFIX_GENERATED = "gen_mapping"
    Config.PATH_TEMPLATE = "models/alloy/oauth/oauth-to-http-template.als"
    Config.MODE = "ALLOY"
  }
}
