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
import mapping.OAuth2Mapping

object SynthesizerOAuthAlloy extends MappingExplorer {  
  
  val mapping = OAuth2Mapping.mapping; 
    
  val DIR_MODEL = "models/alloy/oauth/"
  val DIR_GENERATED = "models/alloy/generated/"
  val PREFIX_GENERATED = "gen_mapping"
  val PATH_TEMPLATE = "models/alloy/oauth/oauth-to-http-template.als"
  val MODE = "ALLOY"
}
