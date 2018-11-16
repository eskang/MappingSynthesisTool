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
import mapping.OAuth2Mapping

object SynthesizerOAuthSpin extends MappingExplorer {

  val mapping = OAuth2Mapping.mapping;

  val DIR_MODEL = "models/spin/oauth/"
  val DIR_GENERATED = "models/spin/generated/"
  val PREFIX_GENERATED = "gen_mapping"
  val PATH_TEMPLATE = "models/spin/oauth/oauth-to-http-template.pml"
  val MODE = "SPIN"
}
