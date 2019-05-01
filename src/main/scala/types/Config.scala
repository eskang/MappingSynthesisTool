package types

import writer.Logger;

object Config {
  var DIR_MODEL = "models/alloy/oauth/"
  var DIR_GENERATED = "models/alloy/generated/"
  var PREFIX_GENERATED = "gen_mapping"
  var PATH_TEMPLATE = "models/alloy/oauth/oauth1-to-http-template.als"
  var MODE = "ALLOY" 
  var VERBOSITY = Logger.VERBOSE;
}
