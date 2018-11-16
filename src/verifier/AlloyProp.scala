package verifier

abstract class AlloyProp {
  val propName: String
  val defaultScope: Int
  val scopes: List[(String,Int)]
}

object PropMappingLive1 extends AlloyProp {
  val propName = "mappingLiveness1"
  val defaultScope = 3
  val scopes = List(("Event", 7))
  //val defaultScope = 4  
  //val scopes = List(("Event", 8))
}

object PropMappingLive2 extends AlloyProp {
  val propName = "mappingLiveness2"
  val defaultScope = 3
  val scopes = List(("Event", 7))
  //val defaultScope = 4  
  //val scopes = List(("Event", 8))
}

object PropMappingSafe extends AlloyProp {
  val propName = "mappingSafety"
  val defaultScope = 3  
  val scopes = List(("Event", 8))
  //val defaultScope = 4  
  //val scopes = List(("Event", 9))
}
