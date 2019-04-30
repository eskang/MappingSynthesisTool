package mapping

import constraints.ImplConstraints

object MappingFactory {
  
  private var mapping : Mapping = _
  
  def mkMapping(constraintSets : Set[ImplConstraints]) = {
    mapping = new Mapping(constraintSets)
  }
  
  def getMapping : Mapping = {
    return mapping
  }
}
