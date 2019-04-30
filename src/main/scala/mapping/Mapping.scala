/**
 * Contains mappings between a pair of abstract & concrete models
 * Provides a function to incrementally enumerate one mapping at a time
 * 
 * Created by: Eunsuk Kang
 */
package mapping

import types.Label
import constraints.ImplConstraints

class Mapping(implConstraints: Set[ImplConstraints]) {
  
  private val iters = scala.collection.mutable.Map[ImplConstraints, Iterator[Map[String,String]]](); 
  private val curr = scala.collection.mutable.Map[ImplConstraints, Map[String,String]]();
  
  /**
   * Generate mappings for each abstract-concrete label pair
   * and reset the iterators for each list of mappings 
   */
  def genMapings() = {
    iters ++= (implConstraints.map(i => (i, i.enumerateMappings)))  
    iters.foreach(p => curr(p._1) = p._2.next)
  }
  
  def numMappings : Int = {
    implConstraints.foldLeft(1){ (n, e) => n * e.getNumMappings }
  }
  
  /**
   * Increment the iterator to obtain the next mapping
   */
  def increment(is: List[ImplConstraints]) : Boolean = {
    val hd = is.head
    val tl = is.tail
     
    while (true){
      var exhausted = true

      if (!tl.isEmpty) {
        exhausted = increment(tl)
      }
      
      if (!exhausted) {
        return false  
      } else if (exhausted && iters(hd).hasNext) {
        curr(hd) = iters(hd).next
        return false
      } else {
        iters(hd) = hd.iter
        curr(hd) = iters(hd).next
        return true
      } 
    }
    return true
  }
  
  /**
   * Obtain the next mapping & store it in "curr"
   * Returns true iff if there's still a mapping remain to be explored
   */
  def next() : Boolean = {
    val done = increment(implConstraints.toList)    
    return !done
  }
  
  def currMapping: Map[ImplConstraints, Map[String,String]] = {
    return curr.toMap  
  }
  
}