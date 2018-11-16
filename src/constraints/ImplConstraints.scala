/**
 * Implementation constraints between an abstract and concrete label type
 * 
 * Created by: Eunsuk Kang 
 */

package constraints

import types.Label
import types.Datatype
import types.BasicDatatype
import types.ComplexDatatype
import types.Store
import synthesis.SynthesizerOAuthSpin

object Impl { 
  val COND_FUNC_PREFIX = "$COND_FUNC"
  val UNKNOWN_PREFIX = "$UNKNOWN"
  def extract(condFunc: String) : (String,String) = {
    val l = condFunc.replace(COND_FUNC_PREFIX, "").replace("(","").replace(")","").split(",")
    (l(0), l(1))
  }  
}
  
class ImplConstraints(val abs: Label, val conc: Label) {
  // constraints given by the user
  private val partialConstraints = scala.collection.mutable.Map[String,Constraint]()
  
  val fld2types = scala.collection.mutable.Map[String, Datatype]()
  private val argFields = scala.collection.mutable.Set[String]()
  private val retFields = scala.collection.mutable.Set[String]()
  
  private val currConstraints = scala.collection.mutable.Map[String,Constraint]()
  private val currMap = scala.collection.mutable.Map[String,String]()
  private val currIters = scala.collection.mutable.Map[String, Iterator[String]]()  
  private val prevMaps = scala.collection.mutable.Set[Map[String,String]]()
  private var numMappings = 0

  private var flatConcParams = List[String]()
  private var flatAbsParams = List[String]()
  
  {
    flatConcParams = conc.params.flatMap { case(p, t) => flatten(p, t, null, conc.isRet(p)) }.toList  
    flatAbsParams = abs.params.flatMap { case(p, t) => flatten(p, t, null, abs.isRet(p)) }.toList      
  }
 
  private def flatten(prefix: String, d: Datatype, filter: Datatype = null, isRet: Boolean = false) : List[String] = {
    if (d.isInstanceOf[BasicDatatype]) {
      if (!fld2types.contains(prefix)) fld2types(prefix) = d
      if (!argFields.contains(prefix) && !isRet) argFields.add(prefix)
      if (!retFields.contains(prefix) && isRet) retFields.add(prefix)
      if (filter == null || d.equals(filter)) 
        return List(prefix)
      else if (d.isInstanceOf[BasicDatatype] && filter.isInstanceOf[BasicDatatype] && 
          d.asInstanceOf[BasicDatatype].isChildOf(filter.asInstanceOf[BasicDatatype]))
        return List(prefix)
      else 
        return List()
    }
    d.asInstanceOf[ComplexDatatype].fields.flatMap { case(f,t) =>      
      flatten(prefix + "." + f, t, filter, isRet)           
    }.toList
  }
  
  /**
   * Recursively enumerate all possible mappings of
   * abstract parameters to the concrete ones
   */
  private def enumerate(concElems: List[String]) : Unit = {
    val hd = concElems.head
    val hdTyp = fld2types(hd)
    val tl = concElems.tail
    var notEqualTo : String = ""
    
    if (partialConstraints.contains(hd)){
      val constraint = partialConstraints(hd)
      if (constraint.isInstanceOf[Equal]) {
         // Just set the param to the user-given value, and then continue          
        currMap(hd) = constraint.asInstanceOf[Equal].right          
        if (!tl.isEmpty) enumerate(tl) else saveMapping(currMap.toMap)
        currMap.remove(hd);     
        return
      } else if (constraint.isInstanceOf[NotEqual]) {
        notEqualTo = constraint.asInstanceOf[NotEqual].right  
      }
    }
      
      // list of potential abstract fields that may be mapped to hd, 
      // filtering by the type of hd
      val absElems = (abs.params.flatMap { case(p, t) => flatten(p, t, hdTyp) }.toList)  
      // constants that may be assigned to hd
      val constants = 
        (if (absElems.isEmpty) Store.valuesWithType(hdTyp) else List("none"))  
        
      val argElems = if (!retFields.contains(hd)) List() else {
        flatConcParams.filter { p => 
           argFields.contains(p) && fld2types(p) == fld2types(hd)   
        }
      }     
      
      val candidateElems = 
        (absElems.filter { e =>    
          (retFields.contains(e) && retFields.contains(hd)) ||
          (!retFields.contains(e) && !retFields.contains(hd))
        } ++ argElems  
          ++ constants).filter { e => e != notEqualTo }
  
      if (candidateElems.isEmpty) {
        // nothing that can be mapped to hd
        // just set it to "none" and continue
        currMap(hd) = "none"
        if (!tl.isEmpty) enumerate(tl) else saveMapping(currMap.toMap)        
      } else {
        candidateElems.foreach { e =>
          if (!currMap.exists(p => p._2.equals(e))) {
            currMap(hd) = e  
            if (!tl.isEmpty) enumerate(tl) else saveMapping(currMap.toMap)     
          } else { 
            
            // if "e" has already been assigned to another concrete elem
            // it can't be assigned to hd
            // so set hd to none   
            /*
            val condFuncs = candidateCondFuncs(currMap.toMap, retFields.contains(hd))
            if (!currMap.exists(p => p._2.startsWith(Impl.COND_FUNC_PREFIX)) && 
                !condFuncs.isEmpty) {
              (condFuncs //++ List("some")
                  ).foreach { f =>
                currMap(hd) = f
                if (!tl.isEmpty) enumerate(tl) else saveMapping(currMap.toMap)
              }
            } else {
              List("none").foreach{ f => 
                currMap(hd) = f
                if (!tl.isEmpty) enumerate(tl) else saveMapping(currMap.toMap)                        
              }
            }
            */
            currMap(hd) = "none"
            if (!tl.isEmpty) enumerate(tl) else saveMapping(currMap.toMap)            
          }         
        }
      }
    
      currMap.remove(hd)    
    return
  }
  
  private def mkCondExpr(concField: String, absField: String) : String = {
    Impl.COND_FUNC_PREFIX + "(" + concField + "," + absField + ")"      
  }
  
  private def candidateCondFuncs(m: Map[String,String], isRetField: Boolean) : List[String] = {
    ((m.filter { e => abs.isParam(e._2) && retFields.contains(e._1) == isRetField}.map { 
      case(concField, absField) => mkCondExpr(concField, absField) 
    }.toList) //++ List("none")
    ) 
  }
  
  /**
   * A mapping is valid iff every field of the abstract label
   * has been assigned to some concrete field
   */
  private def isValid(map: Map[String,String]) : Boolean = {
    return !(flatAbsParams.exists(p => !map.values.exists(_ == p))) 
  }
  
  /** 
   *  Check whether the mapping has already been generated
   *  If not, add it to the list of mappings
   */
  private def saveMapping(map: Map[String,String]) = {
    if (isValid(map) && !prevMaps.contains(map)) {
      prevMaps.add(map) 
      numMappings += 1  
 
      map.foreach { case (k, v) => 
        if (map.keySet.contains(v) && !partialConstraints.contains(k)) {
          val newMap = map + (v -> Impl.UNKNOWN_PREFIX)
          if (!prevMaps.contains(newMap)){
            prevMaps.add(newMap)
            numMappings += 1
          }
        }               
      }  
      
      map.foreach { case (k, v) =>
        if (!partialConstraints.contains(k)) {
         val condFuncs = candidateCondFuncs(map, retFields.contains(k))
         condFuncs.foreach { c => 
           val newMap = map + (k -> c)
           if (!prevMaps.contains(newMap)) {
             prevMaps.add(newMap)
             numMappings += 1
           }
         }
        }
      }           
    }    
  }
  
  /**
   * Enumerate all possible mappings from the abstract to the concrete label
   * Return the iterator to the complete mapping list
   */
  def enumerateMappings : Iterator[Map[String,String]] = {
    enumerate(flatConcParams)
    println("No. possible mappings from " + abs.name + " to " + conc.name + ": " + prevMaps.size)
    /*prevMaps.foreach { e =>
      println(e)
    }
    */
    prevMaps.iterator
  }
 
  def iter : Iterator[Map[String,String]] = {
    prevMaps.iterator
  }
 
  def getNumMappings : Int = {
    numMappings 
  }
  
  def addNotEqualConstraints(constraints: Map[String,String]) = {
    constraints.foreach{ case(left, right) =>
      if (!partialConstraints.contains(left))
        partialConstraints(left) = new NotEqual(left, right, fld2types(left))
    }
  }
  
  def addEqualConstraints(constraints: Map[String,String]) = {
    constraints.foreach{ case(left, right) =>
      if (!partialConstraints.contains(left))
        partialConstraints(left) = new Equal(left, right, fld2types(left))
    }
  }

  def isGivenConstraint(s : String) : Boolean = {
    partialConstraints.contains(s)
  }
  
  def isRetField(s: String) : Boolean = {
    retFields.contains(s)
  }
}