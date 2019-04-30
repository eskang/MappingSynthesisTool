/**
 * Event label definitions
 * 
 * Created by: Eunsuk Kang
 */
package types

class Label(val name: String, val params: Map[String,Datatype], val rets: Set[String], 
    val procID: Int, val rewrites: Map[String,String]=Map())  {
  // params: optional parameters of the label
  // rets: return parameters of the label
  
  def isRet(p: String) : Boolean = {
    return rets.contains(p);  
  }
    
  def rewrite(f: String) : String = {
    if (rewrites.isEmpty) f
    else rewrites.foldLeft(f){ case (s, (k,v)) => s.replace(k,v) }
  }
  
  def isParam(p : String) : Boolean = {
    params.keySet.contains(p)
  }
  
  def args : List[String] = {
    params.filter(f => !rets.contains(f._1)).keys.toList
  }
  
  def hasRet : Boolean = {
    return !(rets.isEmpty)
  }
}
