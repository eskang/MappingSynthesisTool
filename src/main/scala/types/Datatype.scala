package types

/**
 * Datatype definitions
 * 
 * Created by: Eunsuk Kang
 */
abstract class Datatype(val name: String) {}

class BasicDatatype(name: String, val parent: BasicDatatype=null) extends Datatype(name) {
  val members = scala.collection.mutable.Set[Value]();
  val children = scala.collection.mutable.Set[BasicDatatype]()
  
  if (parent != null) parent.addChild(this)
  
  def hasParent : Boolean = {
    (parent != null)
  }
  
  def isChildOf(p : BasicDatatype) = {
    p.children.contains(this)
  }
  
  def addChild(c: BasicDatatype) = {
    children.add(c)
  }
}

class ComplexDatatype(name: String, val fields: Map[String,Datatype]) extends Datatype(name) {
}
