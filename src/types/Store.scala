/**
 * A helper object that keeps track of all labels, datatypes, and values
 * 
 * Created by: Eunsuk Kang
 */

package types

object Store {
  val datatypes = scala.collection.mutable.Map[String, Datatype]();
  val labels = scala.collection.mutable.Map[String, Label]();
  val values = scala.collection.mutable.Map[String, Value]();
  private var specialValCounter = -1;   
  private val SPECIAL_VAL_PREFIX = "NONCE"
  private val specialVals = scala.collection.mutable.Map[String,String]() 
  
  datatypes("mtype") = new BasicDatatype("mtype");
  
  def l(name: String) : Label = {
     return labels(name);   
  }
  
  def d(name: String) : Datatype = {
     return datatypes(name);   
  }
  
  def v(name: String): Value = {
    return values(name);
  }
  
  def isVal(name: String) : Boolean = {
    return values.contains(name)
  }
  
  def resetSpecialVals = {
    specialValCounter = -1;
    specialVals.clear()
  }

  def specialValList : List[String] = {
    specialVals.values.toList
  }
  
  def specialVal(v: String) : String = {
    if (specialVals.contains(v)) {
      specialVals(v)
    } else {
      specialValCounter += 1;      
      specialVals(v) = SPECIAL_VAL_PREFIX + specialValCounter
      specialVals(v)     
    }
  } 
  
  def valuesWithType(typ : Datatype) : List[String] = {
    val x = values.filter{ case (s,v) => v.typ == typ };
    x.keys.toList;
  }
  
  def mkComplexDatatype(name: String, fields: Map[String,Datatype]) : ComplexDatatype = {    
    if (datatypes.contains(name)) return datatypes(name).asInstanceOf[ComplexDatatype];
    val d = new ComplexDatatype(name, fields);
    datatypes(name) = d; 
    return d.asInstanceOf[ComplexDatatype];
  }
  
  def mkBasicDatatype(name: String,parent: BasicDatatype=null) : BasicDatatype = {
    if (datatypes.contains(name)) return datatypes(name).asInstanceOf[BasicDatatype];
    val d = new BasicDatatype(name,parent);
    datatypes(name) = d; 
    return d.asInstanceOf[BasicDatatype]; 
  }
  
  def mkLabel(name: String, params: Map[String,Datatype], rets: Set[String], procID: Int, rewrites: Map[String,String]=Map()) : Label = {
     if (labels.contains(name)) return labels(name);
    val l = new Label(name, params, rets, procID, rewrites);
    labels(name) = l; 
    return l;
  }
  
  def mkValue(name: String, typ: BasicDatatype) : Value = {
    if (values.contains(name)) return values(name);
    val v = new Value(name, typ);
    values(name) = v; 
    return v;  
  }
}