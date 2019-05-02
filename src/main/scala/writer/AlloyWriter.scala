package writer

import constraints.ImplConstraints
import types.Store
import constraints.Impl
import java.io._

class AlloyWriter(modelDir: String, outputDir: String, templateFile: String, outfilePrefix: String) {

  private def newline = "\n";
  private val template = {
    val f = scala.io.Source.fromFile(templateFile)
    val s = f.mkString
    f.close()
    s
  }
  
  private def line(s: String, indent: Int=0) : String = {
     "  "*indent + s + "\n" 
  }  
  
  def mappingPrefix(i : Int) : String = {
    // print the list of special variable constants
    val specialVals = Store.specialValList
    (if (!specialVals.isEmpty) 
    //  line ("abstract sig NONCE extends Data {}") + 
      line ("one sig " + (specialVals mkString ",") + " extends " + Store.SPECIAL_VAL_PREFIX + " {}") else "")      
  }
    
  def mappingSuffix(i : Int) : String = {
    ""   
    }
  
  def writeMapping(ms: Map[ImplConstraints, Map[String,String]], rewrite: Map[String,String]) = {
    val i = 0;
    Store.resetSpecialVals
    val body =   
      line("") +
      line("") +
      line("/**") +
      line("  *") +
      line("  * SYNTHESIZED MAPPING CONSTRAINTS", i) +
      line("  *") +
      line("  */") +
      line("pred mappingConstraints {", i) + 
       (ms.map(f =>            
        writeAbsToConcMap(i+1, f._1, f._2, rewrite)) mkString) +  
      line("}", i)  
    val s =  
      mappingPrefix(i) + 
      line("") + 
      body + 
      line("")
      mappingSuffix(i)  
      
    val pw = new PrintWriter(new File(modelDir + "/" + outfilePrefix + "_alloy.als"))
    pw.write("// Synthesized\n" +  template + s)
    pw.close
//    println(s)
  }
  
   private def writeAbsToConcMap(i: Int, impl: ImplConstraints, m: Map[String,String], rewrite: Map[String, String]) : String = { 
     line("// mapping from " + impl.abs.name + " to " + impl.conc.name, i) + 
     line("all a : " + impl.abs.name + " | let b = a { b in " + impl.conc.name, i) +
     (m.map{f => 
       var k = f._1
       rewrite.foreach { x => if (k.contains(x._1)) k = k.replace(x._1, x._2) }
       var v = f._2
       rewrite.foreach { x => if (v.contains(x._1)) v = v.replace(x._1, x._2) }
       
       if (v == "none"){ 
         line("no b." + k, i+1)
       } else if (v == "some") {
         line("some b." + k, i+1)
       } else if (Store.isVal(v)) {
         line("b." + k + " = " + v, i+1)
       } else if (v == Impl.UNKNOWN_PREFIX) {
         ""
       } else if (v.startsWith(Impl.COND_FUNC_PREFIX)) {
          val condConcField = Impl.extract(v)._1
          val condAbsField = Impl.extract(v)._2
          (Store.valuesWithType(impl.fld2types(condAbsField)).map { absVal =>
            line("(b." + condConcField + " = " + absVal + ") implies " + 
                "b." + k + " = " + Store.specialVal(absVal), i + 1)        
          } mkString)
       } else {
         line("b." + k + " = " + "a." + v, i+1)
       }
     } mkString) +
     line("}", i)
   }  
}