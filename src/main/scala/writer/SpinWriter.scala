/**
 * Used to convert abstract representation of mappings
 * into a SPIN model
 * 
 * Created by: Eunsuk Kang
 */

package writer

import scala.io.Source
import constraints.ImplConstraints
import types.Label
import types.Store
import java.io._
import constraints.Impl
import types.BasicDatatype

class SpinWriter(modelDir: String, outputDir: String, templateFile: String, outfilePrefix: String) {
  
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
  
  private def attackerBehavior(i: Int) : String = {
    val attackerLabel = Store.l("port_attacker")
    val attackerID = attackerLabel.procID;
    line("atomic {", i) + 
    line(attackerLabel.name + "?req,sender_id;",i+1) +
    line("resps[" + attackerID + "].code = REDIRECT;", i+1) +
    line("resps[" + attackerID + "].set_cookie = none;", i+1) +
    line("resps[" + attackerID + "].redirectTo.origin = ORIGIN_MYAPP;", i+1) +
    line("attackerChoosePath(tmp);", i+1) +
    line("resps[" + attackerID + "].redirectTo.path = tmp;", i+1) +
    line("attackerChooseQuery(tmp);", i+1) + 
    line("resps[" + attackerID + "].redirectTo.query = tmp;", i+1) +
    line("resps[" + attackerID + "].redirectTo.query2 = none;", i+1) +
    line("resps[" + attackerID + "].resource.content = none;", i+1) +
    line("resp_set[" + attackerID + "] = 1;", i+1) +   
    line("_" + attackerLabel.name + "!req,sender_id;", i+1) +
    line("resp_ports[sender_id]?resp;", i+1) +
    line("_resp_ports[sender_id]!resp;", i+1)+
    line("}", i)
  }
  
  private def labelStr(i: Int, l: Label, isReceive: Boolean, isConc: Boolean, labelPrefix: String="") : String = {
    line(
        labelPrefix + 
        l.name + 
        (if (isReceive) "?" else "!") + 
        ((l.args ++ 
            (if (isConc) List("conc_sender_id") else List("sender_id"))
            ) mkString ",") +
        ";"
        ,
        i)  
  }
  
  def writeMapping(ms: Map[ImplConstraints, Map[String,String]]) = {
    val i = 0;
    Store.resetSpecialVals
    
    val body = 
      (ms.map(f =>        
        line("::",i+1) +        
        writeAbsToConcMap(i+2, f._1, f._2)) mkString) +
      writeConcToAbsMap(i+1, ms) + 
      line("::",i+1) + 
      attackerBehavior(i+2) + 
      line("od;",i)      
    val s =  
      mappingPrefix(i, "_") + 
      line("end:do",i) +
      body + 
      mappingSuffix(i)  
    
    val pw = new PrintWriter(new File(modelDir + "/" + outfilePrefix + "_liveness.pml"))
    pw.write("#define LIVENESS_PROP\n" + header + template + s)
    pw.close
    val pw2 = new PrintWriter(new File(modelDir + "/" + outfilePrefix + "_safety.pml"))
    pw2.write("#define SAFETY_PROP\n" + header + template + s)
    pw2.close    
  }
  
  private def writeRet(i: Int, chanName: String, isReceive: Boolean, label: Label, prefix: String="") : String = {
    line(
        prefix + 
        chanName + 
        (if (isReceive) "?" else "!") +
        (label.rets mkString ",") +
        ";",
        i)
  }
  
  private def writeArgs(i: Int, impl: ImplConstraints, m: Map[String,String]) : String = {
    val args = m.filter(f => !impl.isRetField(f._1))
    val nonCondStmts = (args.filter(f => !f._2.startsWith(Impl.COND_FUNC_PREFIX)).map(
        f => writePair(i, impl, f._1, f._2)        
          ) mkString)
    val condStmts = (args.filter(f => f._2.startsWith(Impl.COND_FUNC_PREFIX)).map (
        f => writePair(i, impl, f._1, f._2)        
          ) mkString)
    (nonCondStmts + condStmts)        
  } 
  
  private def writeCheckArgs(i: Int, impl : ImplConstraints, m: Map[String,String]) : String = {
    val args = m.filter(f => !impl.isRetField(f._1))
    val nonCondStmts = (args.filter(f => !f._2.startsWith(Impl.COND_FUNC_PREFIX)).map(
        f => writePairEnforce(i, impl, f._1, f._2)        
          ) mkString)
    val condStmts = (args.filter(f => f._2.startsWith(Impl.COND_FUNC_PREFIX)).map (
        f => writePairEnforce(i, impl, f._1, f._2)        
          ) mkString)
    (nonCondStmts + condStmts)  
  }
  
  private def writeEnforceArgs(i : Int, impl: ImplConstraints, m: Map[String,String]) : String = {
    val nonCondStmts = 
      (m.filter(f => !f._2.startsWith(Impl.COND_FUNC_PREFIX)).map { case (concField, v) => 
              if (impl.abs.isParam(v) && !impl.isRetField(v)) 
                line (v + " = " + concField + ";", i) 
              else if (v != "none" && !impl.isRetField(concField))                
                writePairEnforce(i, impl, concField, v)
              else  ""} mkString)             
    val condStmts = 
      (m.filter(f => f._2.startsWith(Impl.COND_FUNC_PREFIX)).map {
        f => writePairEnforce(i, impl, f._1, f._2)
      } mkString)
      nonCondStmts + condStmts             
  }
  
  private def writeResp(i: Int, impl: ImplConstraints, m: Map[String,String]) : String = {
    val rets = m.filter(f => impl.isRetField(f._1))
    val nonCondStmts = (rets.filter(f => !f._2.startsWith(Impl.COND_FUNC_PREFIX)).map(
        f => writePair(i, impl, f._1, f._2)        
          ) mkString)
    val condStmts = (rets.filter(f => f._2.startsWith(Impl.COND_FUNC_PREFIX)).map (
        f => writePair(i, impl, f._1, f._2)        
          ) mkString)
    (nonCondStmts + condStmts)      
  }  
  
  private def writeUnknownResp(i : Int, impl: ImplConstraints, m: Map[String,String]) : String = {
    val rets = m.filter(f => impl.isRetField(f._1))
    (rets.filter(f => f._2.startsWith(Impl.UNKNOWN_PREFIX)).map(
        f => line("choose(" + f._1 + ");", i)        
    ) mkString)
  }
  
  private def writePair(i:Int, impl: ImplConstraints, left: String, right:String) : String = {
    val concField = impl.conc.rewrite(left)   
    if (!(right.startsWith(Impl.COND_FUNC_PREFIX) || right.startsWith(Impl.UNKNOWN_PREFIX))) {
      // TODO: Hack! Need a better way to do this         
      line(concField + " = " + right + ";", i)
    } else if (right.startsWith(Impl.UNKNOWN_PREFIX)) {
      ""  
    } else {
      val condConcField = Impl.extract(right)._1
      val condAbsField = Impl.extract(right)._2
      line("if", i) +       
      (Store.valuesWithType(impl.fld2types(condAbsField)).map { absVal =>
        line(":: (" + impl.conc.rewrite(condConcField) + " == " + absVal + ") -> ", i + 1) + 
        line("  " + concField + " = " + Store.specialVal(absVal) + ";", i + 1)        
      } mkString) + 
      line("fi;", i)      
    }
  }
  
  private def writePairEnforce(i:Int, impl : ImplConstraints, left: String, right:String) : String = {
   
    if (!(right.startsWith(Impl.COND_FUNC_PREFIX) || right.startsWith(Impl.UNKNOWN_PREFIX))) {
      line(left + " == " + right + ";", i)
    } else if (right.startsWith(Impl.UNKNOWN_PREFIX)){
      line("choose( " + left + ");", i)
    } else {
      val condConcField = Impl.extract(right)._1
      val condAbsField = Impl.extract(right)._2
      line("if", i) +       
      (Store.valuesWithType(impl.fld2types(condAbsField)).map { absVal =>
        line(":: (" + condConcField + " == " + absVal + ") -> ", i + 1) + 
        line("  " + left + " == " + Store.specialVal(absVal) + ";", i + 1)        
      } mkString) + 
      line("fi;", i)  
    }    
  }
  
  private def header : String = {
    // print the list of special variable constants
    val specialVals = Store.specialValList
    (if (!specialVals.isEmpty) line ("mtype = {" + (specialVals mkString ",") + "};") else "") + 
    line("#define NUM_NONCES " + specialVals.size) + 
    newline
  }
  
  private def mappingPrefix(i: Int, prefix: String="") : String = {     
    val labels = Store.labels.keys.toList.sorted;
    val datatypes = Store.datatypes.keys.toList;
      
    newline +
    // print the list of temp variables used to store parameters
    {
      line (
        (Store.labels.values.toList.map {
          l => l.params
        }.flatten.map {
          case (n, d) => "hidden " + 
          (if (d.isInstanceOf[BasicDatatype] && d.asInstanceOf[BasicDatatype].hasParent) 
            d.asInstanceOf[BasicDatatype].parent.name else d.name) + 
          " " + n
        }.distinct mkString "; ") + ";",
        i)
    } +
    line("hidden byte sender_id;", i+1) +
    line("hidden byte conc_sender_id;", i+1) +   
    line("hidden mtype tmp;", i+1) +
    newline +
    line("proctype Mapping(", i) +
    line((labels.map(l => "chan " + l) mkString "; ") + ";", i+1) + 
    line((labels.map(l => "chan _" + l) mkString "; ") + ") {", i+1) +   
    newline    
  }
  
  private def mappingSuffix(i: Int) : String = {
    line("}", i);
  }
  
  private def writeConcToAbsMap(i: Int, ms: Map[ImplConstraints, Map[String,String]]) : String = {
    (ms.keys.map { ic => ic.conc }).map { c =>
      line("::", i) +
      line("atomic {",i+1) + 
      labelStr(i+2, c, true, true) +
      line("if", i+2) +  
      { ms.filter{ f => f._1.conc == c}.map { case (ic, m) =>
          line("::", i+2) +                      
           writeEnforceArgs(i+3, ic, m) +
           line("sender_id = conc_sender_id", i+3) + 
           labelStr(i+3, ic.abs, false, false, "_") +
           (if (ic.abs.hasRet) writeRet(i+3, "rets[sender_id]", true, ic.abs) else "") + 
           writeResp(i+3, ic, m) +
           line("resp_set[" + c.procID + "] = 1;", i+3)   
        } mkString
      } +
      line("fi;", i+2) +
      labelStr(i+2, c, false, true, "_") +
      (if (c.hasRet) writeRet(i+2, "resp_ports[sender_id]", true, c) else "") +  
      (if (c.hasRet) writeRet(i+2, "resp_ports[sender_id]", false, c, "_") else "") +
      line("}", i+1)
    } mkString
  } 
  
  private def writeComment(i: Int, comment: String) : String = {
    line("/* " + comment + " */", i)
  }
  
  private def writeAbsToConcMap(i: Int, impl: ImplConstraints, m: Map[String,String]) : String = { 
 
    line("atomic {",i) + 
    // list on proxy abstract port (label)
    labelStr(i+1, impl.abs, true, false) +
    // set values of arguments in the corresponding concrete message
    writeComment(i+1, "For optimization purposes only") +
    writeArgs(i+1, impl, m) +     
    writeComment(i+1, "End of optimization") +    
    //line("req[sender_id] = req;", i+1) +
    line("req_set[sender_id] = 1;", i+1) +    
    newline + 
    // listen on proxy concrete port
    labelStr(i+1, impl.conc, true, true) +
    line("sender_id == conc_sender_id;", i+1) + 
    line("req_set[sender_id] = 0;", i+1) +  
    newline +
    writeCheckArgs(i+1, impl, m) +
    newline +
    // send message on the actual abstract port
    labelStr(i+1, impl.abs, false, false, "_") +
    // wait for return value from the actual abstract label
    (if (impl.abs.hasRet) writeRet(i+1, "rets[sender_id]", true, impl.abs) else "") + 
    newline +
    // set values of the return paramters in the corresponding concrete message
    writeResp(i+1, impl, m) +
    //line("resp[sender_id] = resp;", i+1) +
    line("resp_set[" + impl.conc.procID + "] = 1;", i+1) +        
    newline +
    // send message on the actual concrete port
    labelStr(i+1, impl.conc, false, true, "_") + 
    // wait for return value from the actual concrete port
    (if (impl.conc.hasRet) 
      writeRet(i+1, "resp_ports[sender_id]", true, impl.conc) else "") +
    (if (impl.conc.hasRet) writeUnknownResp(i+1, impl, m)) + 
    newline +
    // send return message on the proxy abstract & concrete ports
    (if (impl.abs.hasRet) writeRet(i+1, "rets[sender_id]", false, impl.abs, "_") else "") +
    (if (impl.conc.hasRet) writeRet(i+1, "resp_ports[sender_id]", false, impl.conc, "_") else "") +    
    line("}", i)
  }
  
}
