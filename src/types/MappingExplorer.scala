package types

import constraints.ImplConstraints
import constraints.Impl
import mapping.Mapping
import writer.SpinWriter
import java.io._
import scala.sys.process._
import scala.collection.immutable.IndexedSeq.Impl
import writer.AlloyWriter
import verifier.AlloyRunner
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution
import verifier.PropMappingSafe
import verifier.PropMappingLive1
import verifier.PropMappingLive2


abstract class MappingExplorer {
    
  protected val OPTIMIZE = false
  protected val MINIMIZE = false
  protected val NOT_VERIFIED = -1
  protected val MAPPING_OK = 0 
  protected val SAFETY_VIOLATED = 1
  protected val LIVENESS_VIOLATED = 2   
  protected val SKIPPED = 3
  
  protected var reducing = false
  
  protected var numMapping = 0
  protected var correctMappingFound = false  
  protected val skipConstraints = scala.collection.mutable.Set[Map[ImplConstraints,Map[String,String]]]() 
  
  var numSkipped = 0 
  var relaxNumCalls = List[Int]();
  var relaxTime = List[Long]();
  var numActualMapping = 0
  var minNumCalls : Int = 0
  var minTime : Long = 0
  var numValidMappings = 0
  
  var lastResult : Int = 0
  
  def mapping: Mapping
  def DIR_MODEL : String
  def DIR_GENERATED : String
  def PATH_TEMPLATE : String
  def PREFIX_GENERATED : String 
  def MODE : String
  private val PATH_SPIN = "/usr/local/bin/spin" 
  
  def init = { 
    mapping.genMapings();
    Process(Seq("/bin/sh","-c","rm " + DIR_GENERATED + "*.*")).!    
    Process(Seq("/bin/sh","-c","rm " + DIR_GENERATED + "permissive/*.*")).!     
    Process(Seq("/bin/sh","-c","rm " + DIR_GENERATED + "restrictive/*.*")).! 
    Process(Seq("/bin/sh","-c","rm " + DIR_GENERATED + "violated/*.*")).!
    Process(Seq("/bin/sh","-c","rm " + DIR_GENERATED + "safe/*.*")).! 
  }
     
  def writeAllMappings(verify:Boolean=false) = {
    while(writeNext(verify)) {}
    printStats
  }
   
  def printStats() = {
      println("Total number of mappings: " + numMappings)      
      println("A correct mapping found after: " + numMapping + " iterations")
      println("Total number of skipped mappings: " + numSkipped);
      
      if (!relaxNumCalls.isEmpty) {
        println("Actual number of mappings explored: " + (numMapping - (relaxNumCalls.sum + minNumCalls)))
        println("Number of verifier calls during relaxation: " + relaxNumCalls.sum)
        println("Average of verifier calls during relaxation: " + relaxNumCalls.sum/relaxNumCalls.size)
        println("Total relaxation time: " + relaxTime.sum/1000.00)            
        println("Average relaxation time: " + (relaxTime.sum/relaxTime.size)/1000.00)      
      }
      println("Minimization time: " + minTime/1000.00)            
      println("Number of verifier calls during minimization time: " + minNumCalls)
      println("Number of valid mappings found: " + numValidMappings)
  }
  
  def findSecureMapping : Boolean = {
    while(writeNext(true) && !correctMappingFound) {}
    if (correctMappingFound) {
      correctMappingFound = false
      printStats
      return true
    } else {
      return false
    }
  }
  
  def writeUpto(n: Int, verify:Boolean=false) = {
     var i=0
     while (i < n && i < numMappings) {
       writeNext(verify)
       i += 1
     }
  }
  
  private def mkReport(out: String) : Map[String,String] = {
    out.split("\n").map { x =>
        val l = x.split(",")
        l(0) -> l(1)
      }.toMap  
  }
      
  def numMappings : Int = {
    mapping.numMappings
  }
  
  def relaxMapping(mapping: Map[ImplConstraints, Map[String,String]], status : Int) : Map[ImplConstraints, Map[String,String]] = { 
    var newMapping = mapping
    var badConstraints = mapping
    val start = System.currentTimeMillis
    var count = 0;
    
    reducing = true
    
    println("************")
    println("Relaxing constraint set")
    
    val mappingPP = (mapping.map { case (impl, m) =>
      (impl.abs.name + " to " + impl.conc.name + "\n") +  
      //pp(m)
      m + "\n"
    } mkString)    
    println(mappingPP)
    
    var currTime = (System.currentTimeMillis() - start)/1000.00
    
    mapping.foreach { case(impl,m) =>  
      m.foreach { case (k,v) =>
        if (!impl.isGivenConstraint(k)) {      
          val tempMapping = newMapping + (impl -> (newMapping(impl) + (k -> Impl.UNKNOWN_PREFIX)))
          val res = writeMapping(tempMapping, true)
          count += 1;
          currTime = (System.currentTimeMillis() - start)/1000.00
          println("Relaxation time stamp: " + currTime)
          if (res == MAPPING_OK && MINIMIZE) {
            minimizeMapping(tempMapping, res)
            return badConstraints.toMap
          } else if (res == status) { 
            newMapping = tempMapping
            badConstraints = badConstraints + (impl -> (badConstraints(impl) - k))
          } 
        }
      }
    } 

    val totalTime = System.currentTimeMillis - start
      
    reducing = false    
    
    println(badConstraints);    
    println("Relaxation complete in " + totalTime/1000.00)
    relaxNumCalls = count :: relaxNumCalls
    relaxTime = totalTime :: relaxTime
    println("************")     
    badConstraints.toMap;
  }  
  
  // returns true if there's at least one skip constraint group that matches "m"
  def checkSkipConstraints(m : Map[ImplConstraints, Map[String,String]]) : Boolean = {    
    skipConstraints.exists { x =>
      x.filter(e => !e._2.isEmpty).forall { case (impl, m2) =>
        !(m2.exists { case(k, v) => m(impl)(k) != v })
      }
    }
  }
  
  protected def writeToPath(path: String, content: String) = {
     val pw = new PrintWriter(new File(path))
     pw.write(content)
     pw.close 
  }
  
  def writeNext(verify:Boolean=false) : Boolean = {
    val hasNext = mapping.next()       
    val currMapping = mapping.currMapping
    
    if (!checkSkipConstraints(currMapping)) {
      val result = writeMapping(currMapping, verify)
      lastResult = result
      if (OPTIMIZE && 
           (result == LIVENESS_VIOLATED 
               //|| result == SAFETY_VIOLATED
               )) { 
        val newSkipSet = relaxMapping(currMapping, result)
        if (newSkipSet.exists(p => !p._2.isEmpty))
          skipConstraints += newSkipSet   
      }
      if (result == MAPPING_OK && MINIMIZE) {
        minimizeMapping(currMapping, result)
      }      
    } else {
      //println("Skipping " + numMapping + "th mapping!")
      numSkipped += 1
      println("SKIPPED: " + numSkipped)
      lastResult = SKIPPED
    }     
    hasNext
  }
  
  def writeMapping(currMapping: Map[ImplConstraints, Map[String,String]], verify:Boolean = false) : Int = {
    if (MODE == "ALLOY") {
      writeAlloyMapping(currMapping, verify)
    } else if (MODE == "SPIN") {
      writeSpinMapping(currMapping, verify)
    } else {
      NOT_VERIFIED
    }
  }
  
  def writeAlloyMapping(currMapping: Map[ImplConstraints, Map[String,String]], verify:Boolean = false) : Int = {
    val writer = new AlloyWriter(DIR_MODEL,DIR_GENERATED,PATH_TEMPLATE,PREFIX_GENERATED)
    writer.writeMapping(currMapping, 
        collection.immutable.HashMap("req." -> "", "resp." -> "resp_", 
            "redirectTo." -> "redirectTo_", "url." -> "url_"))
    var result = NOT_VERIFIED
    val mappingPP = currMapping.map { case (impl, m) =>
      (impl.abs.name + " to " + impl.conc.name + "\n") +  
      pp(m)      
    } mkString
    
    println("Mode: Alloy");
    if (verify) {
      val runner = new AlloyRunner(DIR_MODEL + PREFIX_GENERATED + "_alloy.als")   
      println("Checking liveness for " + numMapping + "-th mapping");      
      val sol1 = runner.run(PropMappingLive1)
      val sol2 = runner.run(PropMappingLive2)
      if (!(sol1.satisfiable && sol2.satisfiable)) { 
        println("Livness violated")
        result = LIVENESS_VIOLATED
        writeToPath(DIR_GENERATED + "restrictive/gen_mapping" + numMapping + ".out", mappingPP)             
      } else {
        println("Livness OK")
        writeToPath(DIR_GENERATED + "permissive/gen_mapping" + numMapping + ".out", mappingPP)
        println("Checking safety for " + numMapping + "-th mapping");     
        val sol = runner.run(PropMappingSafe)
        if (sol.satisfiable) {
          println("Safety violated")   
          result = SAFETY_VIOLATED
          writeToPath(DIR_GENERATED + "violated/gen_mapping" + numMapping + ".out", mappingPP)
        } else {
          println("Safety OK!")  
          //if (reducing == false) 
          correctMappingFound = true
          numValidMappings += 1
          result = MAPPING_OK
          writeToPath(DIR_GENERATED + "safe/gen_mapping" + numMapping + ".out", mappingPP)          
        }
      }
    }
        
    ("/bin/cp " + DIR_MODEL + "gen_mapping_alloy.als " + DIR_GENERATED + "gen_mapping" + numMapping + ".als").!
    println("Mapping and verification results written as gen_mapping" + numMapping + "(.als|.out)");         
    println()
    
    numMapping += 1 
    result
  }
    
  def writeSpinMapping(currMapping: Map[ImplConstraints, Map[String,String]], verify:Boolean = false) : Int = {    
    val writer = new SpinWriter(DIR_MODEL,DIR_GENERATED,PATH_TEMPLATE,PREFIX_GENERATED);
    writer.writeMapping(currMapping)
    var result = NOT_VERIFIED
    
    val mappingPP = currMapping.map { case (impl, m) =>
      (impl.abs.name + " to " + impl.conc.name + "\n") +  
      pp(m)
    } mkString    
        
    println("Mode: Spin");   
    if (verify) {
      (PATH_SPIN + " -a " + DIR_MODEL + PREFIX_GENERATED + "_liveness.pml").!
      "/usr/bin/cc -O2 -DSAFETY -o pan pan.c".!
      println("Checking liveness for " + numMapping + "-th mapping");
      val out: String = ("./pan -E " #| "util/parsepan -l --delimiter c" !!)      
      val report = mkReport(out)
      
      writeToPath(DIR_GENERATED + "gen_mapping" + numMapping + ".out", mappingPP + out)           
      if (report("errors") == "1") {
        println("Liveness OK!")        
        writeToPath(DIR_GENERATED + "permissive/gen_mapping" + numMapping + ".out", mappingPP + out)
        (PATH_SPIN + " -a " + DIR_MODEL + PREFIX_GENERATED + "_safety.pml").!       
        "/usr/bin/cc -O2 -DSAFETY -o pan pan.c".!
        println("Checking safety for " + numMapping + "-th mapping");     
        val out2: String = ("./pan -E " #| "util/parsepan -l --delimiter c" !!)      
        val report2 = mkReport(out2)
        
        if (report2("errors") == "1") {
          println("Safety violated")   
          result = SAFETY_VIOLATED
          writeToPath(DIR_GENERATED + "violated/gen_mapping" + numMapping + ".out", mappingPP + out2)
        } else {
          println("Safety OK!")  
          correctMappingFound = true
          result = MAPPING_OK
          writeToPath(DIR_GENERATED + "safe/gen_mapping" + numMapping + ".out", mappingPP + out2)          
        }        
      } else {
        println("Livness violated")
        result = LIVENESS_VIOLATED
        writeToPath(DIR_GENERATED + "restrictive/gen_mapping" + numMapping + ".out", mappingPP + out)          
      }
    }
    
    ("/bin/cp " + DIR_MODEL + "gen_mapping_safety.pml " + DIR_GENERATED + "gen_mapping" + numMapping + ".pml").!
    println("Mapping and verification results written as gen_mapping" + numMapping + "(.pml|.out)");         
    println()
    
    numMapping += 1 
    result
  }
  
  def minimizeMapping(mapping: Map[ImplConstraints, Map[String,String]], status : Int) : Map[ImplConstraints, Map[String,String]] = {
    var newMapping = mapping   
    val start = System.currentTimeMillis
    var count = 0;
    
    println("************")
    println("Minimizing constraint set")
    
    val mappingPP = (mapping.map { case (impl, m) =>
      (impl.abs.name + " to " + impl.conc.name + "\n") +  
      pp(m)
    } mkString)    
    println(mappingPP)
    
    mapping.foreach { case(impl,m) =>  
      m.foreach { case (k,v) =>
        if (!impl.isGivenConstraint(k)) {      
          val tempMapping = newMapping + (impl -> (newMapping(impl) + (k -> Impl.UNKNOWN_PREFIX)))
          val res = writeMapping(tempMapping, true)
          count += 1;
          val currTime = (System.currentTimeMillis() - start)/1000.00
          println("Minimization time stamp: " + currTime)
          if (res == status) newMapping = tempMapping         
        }
      }
    } 
    val totalTime = System.currentTimeMillis - start
       
    println("Minimization complete in " + totalTime/1000.00)
    minTime = totalTime;
    minNumCalls = count;
    println("************")     
    newMapping.toMap
  }  
        
  /**
   * Pretty-print a mapping
   * For debugging purpose
   */
  def pp(map: Map[String,String]) = {
    val s = 
    ("http://" + map("req.url.origin") + ".com/" + map("req.url.path") + "?" + map("req.url.query") + "&" + map("req.url.query2") + "\n") +
    ("  cookie:" + map("req.cookie") + " body:" + map("req.body") + "\n") +    
    ("response status:" + map("resp.code") + " set_cookie:" + map("resp.set_cookie") + "\n") + 
    (if (map("resp.code") == "REDIRECT") 
      ("  redirectTo: http://" + map("resp.redirectTo.origin") + ".com/" + map("resp.redirectTo.path") + "?" + map("resp.redirectTo.query") + "&" + map("resp.redirectTo.query2") + "\n") 
      else "" )+     
    ("  resource: " + map("resp.resource.content") + "\n") +
    ("\n")
    
    s.replace("none", "_")
  }
  
}