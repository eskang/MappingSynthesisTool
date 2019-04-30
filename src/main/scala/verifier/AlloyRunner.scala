package verifier

import scala.collection.JavaConverters._
import writer.Logger

import edu.mit.csail.sdg.alloy4compiler.ast.Module
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4.A4Reporter
import edu.mit.csail.sdg.alloy4compiler.ast.Module
import edu.mit.csail.sdg.alloy4compiler.ast.Command
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution
import edu.mit.csail.sdg.alloy4compiler.ast.Func
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;

class AlloyRunner(modelPath: String) {

  private val SCOPE_BITWIDTH = 0;
  private val SCOPE_SEQ = -1;
  private val PREFIX_CHAR = "/"
  private val DEBUG = false
  
  def run(p: AlloyProp) : A4Solution = {  
    val rep = new A4Reporter()
    val world = CompUtil.parseEverything_fromFile(rep, null, modelPath)
    val cmd = mkCheckCmd(world, p)   
    val options = new A4Options()
//    options.solver = A4Options.SatSolver.MiniSatJNI
    options.solver = A4Options.SatSolver.SAT4J
    options.noOverflow = true

    if (DEBUG) {
      Logger.log("**********************************", Logger.VERBOSE)
      Logger.log("Solving a new formula...", Logger.VERBOSE)
      Logger.log(cmd.scope.toString(), Logger.VERBOSE)
      Logger.log(cmd.formula.toString(), Logger.VERBOSE)
    }

    val solvingStart = System.nanoTime()
    val sol = runCmd(rep, world, cmd, options)
    val solvingTime = System.nanoTime() - solvingStart

    if (DEBUG) {
      Logger.log("Solving completed: " + solvingTime / 1000000 + "ms", Logger.VERBOSE)
      Logger.log("", Logger.VERBOSE)
      if (sol.satisfiable()) {
        Logger.log("Instance found!", Logger.VERBOSE)
        Logger.log(sol.toString(), Logger.VERBOSE)
        sol.writeXML("alloy_example_output.xml");   
        // You can then visualize the XML file by calling this:
        //val viz = new VizGUI(false, "alloy_example_output.xml", null);
        //viz.loadXML("alloy_example_output.xml", true);
      } else {
        Logger.log("Unsatisfiable!", Logger.VERBOSE)
      }
      Logger.log("**********************************", Logger.VERBOSE)
    }  
    sol
  }

  private def funcWithName(world: Module, name: String): Func = {
    world.getAllReachableModules().asScala.foreach { m =>
      val funOpt = m.getAllFunc.asScala.find { f => f.label.contains(PREFIX_CHAR + name) }
      if (!funOpt.isEmpty) return funOpt.get
    }
    return null
  }

  private def sigWithName(world: Module, name: String): Sig = {
    val res = world.getAllReachableSigs().asScala.find { s => s.label.contains(PREFIX_CHAR + name) }
    if (res.nonEmpty)
      return res.get
    else
      return null
  }

  private def runCmd(rep: A4Reporter, world: Module, cmd: Command, options: A4Options) = {
    TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), cmd, options);
  }
  
  private def mkCheckCmd(world: Module, p: AlloyProp) = {
    val predProp = funcWithName(world, p.propName)
    val factExpr = world.getAllReachableFacts
    var cmd = new Command(false, p.defaultScope, SCOPE_BITWIDTH, SCOPE_SEQ, factExpr.and(predProp.call()))
    p.scopes.foreach { s =>
      val sig = sigWithName(world, s._1)
      val bound = s._2
      cmd = cmd.change(sig, false, bound)
    }
    cmd
  }
  
}