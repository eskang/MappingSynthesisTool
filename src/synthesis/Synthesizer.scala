/**
 * Main function for the synthesizer
 *
 * Created by: Eunsuk Kang
 */

package synthesis

import scala.reflect.runtime.currentMirror
import scala.tools.reflect.ToolBox
import io.Source

import mapping._
import types._
import writer.Logger
import model.ModelHttp
import model.ModelHttp2
import model.ModelOAuth
import model.ModelOAuth1

case class Mismatch(msg: String) extends Exception(msg) {}

object Synthesizer extends App {

  if (args.length < 4) {
    println("Error: Missing parameters.")
    println("Usage: mappingSynthesizer model_1 model_2 partial_mapping config")
    println("Please see README.txt for more details.")
    System.exit(1)
  }

  val toolbox = currentMirror.mkToolBox()
  val modelFile1 = args(0)
  val modelFile2 = args(1)
  val partialMappingFile = args(2)
  val configFile = args(3)

  parseEvalModel(modelFile1)
  parseEvalModel(modelFile2)
  parseMapping(partialMappingFile)
  val mapping = MappingFactory.getMapping
  println("Num mappings:" + mapping.numMappings)
  parseEvalConfig(configFile)

  val mappingExplorer = new MappingExplorer(mapping)

  Logger.log("Initiating the synthesis process...", Logger.MINIMAL)
  val start = System.currentTimeMillis
  // Construct the representations of the concrete and abstract models
  mappingExplorer.init
  Logger.log("Number of possible mapping candidates to search is " + mapping.numMappings, Logger.MINIMAL)
  Logger.log("", Logger.MINIMAL)
  // Enumerate and verify each mapping
  mappingExplorer.findSecureMapping
  val totalTime = System.currentTimeMillis - start
  Logger.log("Mapping exploration complete.", Logger.MINIMAL)
  Logger.log("Total time elapsed " + totalTime / 1000.00 + " seconds", Logger.MEDIUM)

  /**
   * Comment out below to run synthesis on different models/with different verifiers
   */
  //runTest
  //runAlloy1
  //runAlloy2
  //runSpin1
  //runSpin2
  //runBothOAuth2

  def parseEvalModel(modelFile: String) = {
    val fileContents = Source.fromFile(modelFile).getLines.mkString("\n")
    val tree = toolbox.parse("import types._; " + fileContents)
    toolbox.eval(tree)
  }

  def parseEvalConfig(configFile: String) = {
    val fileContents = Source.fromFile(configFile).getLines.mkString("\n")
    val tree = toolbox.parse("import types._; " + fileContents)
    toolbox.eval(tree)
  }

  def parseMapping(mappingFile: String) {
    val fileContents = Source.fromFile(mappingFile).getLines.mkString("\n")
    val tree = toolbox.parse(
      "import constraints.ImplConstraints; import mapping._; import types._; " +
        fileContents)
    toolbox.eval(tree)
  }

  def runTest = {
    println(Store.numLabels)
    val fileContents = Source.fromFile("test.scala").getLines.mkString("\n")
    val tree = toolbox.parse("import types._; " + fileContents)
    //val compiledCode = toolbox.compile(tree)
    val e = toolbox.eval(tree)

    /*
    val obj = compiledCode().asInstanceOf[Object]
    val clazz = obj.getClass
    println(clazz.getDeclaredFields())
    */

    println(Store.numLabels)
    println(Store.numDatatypes)
    println("done")
  }

  // Synthesize a mapping from OAuth 2.0 to HTTP using Alloy as a verifier
  def runAlloy1 = {
    Logger.log("Initiating the synthesis process...", Logger.MINIMAL)
    val start = System.currentTimeMillis
    // Construct the representations of the concrete and abstract models
    ModelHttp.make
    ModelOAuth.make
    SynthesizerOAuthAlloy.init
    Logger.log("Number of possible mapping candidates to search is " + SynthesizerOAuthAlloy.numMappings, Logger.MINIMAL)
    Logger.log("", Logger.MEDIUM)
    // Enumerate and verify each mapping
    //SynthesizerOAuthAlloy.writeAllMappings(true)
    //SynthesizerOAuthAlloy.writeNextAlloy(true);
    //SynthesizerOAuthAlloy.writeUpto(1, true);
    SynthesizerOAuthAlloy.findSecureMapping
    val totalTime = System.currentTimeMillis - start
    Logger.log("Mapping exploration complete.", Logger.MINIMAL)
    Logger.log("Total time elapsed " + totalTime / 1000.00 + " seconds", Logger.MEDIUM)
    //  Logger.log("Total number of skipped mappings " + SynthesizerOAuthAlloy.numSkipped, Logger.MEDIUM);
  }

  // Synthesize a mapping from OAuth 1.0 to HTTP using Alloy as a verifier
  def runAlloy2 = {
    println("Initiating the synthesis process...")
    val start = System.currentTimeMillis
    // Construct the representations of the concrete and abstract models
    ModelHttp2.make
    ModelOAuth1.make
    SynthesizerOAuth1Alloy.init
    println("Number of possible mappings is " + SynthesizerOAuth1Alloy.numMappings)
    println()
    // Enumerate and verify each mapping
    //SynthesizerOAuth1Alloy.writeAllMappings(true)
    //SynthesizerOAuth1Alloy.writeNextAlloy(true);
    //SynthesizerOAuth1Alloy.writeUpto(1, true);
    SynthesizerOAuth1Alloy.findSecureMapping
    val totalTime = System.currentTimeMillis - start
    println("Mapping exploration complete.")
    println("Total time elapsed " + totalTime / 1000.00 + " seconds")
  }

  // Synthesize a mapping from OAuth 2.0 to HTTP using Spin as a verifier
  def runSpin1 = {
    println("Initiating the synthesis process...")
    val start = System.currentTimeMillis
    // Construct the representations of the concrete and abstract models
    ModelHttp.make
    ModelOAuth.make
    SynthesizerOAuthSpin.init
    println("Number of possible mappings is " + SynthesizerOAuthSpin.numMappings)
    println()
    // Enumerate and verify each mapping
    //SynthesizerOAuthSpin.writeAllMappings(true)
    SynthesizerOAuthSpin.writeNext(true);
    //SynthesizerOAuthSpin.writeUpto(10, true);
    //SynthesizerOAuthSpin.findSecureMapping
    val totalTime = System.currentTimeMillis - start
    println("Mapping exploration complete.")
    println("Total time elapsed " + totalTime / 1000.00 + " seconds")
    println("Total number of skipped mappigns " + SynthesizerOAuthSpin.numSkipped);
  }

  // Synthesize a mapping from OAuth 1.0 to HTTP using Spin as a verifier
  def runSpin2 = {
    println("Initiating the synthesis process...")
    val start = System.currentTimeMillis
    // Construct the representations of the concrete and abstract models
    ModelHttp2.make
    ModelOAuth1.make
    SynthesizerOAuth1Spin.init
    println("Number of possible mappings is " + SynthesizerOAuth1Spin.numMappings)
    println()
    // Enumerate and verify each mapping
    //SynthesizerOAuth1Spin.writeAllMappings(true)
    SynthesizerOAuth1Spin.writeNext(true);
    //SynthesizerOAuth1Spin.writeUpto(10, true);
    //SynthesizerOAuth1Spin.findSecureMapping
    val totalTime = System.currentTimeMillis - start
    println("Mapping exploration complete.")
    println("Total time elapsed " + totalTime / 1000.00 + " seconds")
    println("Total number of skipped mappigns " + SynthesizerOAuth1Spin.numSkipped);
  }

  // Run both Spin and Alloy-based synthesizers on OAuth 2
  def runBothOAuth2 = {
    val N = 108;
    println("Initiating the synthesis process...")
    val start = System.currentTimeMillis
    ModelHttp.make
    ModelOAuth.make
    SynthesizerOAuthSpin.init
    SynthesizerOAuthAlloy.init
    println("Number of possible Spin mappings is " + SynthesizerOAuthSpin.numMappings)
    println("Number of possible OAuth mappings is " + SynthesizerOAuthAlloy.numMappings)

    try {
      for (i <- 1 to N) {
        SynthesizerOAuthSpin.writeNext(true)
        SynthesizerOAuthAlloy.writeNext(true)
        if (SynthesizerOAuthSpin.lastResult != SynthesizerOAuthAlloy.lastResult)
          throw Mismatch(String.valueOf(i))
      }
    } catch {
      case Mismatch(msg) => println("Mismatch between Spin and OAuth: " + msg + "th mapping!")
    }

    println()
    val totalTime = System.currentTimeMillis - start
    println("Mapping exploration complete.")
    println("Total time elapsed " + totalTime / 1000.00 + " seconds")
  }

}
