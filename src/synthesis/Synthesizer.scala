/**
 * Main function for the synthesizer
 *
 * Created by: Eunsuk Kang
 */

package synthesis

import types._
import model.ModelHttp
import model.ModelHttp2
import model.ModelOAuth
import model.ModelOAuth1

case class Mismatch(msg: String) extends Exception(msg) {}

object Synthesizer extends App {

  /**
   * Comment out below to run synthesis on different models/with different verifiers
   */  
  runAlloy1
  //runAlloy2
  //runSpin1
  //runSpin2
  //runBothOAuth2

  // Synthesize a mapping from OAuth 2.0 to HTTP using Alloy as a verifier
  def runAlloy1 = {
    println("Initiating the synthesis process...")
    val start = System.currentTimeMillis
    // Construct the representations of the concrete and abstract models 
    ModelHttp.make
    ModelOAuth.make
    SynthesizerOAuthAlloy.init
    println("Number of possible mappings is " + SynthesizerOAuthAlloy.numMappings)
    println()
    // Enumerate and verify each mapping
    //SynthesizerOAuthAlloy.writeAllMappings(true)
    //SynthesizerOAuthAlloy.writeNextAlloy(true);
    //SynthesizerOAuthAlloy.writeUpto(1, true);
    SynthesizerOAuthAlloy.findSecureMapping
    val totalTime = System.currentTimeMillis - start
    println("Mapping exploration complete.")
    println("Total time elapsed " + totalTime / 1000.00 + " seconds")
    println("Total number of skipped mappings " + SynthesizerOAuthAlloy.numSkipped);
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
