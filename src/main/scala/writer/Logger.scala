/**
 * A simple logging component.
 */
package writer

object Logger {
  
  val MINIMAL = 0
  val MEDIUM = 1
  val VERBOSE = 2 
  
  private var verbosity = VERBOSE
  
  def setVerbosity(v : Int) = { 
    verbosity = v;
  }
  
  def log(s:String, v : Int) = {
    if (verbosity >= v) println(s)
  }
  
}