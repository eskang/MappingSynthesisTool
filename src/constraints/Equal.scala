/**
 * An equality constraint between parameters of two labels 
 * 
 * Created by: Eunsuk KAng
 */
package constraints

import types.Datatype

class Equal(val left:String, val right: String, val typ: Datatype) extends Constraint {}
