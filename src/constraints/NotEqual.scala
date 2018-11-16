package constraints

import types.Datatype

class NotEqual(val left:String, val right: String, val typ: Datatype) extends Constraint {}