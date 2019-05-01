package constraints

import types.Datatype

class Conditional(val left : Equal, val right : Equal) extends Constraint {}