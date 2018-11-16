/**
 * Represent a value of a datatype
 */

package types

class Value(name: String, val typ: BasicDatatype) {
  typ.members += this;
}
