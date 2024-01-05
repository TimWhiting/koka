struct astruct
  field1: int
  field2: string
  field3: bool

fun test1()
  Astruct(1, "hello", True).copy2(?field2="world")
  "Done".println

// Rewrite copy as the following:
// Astruct(1, "hello", True).copy2(?field2="world")
// => 
// val @tmp = Astruct(1, "hello", True)
// val field1 = @tmp.field1
// val field3 = @tmp.field3
// @tmp.copy2(?field2="world")

inline fun copy2(a: astruct, ?field1, ?field2, ?field3): astruct
  // (a is still passed in to help disambiguate as well as since a's memory can be reused)
  Astruct(implicit/field1, implicit/field2, implicit/field3)
