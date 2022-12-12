// Here is our effect type / typeclass definition
// it has only one generic parameter, and thus is associated with only a single value 
// (value polymorphism via an effect).
effect effshow<a>
  fun eshow(a: a): string;

// This specifies a default instance of eshow for the effect eshow<int>
default handler
  fun eshow(a: int)
    a.show

// This specifies a default instance of eshow for the effect eshow<int>
default handler
  fun eshow(a: float64)
    a.show

// In koka main is special cased to be wrapped in a function which provides a handler for the console effect
// In implementing these default handlers we could also make console / exception / async effects
//  no longer special cased by the compiler. 
fun main(): <console> ()
  // val x = 0.eshow
  // x.println
  // println(eshow(3))
  // 0.eshow.println
  1.1.eshow.println