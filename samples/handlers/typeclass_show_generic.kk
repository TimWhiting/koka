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
  fun eshow(a: some<a> list<a>)
    a.map(eshow).join(", ")

val default_int = handler
  fun eshow(a: int)
    a.show

// //  // Needs to unify with effshow<list<int>> to being handled, but with the handlers body requires effshow<a> instantiated with int
val default_list = handler
  fun eshow(a: some<a> list<a>)
    a.map(eshow).join(", ")

// In koka main is special cased to be wrapped in a function which provides a handler for the console effect
// In implementing these default handlers we could also make console / exception / async effects
//  no longer special cased by the compiler. 
fun main(): <console> ()
  with default_int
  with default_list
  [0, 1, 2].eshow.println
