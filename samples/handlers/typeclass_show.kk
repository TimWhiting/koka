// Here is our effect type / typeclass definition
// it has only one generic parameter, and thus is associated with only a single value 
// (value polymorphism via an effect).
effect effshow<a>
  fun eshow(a: a): string

// This prints a pair, it takes in a value called tuple with a type (a, b), and returns ()
// it produces a console effect, as well as the effects eshow<a> and eshow<b>.
// 
// The effect acts as constraints to the parameters x and y, and requires default handlers
// for those types to be provided in order for the function to typecheck.
fun printPair((x, y): (a, b)): <console, effshow<a>, effshow<b>> ()
  val xs = eshow(x)
  val ys = eshow(y)
  println(xs ++ " ")

// This specifies a default instance of eshow for the effect eshow<int>
default handler
  fun eshow(a: int)
    a.show

// This specifies a default instance of eshow for the effect eshow<int>
default handler
  fun eshow(a: float64)
    a.show

// In Koka, main is currently special cased to be wrapped in a function which provides a handler for the console effect
// In implementing these default handlers we could also make console / exception / async effects
// no longer special cased by the compiler.
fun main(): <console> ()
  // Here we do the magic in the compiler, we insert the default handlers for the eshow<int> and eshow<float64> effect 
  // since their types are no longer polymorphic at this point of inference, 
  // and we have default instances for those types
  //
  // For default handlers we insert the effect handler 
  // at the first application where the effect type matches the handler type
  printPair((5,1.1))

// Alternatively you can override one of the implementations
// The compiler will propagate the handler type down so that printPair unifies with it before the default
// handler is inserted
// Similarly by propagating the effect type you can request that a parent function is in charge of the
// implementation of the typeclass / effect
fun othermain(): <console> ()
  with handler
    fun show(a: int)
      stringify(a) ++ "_hehe"
  // Now in order for the function to typecheck all it needs is the eshow<float64> effect 
  // which gets inserted by our default effect addition to the compiler
  printPair((5,1.1))
