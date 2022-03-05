// Declare an effect `:input` with a single operation `ask`.
// We use `fun` instead of general `ctl` to ensure that all handlers
// will always resume (at most once) with the result.
effect fun ask() : string

fun hello() // TODO: Infer linear effect
  val name = ask()
  println("Hello " ++ name ++ ", " ++ ask())


pub fun main() 
  with fun ask() "there"    // infer linear effect & bypass monadic translation
  hello()