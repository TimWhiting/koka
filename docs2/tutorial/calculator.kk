/* The complete source for the Koka Tutorial Calculator.
   You can run this directly with: koka calculator.kk
*/
module calculator

// begin imports
import std/num/float64
// end imports

// begin exp
type exp
  Val( n : int )
  Add( l : exp, r : exp )
  Sub( l : exp, r : exp )
  Mul( l : exp, r : exp )
  Div( l : exp, r : exp )
  Var( name : string )
// end exp

// begin effects
effect calculator
  fun lookup( name : string ) : maybe<int>
  final ctl raise( msg : string ) : a
// end effects

// begin eval
fun eval( e : exp ) : <calculator> int
  match e
    Val(n)    -> n
    Add(l, r) -> eval(l) + eval(r)
    Sub(l, r) -> eval(l) - eval(r)
    Mul(l, r) -> eval(l) * eval(r)
    Div(l, r) ->
      val rv = eval(r)
      if rv == 0 then raise("division by zero")
      else eval(l) / rv
    Var(n) ->
      match lookup(n)
        Just(v) -> v
        Nothing -> raise("undefined variable: " ++ n)
// end eval

// begin run-calc
fun run-calc( v-list : list<(string,int)>, e : exp ) : console int
  with handler
    fun lookup(name)
      v-list.find(fn(kv) kv.fst == name).map(snd)
    final ctl raise(msg)
      println("Runtime Error: " ++ msg)
      0 // Return 0 as a fallback
  eval(e)
// end run-calc

// begin repl
fun repl() : <console,calculator,div> ()
  println("\nEnter expression (or 'quit'):")
  // In a real app, you'd parse a string here.
  // For this exercise, we simulation a division-by-zero error.
  val expr = Div(Val(10), Val(0))
  println("Result: " ++ eval(expr).show)

fun main()
  with handler
    fun lookup(_) Nothing // No variables for now
    final ctl raise(msg)
      println("Oops! " ++ msg)
      // RESTART the entire repl!
      main()
  repl()
// end repl
