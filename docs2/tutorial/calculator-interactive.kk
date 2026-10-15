/* Advanced Interactive Calculator with Resumption.
   This version allows the user to FIX errors (like missing variables)
   interactively without aborting the entire evaluation.
   It also includes actual parsing from a string.
*/
module calculator-interactive

// begin imports
import std/num/float64
import std/text/parse
import std/os/readline
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
  ctl lookup( name : string ) : int
  ctl raise( msg : string ) : int
// end effects

// begin parser
fun pexp() : <parse,div> exp
  var e := pterm()
  many {
    val op = one-of("+-")
    val r = pterm()
    e := (if op == '+' then Add(e,r) else Sub(e,r))
  }
  e

fun pterm() : <parse,div> exp
  var e := pfactor()
  many {
    val op = one-of("*/")
    val r = pfactor()
    e := (if op == '*' then Mul(e,r) else Div(e,r))
  }
  e

fun pfactor() : <parse,div> exp
  choose([
    fn() {
      whitespace0()
      val i = pint()
      whitespace0()
      Val(i)
    },
    { // we can avoid the fn() here
      whitespace0()
      val name = chars-are("letter", is-alpha).string
      whitespace0()
      Var(name)
    },
    {
      whitespace0()
      char('(')
      val e = pexp()
      char(')')
      whitespace0()
      e
    }
  ])
// end parser

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
    Var(n) -> lookup(n)
// end eval

// begin interactive
fun read-int-loop(prompt : string) : <console,exn,div> int
  print(prompt)
  val input = readline()
  match input.parse-int
    Just(i) -> i
    Nothing ->
      println("Invalid number: " ++ input)
      read-int-loop(prompt)

fun interactive-calc( e : exp ) : <console,div,exn> int
  var vars := [("pi", 3)]
  
  with handler
    ctl lookup(name)
      match vars.find(fn(kv) kv.fst == name)
        Just(v) -> resume(v.snd)
        Nothing -> 
          println("Variable '" ++ name ++ "' is missing.")
          val input = read-int-loop("Enter value for '" ++ name ++ "': ")
          vars := Cons((name,input), vars)
          resume(input)

    ctl raise(msg)
      println("Error: " ++ msg)
      val input = read-int-loop("Enter result to use instead: ")
      resume(input)

  eval(e)

fun main()
  while { True }
    with handler
      ctl lookup(_) resume(0)
      ctl raise(msg)
        println("Oops! " ++ msg)
        resume(0)
    
    println("\nEnter expression (or 'quit'):")
    val input = readline()
    if input == "quit" then return ()
    
    match input.slice.parse(pexp)
      ParseOk(expr, _)  -> println("Result: " ++ interactive-calc(expr).show)
      ParseError(msg,_) -> println("Parse Error: " ++ msg)
// end interactive
