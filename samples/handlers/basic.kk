/* Basic effect handler examples
   Prerequisites:
   - learn/basic
   - learn/var
   - learn/with
*/
module basic

import std/num/random


// --------------------------------------------------------
//  Input
//  Essentially models dynamically bound state
// --------------------------------------------------------

// Declare an effect `:input` with a single operation `ask`.
// We use `fun` instead of general `ctl` to ensure that all handlers
// will always resume (at most once) with the result.
effect fun ask() : string

fun hello()
  val name = ask()
  println("Hello " ++ name ++ ", " ++ ask())  // "Hello <ask>, <ask>"


pub fun example2()
  with fun ask() "there"    // a `fun` operation resumes implicitly with its result
  hello()



// --------------------------------------------------------
//  Exceptions
// --------------------------------------------------------

// An effect `:raise` with a single ctl operation `raise`.
// This is equivalent to writing:
// ```
// effect raise
//   ctl raise(s:string) : a
// ```

effect ctl raise(s : string ) : a

fun safe-div(x,y)
  if y==0 then raise("division by zero") else x / y


fun rcatch(action,h)
  with ctl raise(s) h(s)   // handle `raise` with function `h`
  action()                     // in `action()`


fun zerodiv(x,y)
  rcatch( fn() safe-div(x,y), fn(s) 0 )


// reify the exception effect back to a `:maybe` value
fun to-maybe(action)
  with final ctl raise(s) Nothing   // a control clause marked as `final` cannot resume; this can be more efficient as it runs finalizers eagerly and does not capture a resumption.
  Just(action())


pub fun example1()
  zerodiv(10,0).println



// --------------------------------------------------------
//  State
// --------------------------------------------------------

effect state<s>
  fun get() : s
  fun put( x : s ) : ()


fun counter()
  val i = get()
  if i <= 0 then () else
    println("hi")
    put(i - 1);
    counter()


// State handler.
fun state(init, action)
  var s := init        // use a local mutable variable
  handle action
    return(x)  (x,s)
    fun get()  s
    fun put(x) s := x


pub fun example3()
  state(1,counter).snd



// --------------------------------------------------------
//  Iterators
// --------------------------------------------------------

// Now we use general ctl `ctl` as we want to enable breaking
// the interation (and thus not resume). Equivalent to:
// ````
// effect yield<a>
//   ctl yield( item : a ) : ()
// ````
effect<a> ctl yield( item : a ) : ()

fun iterate(xs : list<a> ) : yield<a> ()
  match xs
    Cons(x,xx) -> { yield(x); iterate(xx) }
    Nil -> ()


fun foreach( f : a -> e bool, action : () -> <yield<a>|e> () ) : e ()
  with ctl yield(x) if f(x) then resume(()) else ()   // resume is explicit in a `ctl` operation
  action()


pub fun example4()
  foreach( fn(x:int){ println(x); x <= 1 } )
    [1,2,3].iterate

pub fun example4b()
  with return(x) ()                // just force final result to ()
  with amb
  with foreach fn(x:int)
    if flip() then println(x) else println("flip false " ++ x.show)
    x <= 1
  [1,2,3].iterate


// --------------------------------------------------------
//  Resume more than once
// --------------------------------------------------------

effect ctl flip() : bool

fun xor() : flip bool
  val p = flip()
  val q = flip()
  (p||q) && not(p&&q)


// handler that randomly flips
val coinflip = handler
  fun flip() srandom-bool()      // we can still define an operation as `fun` even if declared as `ctl`


// handler that returns all possible outcomes
val amb = handler
  return(x)  [x]
  ctl flip() resume(False) ++ resume(True)


pub fun example5()
  amb(xor).show.println



// --------------------------------------------------------
//  Combine effects
// --------------------------------------------------------

fun surprising() : <flip,state<int>> bool
  val p = flip()
  val i = get()
  put(i+1)
  if (i>0 && p) then xor() else False


pub fun example6()
  state(0){ amb(surprising) }.show.println

pub fun example7()
  amb{ state(0,surprising) }.show.println


// --------------------------------------------------------
//  Testing
// --------------------------------------------------------
pub fun main()
  example1()
  example2()
  example3()
  example4()
  example5()
  example6()
  42

