
// Now we use general ctl `ctl` as we want to enable breaking
// the interaction (and thus not resume). Equivalent to:
// ````
// effect yield<a>
//   ctl yield( item : a ) : ()
// ````
effect<a> ctl yield( item : a ) : ()

fun iterate(xs : list<a> ) : yield<a> ()
  match xs
    Cons(x,xx) -> { yield(x); iterate(xx) } // always yields control (could reuse current function to allocate next if singleton). 
    // Cons(x,xx) -> { @always-mon(yield)(x); iterate(xx) } // always yields control (could reuse current function to allocate next if singleton). 
    Nil -> ()


fun foreach( f : a -> e bool, action : () -> <yield<a>|e> () ) : e ()
  with ctl yield(x) 
          if f(x) then // might always yield control to flip above (under specialization to f)
            // Could lift the x <= 1 test into here from the functions.
            resume(()) // second resume is always final.
          else ()   // resume is explicit in a `ctl` operation
  action() // always yields control.

effect ctl flip() : bool

// handler that returns all possible outcomes
// val amb = handler
//   return(x3)  [x3]
//   ctl flip() @never-mon(resume)(False) ++ @never-mon(resume)(True) // never yields control after resume (this is top handler).
val amb = handler
  return(x3)  [x3]
  ctl flip() resume(False) ++ resume(True) // never yields control after resume (this is top handler).

pub fun example4()
  foreach( fn(x2:int){ println(x2); x2 <= 1 } )
    [1,2,3].iterate 

pub fun example4b()
  with return(x) ()                // just force final result to ()
  with amb
  with foreach fn(x1:int)
    if flip() then println(x1) else println("flip false " ++ x1.show)
    x1 <= 1
  [1,2,3].iterate

fun main()
  example4()
  example4b()

fun analyze-main1()
  main()
fun result-main1()
  ()