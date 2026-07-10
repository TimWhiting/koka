// A tail-recursive function is compiled to `{ tailcall: while(1) { ... } }`
// whose bindings are function-scoped `var`s SHARED by every iteration. A
// closure that outlives the iteration that built it -- stored in a ref here,
// forked as a strand in the case that found this -- must still see that
// iteration's values, exactly as it does on the C backend (which lambda-lifts
// each closure and copies the captured values into it at creation).
//
// Before the fix all three closures printed the LAST loop value (3 3 3), or
// `undefined` when the loop suspended before reassigning.
import std/core/unsafe

val saved : ref<global, list<() -> console ()>> = unsafe-total{ ref([]) }

fun save( f : () -> console () ) : <read<global>,write<global>> ()
  saved := Cons(f, !saved)

// tail-recursive: `n` is a parameter (overwritten by the tail call) and
// `label` is a local (re-declared each iteration) -- both are loop-carried
fun collect( n : int ) : <read<global>,write<global>,div> ()
  if n > 3 then () else
    val label = "closure " ++ n.show
    save( fn() println(label ++ " sees n=" ++ n.show) )
    collect(n + 1)

// the same shape one block deeper: the captured binding comes from a pattern
// match inside the loop body, not from the loop's top level
fun collect-matched( xs : list<int> ) : <read<global>,write<global>,div> ()
  match xs
    Nil -> ()
    Cons(x, rest) ->
      save( fn() println("matched closure sees x=" ++ x.show) )
      collect-matched(rest)

pub fun main()
  collect(1)
  collect-matched([7, 8, 9])
  (!saved).reverse.foreach( fn(f) f() )
