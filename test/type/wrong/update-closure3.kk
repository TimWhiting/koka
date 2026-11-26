// a function parameter called in the update: its effect becomes `local<h>` there, and an
// argument may read `x`, so its type may not mention the heap of `x`
fun f() : int
  var x := 1
  val apply = fn(h : () -> _ int) { x := x + h(); x }
  apply(fn() 0) + apply(fn() x)
