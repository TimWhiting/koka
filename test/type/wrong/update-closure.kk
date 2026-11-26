// a closure defined outside the right-hand side of `x := e` may read `x` while it is updated
fun f() : int
  var x := 1
  val g = fn() x
  x := x + g()
  x
