// a value that shadows a variable of the block holds a closure that reads `x`
fun f() : div int
  var x := 1
  var g := 0
  val g = fn() x
  x := x + g()
  x
