// the check uses the final type of `g`: a later assignment makes it read `x`
fun f() : div int
  var x := 1
  var g := fn() 0
  repeat(2)
    x := x + g()
    g ::= (fn() x)
  x
