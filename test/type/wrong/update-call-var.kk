// a closure that reads `x`, assigned to a variable in a loop, is called in the update of `x`
fun f() : div int
  var x := 1
  var g := fn() 0
  repeat(2)
    x := x + g()
    g ::= (fn() x)
  x
