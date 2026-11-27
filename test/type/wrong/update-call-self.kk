// a recursive function that shadows a variable of the block reads `x`
fun f() : div int
  var x := 1
  var k := 0
  fun k( n : int )
    if n <= 0 then x else k(n - 1)
  x := x + k(3)
  x
