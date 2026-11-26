// The right-hand side of `x := e` can use any effect in `ioc`, read and write the other
// variables in the scope of `x` directly, and define functions that do not use them.
fun spin(n : int) : div int
  if n <= 0 then 0 else spin(n - 1)

pub fun main()
  var x := [1,2]
  var y := 10
  var n := 0
  x := x.map(fn(v) v * 2) ++ [y]
  x := Cons(y + spin(3) + unique() * 0, x)
  x := (if True then { n := n + 1; println("update"); Cons(n, x) } else x)
  x := (if True then { fun g(v) v + 1; x.map(g) } else x)
  if n < 0 then throw("negative")
  println(x.show ++ " " ++ n.show)
