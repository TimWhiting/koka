// The right-hand side of `x := e` can read and write the other local variables of the scope, update
// them, and use functions that use them, as long as none of these may use `x`; whether a function is
// written in the update or bound before it makes no difference.
fun f() : div (int,int,list<int>)
  var x := 1
  var y := 10
  x := x + y
  x := (if True then { y := y + 1; x + y } else x)
  var xs := [1,2]
  xs := xs.map(fn(v) v + y)
  val g = fn(v) v + y
  xs := xs.map(g)
  val gy = fn() y
  var fs := [fn() 0]
  fs := Cons(gy, fs)
  fs := Cons(fn() x, fs)
  fs := fs.drop(1)
  (x, y, xs ++ fs.map(fn(h) h()))
