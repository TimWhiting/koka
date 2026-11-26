// the value of `fs` may hold a function that reads the local variables of its scope, so it could
// read `fs` while it is updated
fun f() : div list<int>
  var y := 10
  var fs := [fn() 0]
  fs ::= Cons(fn() y, fs)
  fs := fs.drop(1)
  fs.map(fn(g) g())
