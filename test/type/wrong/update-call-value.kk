// the value of `fs` holds a closure that reads `fs`, and the update of `fs` calls it
fun f() : div int
  var fs := [fn() 0]
  fs ::= Cons(fn() fs.length, fs)
  fs := fs.map(fn(g) { val n = g(); fn() n })
  fs.length
