// a function written in the update calls a closure that reads `xs`
fun f() : list<int>
  var xs := [1,2]
  val gx = fn() xs.length
  xs := xs.map(fn(v) v + gx())
  xs
