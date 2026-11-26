// a function written in the update that does not use the local variables, next to a direct use
fun f() : list<int>
  var y := 1
  var xs := [1,2]
  xs := xs.map(fn(v) v * 2) ++ [y]
  xs

fun main()
  println(f())
