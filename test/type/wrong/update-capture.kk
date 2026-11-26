// a function written in the update may not use the other local variables of the scope: only a
// direct use is allowed (as it would be if the function were defined before the update)
fun f() : list<int>
  var y := 1
  var xs := [1,2]
  xs := xs.map(fn(v) v + y)
  xs
