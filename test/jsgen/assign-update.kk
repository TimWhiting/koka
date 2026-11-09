// `x := e` gives the same result whether it is checked as an update (`e` total)
// or as a plain assignment (`e` reads another local, or may throw)
fun counter( n : int ) : div int
  var i := 0
  var s := 0
  while { i < n }
    s := s + i
    i := i + 1
  s

fun main()
  var xs := [1, 2, 3]
  xs := xs.map(fn(x) x * 2)
  println(xs)
  var ys := [4]
  xs := xs ++ ys
  println(xs)
  xs := xs.map(fn(x) if x > 10 then throw("too big") else x)
  println(xs)
  println(counter(10))
