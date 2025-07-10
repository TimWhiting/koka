
fun main()
  [0, 1, 2].map($0 + 1).println
  [0, 1, 2].map($0 * $0).println
  [(0, 1), (1, 2), (2, 3)].map2($0 * $1 + $1).println
  val id = int/(+)($0, $1)
  val s = list/show(_, ?show=int/show(_))
  [0, 1, 2].s.println
  println(id(10, 20))
  val makefull = $first ++ " " ++ $last
  makefull(last = "Whiting", first="Tim")

fun map2(l : list<(a, b)>, f: (a, b) -> c): list<c>
  match l
    Cons((h1, h2), t) -> Cons(f(h1, h2), map2(t, f))
    Nil -> Nil
