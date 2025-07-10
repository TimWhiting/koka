
fun main()
  [0, 1, 2].map(_ + 1).println
  [0, 1, 2].dupmap(_ * _).println
  val id = int/(+)(_, _)
  val s = list/show(_, ?show=int/show(_))
  [0, 1, 2].s.println
  println(id(10, 20))

fun dupmap(l : list<a>, f: (a, a) -> b): list<b>
  match l
    Cons(h, t) -> Cons(f(h, h), dupmap(t, f))
    Nil -> Nil