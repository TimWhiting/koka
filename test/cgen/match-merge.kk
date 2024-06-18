fun implicit-error-fallthrough(e: list<int>)
  match e
    Cons(_, Cons(2, Cons(3, Nil))) -> 100.show.println
    Cons(a, Cons(1, Cons(c, Nil))) -> (a + c).show.println
    Cons(_, Cons(b, _)) -> b.show.println
    Nil -> "Nothing".println

fun reflow(e: list<int>)
  match e
    Cons(a, Cons(1, Cons(c, Nil))) -> (a + c).show.println
    Cons(_, Cons(b, _)) -> b.show.println
    Cons(a, Nil) -> a.show.println
    Nil -> "Nothing".println

fun main()
  try {
    implicit-error-fallthrough([])
    implicit-error-fallthrough([1,2])
    implicit-error-fallthrough([2,1,2])
    implicit-error-fallthrough([1])
  } fn(err) { println(err.message) }

  reflow([])
  reflow([1,2])
  reflow([2,1,2])
  reflow([1])
  