fun debug-trace()
  False

fun id1(xx)
  debug-trace()
  xx

fun my-map(f, l)
  debug-trace()
  fun lp(lst)
    match lst
      Nil -> Nil
      Cons(x, xs) -> Cons(id1(f)(x), lp(xs))
  lp(l)

fun main()
  my-map(id1(fn(a) a + 1), [1, 2, 3]).show.println
  my-map(id1(fn(b) b + 1), [7, 8, 9]).show.println
   