fun debug-trace()
  trace("Hi")

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

fun analyze()
  val res1 = my-map(id1(fn(a) a + 1), [1, 2, 3])
  my-map(id1(fn(b) b + 1), [7, 8, 9])

fun main()
  val res1 = my-map(id1(fn(a) a + 1), [1, 2, 3])
  res1.show.println
  val res2 = my-map(id1(fn(b) b + 1), [7, 8, 9])
  res2.show.println
