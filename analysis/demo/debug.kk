// Demo for debugging / tracing the source of an error (from unjust / Nothing)

fun error(x : int, v: maybe<int>): exn int
  if x == 0 then x 
  else 
    val res = v.unjust()
    res



















fun test0()
  error(10, Just(10))
  if False then 
    val res = error(0, Nothing)
    ()









fun do-something(x: int, y)
  println(x.show)
  if x == 0 then error(x, y) else x
  error(x, Just(x))















fun test1()
  val res1 = do-something(13, Nothing)
  val res2 = do-something(0, Just(11))
  ()