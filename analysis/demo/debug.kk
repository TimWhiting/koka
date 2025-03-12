// Demo for debugging / tracing the source of an error (from unjust / Nothing)

fun error(v: maybe<a>): exn a
  v.unjust()

fun test0()
  error(Just(10))
  error(Nothing)






// TODO: Add call location to environments & constructors
fun do-something(x: int)
  println(x.show)
  if x == 0 then error(Nothing) else x
  error(Just(x))

fun test1()
  do-something(13)
  do-something(0)