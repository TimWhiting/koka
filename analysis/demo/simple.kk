// 0-CFA
// Numbers & Booleans

fun width(w): total int
  if w then 10 else 4

fun test()
  val wide = width(True)
  val narrow = width(False)
  // We lose the context of which call to "+" was demanded.
  // We have to represent all values that flow to this plus
  // Some of those calls might fail
  val res = wide + narrow
  ()

// recursion, 0-CFA (closure sets)
fun fact(n)
  if n == 0 then 1 else n * fact(n - 1)

fun this/map(l, f)
  match l
    Cons(x, rst) -> Cons(f(x), rst.this/map(f))

fun test2()
  val res = [1, 2, 3].this/map(fn(x) x)
  val res2 = [4, 5, 6].this/map(fn(y) y + 1)
  ()