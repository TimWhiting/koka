// 0-CFA
// Numbers & Booleans
fun width(w): total int
  // w will either be True or False
  if w then 10 else 4

fun test()
  // Wide and narrow are both Top ints
  val wide = width(True)
  val narrow = width(False)
  // When evaluating + below we will lose the context of which call to "+" was demanded.
  // We have to represent all values that flow out of +
  // Resolving some of those paths might cause the analysis to fail
  // Res will result in an error with 0CFA
  val res = wide + narrow
  ()

// 0CFA (closure sets)
fun this/map(l, f)
  match l
    Cons(x, rst) -> Cons(f(x), rst.this/map(f))

fun test2()
  val res = [1, 2, 3].this/map(fn(x) x)
  val res2 = [4, 5, 6].this/map(fn(y) y + 1)
  ()

// recursion 
fun fact(n)
  if n == 0 then 1 else n * fact(n - 1)

fun test-fact()
  val res = fact(10)
  val res2 = fact(1)
  ()