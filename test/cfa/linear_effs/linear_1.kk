linear effect one_e
  fun one(): string

effect two_e
  ctl two(): bool

fun list(i: int): div list<int>
  if i == 0 then
    []
  else
    Cons(i, list(i - 1))

fun test1(i: int): <div,two_e,one_e> string
  val x = list(i).map(fn(x) test1(x - 1)).join("")
  "Hello" ++ x ++ one() ++ (if two() then "World" ++ one() else one() ++ "World2")

fun main(): <div,console> ()
  with handler
    fun one() "one"
  val x = handle({ test1(4)  ++ "done"})
    ctl two() one() ++ resume(True) ++ one() ++ resume(False)
    return(x) x
  x.count.println()