effect inc
  ctl inc(): int

linear effect one_e
  fun one(): string

fun list(i: int): div list<int>
  if i == 0 then
    []
  else
    Cons(i, list(i - 1))

fun test1(i: int): <div,inc,one_e> string
  if i == 0 then
    one()
  else
    val x = list(i).map(fn(_) one() ++ (if inc() % 2 == 0 then one() ++ " " else " " ++ one())).join("")
    "Hello" ++ one() ++ test1(i - 1)

fun main(): <div,console> ()
  val res = ref("")
  val a = fn()
    var x:= 0
    with handler
      fun one() "one"
    with handler
      ctl inc() 
        resume(x)
        resume(x + 1)
        x := x + 1
    res := !res ++ test1(6).count.show
  a()
  (!res ++ "\ndone").println()