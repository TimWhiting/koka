effect inc
  ctl inc(): int

linear effect one_e<a>
  fun one(start: a): a

fun list(i: int): div list<int>
  if i == 0 then
    []
  else
    Cons(i, list(i - 1))

fun test1(i: int, start: a, other: a): <div,inc,one_e<a>> list<a>
  if i == 0 then
    [one(start)]
  else
    list(i).map fn(_) 
      val x = one(start) 
      if inc() % 2 == 0 then one(x) else one(x)
    
fun main(): <div,console> ()
  val res = ref("")
  val a = fn()
    var x:= 0
    with handler
      fun one(a:string) a ++ "one"
    with handler
      ctl inc() 
        resume(x)
        resume(x + 1)
        x := x + 1
    res := !res ++ test1(15, "Hello ", " World").join("").count.show
  a()
  (!res ++ "\ndone").println()