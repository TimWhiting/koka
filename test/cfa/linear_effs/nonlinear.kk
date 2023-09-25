effect one_e
  fun one(i: int): int

effect two_e
  ctl two(): bool

fun test1(i: int): <two_e,one_e> int
  val x = 1 + one(i) + i
  val y = two()
  if y then
    x + one(i - 1) + (x/2)
  else
    x + one(i) + x

fun test(acc: int): <one_e> int
  with handler
    ctl two() 
      val x: int = resume(True)
      val y: int = resume(False)
      (x + y) / (x - y)
  test1(acc)
  
fun main(): <div,console> ()
  var acc := 1
  var iter := 0
  with handler
    fun one(i: int) i + acc
  while { iter < 5000000 } 
    acc := test(acc)
    iter := iter + 1
  acc.println