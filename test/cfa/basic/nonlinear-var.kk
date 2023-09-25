import std/num/random

effect amb
  ctl flip(): bool

fun random(res, v: int)
  val x = random-int() % 2 == v
  res(x)

fun do-something()
  var x := 0
  with handler
    return(x':bool) 
      x'.show.trace
      x'
    ctl flip()
      val fst = random(resume, 0)
      if fst then
        x := x + 1
        True
      elif random(resume, 1) then
        x := x - 1
        True
      else
        x := x + 2
        False
  flip() && flip()

fun main()
  do-something()