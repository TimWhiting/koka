import std/num/random

effect amb
  ctl flip(): bool

fun random(res, v: int)
  val x = random-int() % 2 == v
  res(x)

fun main()
  with handler
    return(x) [x]
    ctl flip()
      random(resume, 0) ++ random(resume, 1)
  flip() && flip()