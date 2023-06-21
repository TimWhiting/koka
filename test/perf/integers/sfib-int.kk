module sfib

fun sfibx(n : int, x1 : int, x2 : int) : div int 
  if n <= 0
    then x1
  elif x2 > 1000000000
    then sfibx(n.dec, 1, 2)
    else sfibx(n.dec, x2 - x1, x1 * x2 + x1)

fun sfib(n : int)
  sfibx(n,1,2)

pub fun main()
  sfib(50000000).println