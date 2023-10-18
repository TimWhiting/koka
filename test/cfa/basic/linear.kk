effect<a> ctl yield( item : a ) : ()

fun iterate(xs : list<a> ) : yield<a> () 
  match xs
    Cons(x,xx) -> 
      yield(x)
      iterate(xx)
    Nil -> ()

fun handleint(i1: int, res)
  println(i1.show)
  res(())

fun main()
  with handler
    ctl yield(a)
      if a == 2 then 
        println("Found a 2!")
        handleint(a, resume)
      else
        println(a)
        handleint(a, resume)
  [0, 1, 2, 3].iterate
