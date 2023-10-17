effect<a> ctl yield( item : a ) : ()

fun iterate(xs : list<a> ) : yield<a> () 
  match xs
    Cons(x,xx) -> 
      yield(x)
      iterate(xx)
    Nil -> ()

fun handleint(i: int, res)
  println(i.show)
  res(())

fun main()
  with handler
    ctl yield(a)
      if a == 2 then 
        print("Found a 2!")
        handleint(a, resume)
      else
        println(a)
        handleint(a, resume)
  [0, 1, 2, 3].iterate
