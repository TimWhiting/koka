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

fun handleLinear(f)
  with handler
    ctl yield(a)
      if a == 2 then 
        print("Found a 2!")
        handleint(a, resume)
      else
        println(a)
        handleint(a, resume)
  f()

fun handleNonLinear(f)
  with handler
    ctl yield(a)
      if a == 2 then 
        print("Found a 2!")
      else
        handleint(a, resume)
  f()


fun main()
  with handleLinear
  [0, 1, 2, 3].iterate
  with handleNonLinear
  [0, 1, 2, 3].iterate
