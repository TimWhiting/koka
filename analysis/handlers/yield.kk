// a generator effect with one operation
effect yield<a>
  ctl yield( x : a ) : ()

// traverse a list and yield the elements
fun traverse( xs : list<a> ) : yield<a> ()
  match xs
    Cons(x,xx) -> { yield(x); traverse(xx) }
    Nil        -> ()

// bind the yield operation dynamically
pub fun analyze() : console ()
  with ctl yield( i : int)
         resume(println("yielded " ++ i.show))
  [1,2,3].traverse
  println("done")

