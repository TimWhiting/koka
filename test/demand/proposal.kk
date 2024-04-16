
fun sum(xs: list<int>, f: (int) -> int)
  match xs
    Cons(x, xs') -> f(x) + sum(xs', f)
    Nil -> 0

fun test-basics()
  val xs = [0, 1, 2, 3]
  // sum(xs, fn(x) x*x).println
  // Same as closure after the closing braces with it's body indented
  val result = sum(xs) fn(x)
    x*x
    // Makes it easier to read longer bodies
  result.println

// Inlining
fun apply(f)
  fn(x)
    f(x)

fun test-inlining()
  apply(fn(y) y + 1)(42) + apply(fn(z) z + 1)(35)

// Handlers
effect<a> ctl yield( item : a ) : ()

fun iterate(xs : list<a> ) : yield<a> () 
  match xs
    Cons(x,xx) -> 
      yield(x)
      iterate(xx)
    Nil -> ()

fun test-nonlinear()
  with handler
    ctl yield(a)
      if a == 2 then 
        print("Found a 2!")
        // Do not resume
      else
        println(a)
        resume(())
  [0, 1, 2, 3].iterate

fun test-linear()
  with handler
    ctl yield(a)
      if a == 2 then 
        print("Found a 2!")
        resume(())
      else
        println(a)
        resume(())
  [5,6,7,8].iterate


// Exceptional control flow\
effect throw-a<a>
  ctl throwa(a: a): b

fun do-throw(do: bool): <throw-a<int>> int
  throwa(10)
  20

fun test-exceptions()
  val result = handle(fn() do-throw(True))
    final ctl throwa(b:int)
      b + 1
    return(x) x + 2
  result.println

// Returns a function that adds n to it's argument
// Higher order function
fun createAddN(n: int)
  fn(x)
    x + n

fun test-addn()
  val add5 = createAddN(5)
  add5(10).println
  // Same as
  println(createAddN(5)(10))

// Returns a function that adds n to n transformed by f
fun combineAdd(n: int, f: (int) -> int): int
  val result = f(n) + n
  result

fun test-higher-order()
  val add5 = createAddN(5)
  combineAdd(10, add5).println
