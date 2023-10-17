effect find
  fun lookup(a: string): int
  fun extend(a: string, i: int): ()

fun main()
  var info := []
  with handler
    fun lookup(a: string)
      match info.find(fn((a', _)) a == a')
        Just((_, x)) -> x
        Nothing -> throw("not found")
    fun extend(a: string, i: int)
      info := Cons((a, i), info)
  do-something()

// We can split the linear and nonlinear parts of the handler to avoid the overhead of the monadic translation. 
// Actually we could just at the operations if we know the target of the operation is linear omit the monadic translation - just for that operation
fun do-something()
  extend("a", 1)
  extend("b", 2)
  lookup("c")