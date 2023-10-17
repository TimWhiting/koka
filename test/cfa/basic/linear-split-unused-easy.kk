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

// Harder, but if we can determine that lookup will never fail, we can make this linear
fun do-something()
  extend("a", 1)
  extend("b", 2)
  // The non-linear part of the handler is never used