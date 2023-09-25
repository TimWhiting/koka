effect find
  fun extend2(a: string, i: int): ()

fun main()
  var info := []
  with handler
    fun extend2(a: string, i: int)
      info := Cons((a, i), info)
  do-something()

// Harder, but if we can determine that lookup will never fail, we can make this linear
fun do-something()
  extend2("a", 1)
  extend2("b", 2)
  // The non-linear part of the handler is never used