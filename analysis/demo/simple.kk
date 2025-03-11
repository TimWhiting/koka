// 0-CFA
// Numbers & Booleans

fun width(wide): total int
  if wide then 10 else 4

fun test()
  val wide = width(True)
  val narrow = width(False)
  // We lose the context of which call to "+" was demanded.
  // We have to represent all values that flow to this plus
  // Some of those calls might fail
  val res = wide + narrow
  ()

// recursion, 0-CFA (closure sets)
//
