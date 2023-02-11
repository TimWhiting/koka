effect one
  fun one(): string

fun test1(): string
  with handler
     fun one() ""
  val y = one()
  val x = "" ++ "hello" ++ "ctl"
  y ++ x ++ one()

// linear effect two
//   fun two(): string

// fun test2(): string
//   with handler
//     fun two() ""
//   val y = two()
//   val x = "" ++ "hello" ++ "ctl"
//   y ++ x ++ two()

fun main(): console ()
  test1().println
  // test2().println