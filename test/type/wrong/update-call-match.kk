// a closure that reads `x`, taken out of a pair by a match, is called in the update of `x`
fun f() : int
  var x := 1
  val p = (fn() x, 1)
  match p
    (g, _) -> { x := x + g(); x }
