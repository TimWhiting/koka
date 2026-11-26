// The effect constraint of `x := e` is solved right after `e`; annotating the effect of a closure
// that `e` calls keeps the constraint from closing it to the effect it has at that point.
pub fun main()
  var x := 1
  var g : () -> ndet int := fn() 0
  repeat(2)
    x := x + g()
    g ::= (fn() unique() * 0 + 1)
  println(x)
