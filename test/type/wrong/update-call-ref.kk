// a closure that reads `x`, stored in a reference, is called in the update of `x`
fun f() : <div,st<global>> int
  var x := 1
  val r = ref(fn() 0)
  r := (fn() x)
  x := x + (!r)()
  x
