
fun analyze-main()
  var x := 0
  val x0 = x
  x := 100
  var y := 200
  val y0 = y
  y := 300
  val y1 = y
  val x1 = x
  x0.show ++ y0.show ++ x1.show ++ y1.show

fun result-main()
  "0200100300"