// n = 2
// # terms = 69

fun main()
  val res = (fn(f1) {f1(True); f1(False)})(
    fn(x1) 
      (fn(f2) {f2(True); f2(False)})(
        fn(x2) fn(z) z(x1, x2))(fn(y1, y2) y1
      )
  )
  res.println