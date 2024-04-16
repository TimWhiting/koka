// n = 3
// # terms = 96

fun main()
  val res = (fn(f1) {
      val a = f1(True); 
      f1(False) })(
        fn(x1) 
          (fn(f2) {
            val b = f2(True); 
            f2(False) })(
              fn(x2) 
                (fn(f3) {
                  val c = f3(True); 
                  f3(False) })(
                  fn(x3) ((fn(z) z(x1, x2, x3))(fn(y1, y2, y3) y1)))
          )
  )
  res.println