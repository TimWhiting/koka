
fun analyze-main()
  val x = Cons(10, Nil);
  match x
    Cons(n, _) | n < 5 -> n
    _ -> 0
fun result-main()
  0

