// define append

type pair
  List(l: list<pair>)
  Num(n: int)

fun append1(x, y)
  match x
    Nil -> y
    Cons(x', xs) -> Cons(x', append1(xs, y))

fun flatten(x: pair): div list<pair>
  match x
    List(Cons(a, b)) -> a.flatten.append1(List(b).flatten)
    Num(n) -> [Num(n)]
    List(Nil) -> []

fun show(x: pair): div string
  match x
    List(l) -> l.show
    Num(n) -> n.show

fun analyze()
  flatten(List([List([Num(1), Num(2)]), List([List([Num(3), Num(4), Num(5)])])]))

fun main()
  val res = flatten(List([List([Num(1), Num(2)]), List([List([Num(3), Num(4), Num(5)])])]))
  res.show.println
  