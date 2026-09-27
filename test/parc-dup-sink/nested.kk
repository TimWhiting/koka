type rec
  Rec(a: list<int>, b: list<int>, c: list<int>, d: int)

// reconstruction inside a NESTED match -- the shape alex-advance has
fun bump-nested(r: rec, xs: list<int>): rec
  match r
    Rec(a, b, c, d) ->
      match xs
        Cons(_, rest) -> Rec(a, b, rest, d + 1)
        Nil -> r

pub fun main()
  var x := Rec([1],[2],[3],0)
  repeat(3) { x := bump-nested(x, [1,2]) }
  println(x.d)
