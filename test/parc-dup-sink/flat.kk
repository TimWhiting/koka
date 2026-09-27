// minimal in-place record update: 4 fields, one changes
type rec
  Rec(a: list<int>, b: list<int>, c: list<int>, d: int)

fun bump(r: rec): rec
  match r
    Rec(a, b, c, d) -> Rec(a, b, c, d + 1)

pub fun main()
  var x := Rec([1],[2],[3],0)
  repeat(3) { x := bump(x) }
  println(x.d)
