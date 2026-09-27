type rec
  Rec(a: list<int>, b: list<int>, c: list<int>, d: int)

// (1) wildcard for one field
fun bump-wild(r: rec): rec
  match r
    Rec(a, b, _, d) -> Rec(a, b, [], d + 1)

// (2) a field's value moved into a DIFFERENT field
fun bump-shift(r: rec): rec
  match r
    Rec(a, b, c, d) -> Rec(a, a, c, d + 1)

pub fun main()
  var x := Rec([1],[2],[3],0)
  repeat(3) { x := x.bump-wild.bump-shift }
  println(x.d)
