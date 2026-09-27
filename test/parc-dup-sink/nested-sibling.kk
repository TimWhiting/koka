// Exercises the SIBLING branch: `Nil` does not use a,b,d, so a deferred dup must
// not be dropped there. t3 passed only because its Nil branch never ran.
type rec
  Rec(a: list<int>, b: list<int>, c: list<int>, d: int)

fun bump-nested(r: rec, xs: list<int>): rec
  match r
    Rec(a, b, c, d) ->
      match xs
        Cons(_, rest) -> Rec(a, b, rest, d + 1)
        Nil -> r                       // <- the path that over-released

pub fun main()
  var x := Rec([1],[2],[3],0)
  // alternate: non-empty (uses a,b,d) then empty (uses none)
  repeat(200) { x := bump-nested(bump-nested(x, [1]), []) }
  println(x.a.show ++ " " ++ x.b.show ++ " " ++ x.c.show ++ " " ++ x.d.show)
