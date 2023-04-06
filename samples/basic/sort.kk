import std/num/random

// Make a list of random integers
fun make-list(n : int) : <div,random> list<int>
  if n == 0 then Nil else Cons(random-int(), make-list(n - 1))

fun show(xs: list<a>, s: (a) -> string): string
  foldl(xs, "[", fn (x, y) x ++ s(y) ++ ", ") ++ "]"

fun main()
  make-list(1000000).sort(compare)
