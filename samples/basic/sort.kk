import std/num/random
import std/os/task

fun merge(a: list<a>, b: list<a>, compare : (a, a) -> pure order) : pure list<a>
  match (a, b)
    (Cons(x, xs), Cons(y, ys)) ->
      if compare(x, y) == Gt then Cons(y, merge(a, ys, compare))
      else Cons(x, merge(xs, b, compare))
    (Nil, ys) -> ys
    (xs, Nil) -> xs
    (_, _) -> Nil

alias thunk<a> = () -> pure a


fun merge-pairs(xs: list<list<a>>, compare: (a, a) -> pure order): pure list<list<a>>
  match xs
    Cons(x, Cons(y, ys)) -> Cons(merge(x, y, compare), merge-pairs(ys, compare))
    Cons(x, y) -> Cons(x, merge-pairs(y, compare))
    Nil -> Nil

fun pmerge-pairs(xs: list<list<a>>, compare: (a, a) -> pure order): pure list<thunk<list<a>>>
  match xs
    Cons(x, Cons(y, ys)) -> Cons(fn() merge(x, y, compare), pmerge-pairs(ys, compare))
    Cons(x, y) -> Cons(fn() x, pmerge-pairs(y, compare))
    Nil -> Nil

fun merge-all(xs: list<list<a>>, compare: (a, a) -> pure order): pure list<a>
  match xs
    Cons(x, Nil) -> x
    Cons(_, _) -> if xs.length > 500 then merge-all(pmerge-pairs(xs, compare).parallel, compare) else merge-all(merge-pairs(xs, compare), compare)

fun ascending(a: a, aas: (list<a>) -> list<a>, bs: list<a>, compare: (a, a) -> pure order): pure list<list<a>>
  match bs
    Cons(b, bbs) ->
      if compare(a, b) != Gt then ascending(b, fn(ys) Cons(a, ys), bbs, compare)
      else Cons(aas([a]), sequences(bs, compare))
    Nil -> Cons(aas([a]), sequences(bs, compare))

fun descending(a: a, aas: list<a>, bs: list<a>, compare: (a, a) -> pure order): pure list<list<a>>
  match bs
    Cons(b, bbs) ->
      if compare(a, b) == Gt then descending(b, Cons(a, aas), bbs, compare)
      else Cons(Cons(a, aas), sequences(bs, compare))
    Nil -> Cons(Cons(a, aas), sequences(bs, compare))

fun sequences(xs: list<a>, compare: (a, a) -> pure order): pure list<list<a>>
  match xs
    Cons(a, Cons(b, ys)) ->
      if compare(a, b) == Gt then descending(b, [a], ys, compare)
      else ascending(b, fn(ys') Cons(a, ys'), ys, compare)
    _ -> [xs]

fun psort( xs: list<a>, compare: (a, a) -> pure order ) : pure list<a>
  with unsafe-no-div
  merge-all(sequences(xs, compare), compare)

// Make a list of random integers
fun make-list(n : int) : <div,random> list<int>
  if n == 0 then Nil else Cons(random-int(), make-list(n - 1))

fun show(xs: list<a>, s: (a) -> string): string
  foldl(xs, "[", fn (x, y) x ++ s(y) ++ ", ") ++ "]"

fun main(): <pure, random> ()
  make-list(100000000).psort(compare).foldl(0, fn (x, y) x + y)
  ()
