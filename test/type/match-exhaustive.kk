
// fun wrong-inexhaustive(c: bool, d: bool): total int
//   match (c, d)
//     (True, False) -> 0
//     (False, True) -> 23
//     (False, False) -> 23

fun exhaustive(c: bool, d: bool): total int
  match (c, d)
    (True, False) -> 0
    (False, True) -> 23
    (False, False) -> 23
    (True, True) -> 0


// Efficiently reverse a list `xs` and append it to `tl`:
// `reverse-append(xs,tl) == reverse(xs) ++ tl
pub fip fun reverse-append( xs : list<a>, tl : list<a> ) : list<a>
  reverse-acc(tl,xs)

fip fun reverse-acc(acc : list<a>, ys : list<a> ) : list<a>
    match ys
      Cons(x,xx) -> reverse-acc(Cons(x,acc),xx)
      _          -> acc

// 1. Literal followed by Wildcard (Exhaustive)
fun exhaustive-lit-wild(x: int): int
  match x
    1 -> 10
    _ -> 20

// 2. Literal only (Inexhaustive)
// fun wrong-inexhaustive-lit(x: int): int
//   match x
//     1 -> 10
//     2 -> 20

// 3. Tuple with Literal, followed by Wildcard (Exhaustive)
// The wildcard `(_,_)` should catch all other integers
fun exhaustive-tuple-lit(x: (int, bool)): int
  match x
    (1, True) -> 1
    (1, False) -> 2
    (_, _) -> 3

// 4. Tuple with Literal, missing cases (Inexhaustive)
// Matches (1, True) and (1, False), but missing (2, True), etc.
// fun wrong-inexhaustive-tuple-lit(x: (int, bool)): int
//   match x
//     (1, True) -> 1
//     (1, False) -> 2

// 5. List with Literal inside pattern (Exhaustive)
fun exhaustive-list-lit(xs: list<int>): int
  match xs
    Cons(1, Nil) -> 1
    Cons(_, _)   -> 2
    Nil          -> 3

// 6. List with Literal, missing wild catch (Inexhaustive)
// fun wrong-inexhaustive-list-lit(xs: list<int>): int
//   match xs
//     Cons(1, Nil) -> 1
//     Nil          -> 0

// 7. Permutations: Fully explicit boolean tuple
fun exhaustive-bools-full(x: (bool, bool)): int
  match x
    (True, True)   -> 1
    (True, False)  -> 2
    (False, True)  -> 3
    (False, False) -> 4

// 8. Permutations: Mixed Structure
// (True, _) covers (True, True) and (True, False)
// (False, True) covers (False, True)
// (False, False) covers (False, False)
fun exhaustive-bool-mixed(x: (bool, bool)): int
  match x
    (True, _)      -> 1
    (False, True)  -> 2
    (False, False) -> 3

// 9. Permutations: Nested Maybes
// Need coverage for:
// (Nothing, Nothing)
// (Nothing, Just(_))
// (Just(_), Nothing)
// (Just(_), Just(_))
fun exhaustive-maybe-tuples(x: (maybe<int>, maybe<int>)): int
  match x
    (Nothing, Nothing) -> 1
    (Just, Nothing)    -> 2
    (Nothing, Just)    -> 3
    (Just, Just)       -> 4

// 10. Permutations: Nested Maybes Missing Case
// Missing (Just, Just)
// fun wrong-inexhaustive-maybe-tuples(x: (maybe<int>, maybe<int>)): int
//   match x
//     (Nothing, Nothing) -> 1
//     (Just, Nothing)    -> 2
//     (Nothing, Just)    -> 3

// 11. Permutations: Three way split
// (True, _, _)
// (False, True, _) 
// (False, False, True)
// (False, False, False)
fun exhaustive-tri-split(x: (bool, bool, bool)): int
  match x
    (True, _, _)          -> 1
    (False, True, _)      -> 2
    (False, False, True)  -> 3
    (False, False, False) -> 4


fun main()
  exhaustive-lit-wild(10)
  exhaustive-tuple-lit((2, True))
  exhaustive-list-lit([2,3,4])
  exhaustive-bools-full((False, True))
  exhaustive-bool-mixed((False, False))
  exhaustive-maybe-tuples((Just(1), Nothing))
  exhaustive-tri-split((False, False, False))
  // catch fn(err) err.show
  //   wrong-inexhaustive-lit(10)
  // catch fn(err) err.show
  //   wrong-inexhaustive-tuple-lit((2, True))
  // catch fn(err) err.show
  //   wrong-inexhaustive-list-lit([2,3,4])
  // catch fn(err) err.show
  //   wrong-inexhaustive-maybe-tuples((Just(1), Just(2)))



fun exhaustive-cons(x: list<int>): int
  match x
    Cons(y, ys) -> y
    Cons -> 0
    _ -> 1