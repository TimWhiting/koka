// Standalone check of `kt-find`/`find-ids` selector resolution over the
// keytrie's id -> path table (see docs/superpowers/specs
// 2026-07-25-owner-identity-design.md, "selector queries"). Not the
// test-scenarios harness -- a plain keytree program that mints a known
// shape with raw `kt-child` and asserts resolution against the actual
// minted ids.
module selector

import std/core/unsafe
import ui/keytrie

val passed : ref<global,int> = unsafe-total{ ref(0) }
val failed : ref<global,int> = unsafe-total{ ref(0) }

fun check( name : string, cond : bool )
  if cond
    then passed := !passed + 1
    else
      failed := !failed + 1
      println("FAIL: " ++ name)

fun check-ids( name : string, got : list<int>, want : list<int> )
  check(name ++ " (got " ++ got.show ++ ", want " ++ want.show ++ ")", got == want)

fun contains( xs : list<int>, x : int ) : bool
  xs.any(fn(y) y == x)

pub fun main()
  with-keytree
    // shape:
    //   root -> Named("todos") -> Index(3) -> Named("bump")
    //        -> Named("todos") -> Index(4)
    //        -> Named("panel") -> Named("row") -> Index(3)   (SBoth pair - adjacent)
    //        -> Named("gap") -> Named("row") -> Named("mid") -> Index(3)
    //                                                          (SBoth non-match --
    //                                                          intervening segment)
    //   root -> Named("x")                     (ambiguous name #1)
    //   root -> Named("side") -> Named("x")    (ambiguous name #2)
    val todos = kt-child(root-key, Named("todos"))
    val r3 = kt-child(todos, Index(3))
    val bump = kt-child(r3, Named("bump"))
    val r4 = kt-child(todos, Index(4))

    val panel = kt-child(root-key, Named("panel"))
    val prow = kt-child(panel, Named("row"))
    val prow3 = kt-child(prow, Index(3))     // adjacent Named("row")+Index(3)

    val gap = kt-child(root-key, Named("gap"))
    val gaprow = kt-child(gap, Named("row"))
    val gapmid = kt-child(gaprow, Named("mid"))
    val gaprow3 = kt-child(gapmid, Index(3)) // path: gap/row/mid/[3] - non-adjacent pair

    val x1 = kt-child(root-key, Named("x"))
    val side = kt-child(root-key, Named("side"))
    val x2 = kt-child(side, Named("x"))

    // REPEATED SEGMENT VALUE before the tail (the backtracking cases): a
    // greedy matcher commits to the first `a` and cannot re-align to the tail
    val a1 = kt-child(root-key, Named("a"))   // path a
    val a2 = kt-child(a1, Named("a"))         // path a/a
    val pb  = kt-child(root-key, Named("pp"))
    val pbb = kt-child(pb, Named("bb"))       // pp/bb
    val pbb2 = kt-child(pbb, Named("bb"))     // pp/bb/bb

    // bare name, unique
    check-ids("bare name unique", find-ids("todos"), [todos.key-id])

    // `:i` alone under a gap
    check("todos :3 includes r3", find-ids("todos :3").contains(r3.key-id))
    check("todos :3 excludes r4", !find-ids("todos :3").contains(r4.key-id))

    // `name:i` adjacency
    check-ids("todos :3 exact", find-ids("todos :3").ints/sort, [r3.key-id].ints/sort)

    // gap-skip: "todos bump" skips the Index(3) segment
    check-ids("todos bump (gap)", find-ids("todos bump"), [bump.key-id])

    // SBoth: adjacent Named+Index resolves
    check-ids("panel row:3 (SBoth)", find-ids("panel row:3"), [prow3.key-id])

    // SBoth must NOT match when intervening segment separates the pair
    check("gap row:3 does not match (intervening)", find-ids("gap row:3").is-nil)
    // sanity: the pieces individually still resolve
    check("gap row resolves", find-ids("gap row") == [gaprow.key-id])
    check("gap :3 resolves", find-ids("gap :3") == [gaprow3.key-id])

    // ambiguity: two `Named("x")` under different parents -> both ids
    val xs = find-ids("x")
    check("ambiguous x sorted", xs == xs.ints/sort)
    check-ids("ambiguous x -> both", xs, [x1.key-id, x2.key-id].ints/sort)

    // BACKTRACKING: "a" over a tree with a (path a) and a/a (path a/a) must
    // match BOTH (each path ends in `a`) -- the greedy matcher missed a2
    check-ids("repeated 'a' -> both (backtrack)", find-ids("a").ints/sort,
              [a1.key-id, a2.key-id].ints/sort)
    // "a a" anchors the tail `a` and needs an earlier `a` ancestor -> only a2
    check-ids("'a a' -> inner only", find-ids("a a"), [a2.key-id])
    // "pp bb" over pp/bb and pp/bb/bb: both paths end in bb under a pp -> both
    check-ids("repeated 'pp bb' -> both", find-ids("pp bb").ints/sort,
              [pbb.key-id, pbb2.key-id].ints/sort)
    // "pp bb bb" anchors the tail bb, needs bb then pp earlier -> only pbb2
    check-ids("'pp bb bb' -> deepest", find-ids("pp bb bb"), [pbb2.key-id])

    // empty selector
    check("empty selector -> []", parse-selector("").is-nil)

    println("SELECTOR: " ++ (!passed).show ++ "/" ++ (!passed + !failed).show ++ " passed")
    if !failed > 0 then println("SELECTOR: FAILED (" ++ (!failed).show ++ " failures)")

fun ints/sort( xs : list<int> ) : list<int>
  fun insert( ys : list<int>, x : int ) : list<int>
    match ys
      Cons(y, rest) -> if x <= y then Cons(x, ys) else Cons(y, insert(rest, x))
      Nil -> [x]
  xs.foldl([], insert)
