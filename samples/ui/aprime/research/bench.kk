// Quick performance look at the A-prime mechanics: is the bookkeeping
// (tracked reads, prefix dirty checks, cache lookups) cheap relative to what
// it saves? Tree: `wide` memo components, each building `deep` text items
// (string work stands in for build+layout cost). One component's cell is
// bumped per frame (the animating leaf); the rest should hit.
//   A: no memo        -- full rebuild every frame (today's lib/ui)
//   B: memo, 1 dirty  -- the animation steady state
//   C: memo, all dirty-- worst case: bookkeeping is pure overhead
module bench
import std/num/int64
import std/num/float64
import std/time/timer
import std/time/duration
import std/data/int-map
import std/data/int-set

alias path = list<string>

fun is-prefix( p : path, d : path ) : div bool
  match (p, d)
    (Nil, _) -> True
    (Cons(x, xs), Cons(y, ys)) -> x == y && is-prefix(xs, ys)
    _ -> False

effect store
  fun cell-read( id : int ) : string
  fun cell-write( id : int, v : string ) : ()
  fun memo-enter( key : path ) : bool
  fun memo-exit( key : path, built : string ) : ()
  fun memo-cached( key : path ) : string

fun with-store( action : () -> <store,div|e> a ) : <div|e> a
  var cells   : list<(int,string)>  := []
  var deps    : list<(int,path)>    := []
  var dirty   : list<path>          := []
  var cache   : list<(path,string)> := []
  var current : list<path>          := []
  with handler
    fun cell-read(id)
      match current
        Cons(k, _) ->
          if !deps.any(fn(d) d.fst == id && d.snd == k) then deps := Cons((id, k), deps)
        _ -> ()
      cells.lookup(fn(i) i == id).default("")
    fun cell-write(id, v)
      cells := Cons((id, v), cells.filter(fn(p) p.fst != id))
      dirty := deps.filter(fn(d) d.fst == id).map(snd) ++ dirty
    fun memo-enter(k)
      val miss = !cache.any(fn(c) c.fst == k) || dirty.any(fn(d) is-prefix(k, d))
      if miss then
        deps := deps.filter(fn(d) d.snd != k)
        current := Cons(k, current)
      miss
    fun memo-exit(k, built)
      cache := Cons((k, built), cache.filter(fn(c) c.fst != k))
      dirty := dirty.filter(fn(d) !is-prefix(k, d))
      current := current.drop(1)
    fun memo-cached(k)
      cache.lookup(fn(c) c == k).default("?")
  action()

fun memo( key : path, build : () -> <store,div|e> string ) : <store,div|e> string
  if memo-enter(key) then
    val w = build()
    memo-exit(key, w)
    w
  else memo-cached(key)

val wide = 30      // memo components
val deep = 30      // items built per component

// the stand-in build cost: read my cell, build `deep` item strings
fun component-body( i : int ) : <store,div> string
  val v = cell-read(i)
  list(1, deep).map(fn(j) "item-" ++ j.show ++ "-" ++ v).join(",")

fun view-memo() : <store,div> string
  list(1, wide).map(fn(i) memo(["c" ++ i.show]) fn() component-body(i)).join("|")

fun view-nomemo() : <store,div> string
  list(1, wide).map(fn(i) component-body(i)).join("|")

fun bench( label : string, frames : int, f : (int) -> <store,div,ndet,console> () ) : <div,ndet,console> ()
  with with-store
  list(0, wide).foreach fn(i) cell-write(i, "seed")
  val t0 = ticks()
  list(1, frames).foreach(f)
  val ms = (ticks() - t0).milli-seconds
  println(label ++ ": " ++ ms.show ++ " ms for " ++ frames.show ++ " frames  (" 
          ++ (ms.float64 / frames.float64).show ++ " ms/frame)")

// D: the same memo semantics with O(1) bookkeeping -- int-keyed vectors
// standing in for cache/dirty state ATTACHED TO KEYTRIE NODES (what the
// lib/ui integration would do). Flat tree here, so subtree-dirty = own bit.
fun bench-o1( label : string, frames : int, all-dirty : bool ) : <div,ndet,console,exn> ()
  var cache : vector<string> := vector(wide + 1, "")
  var dirty : vector<bool>   := vector(wide + 1, True)
  var cells : vector<string> := vector(wide + 1, "seed")
  fun memo1( i : int, build : () -> <local<_>,div,exn> string ) : <local<_>,div,exn> string
    if dirty[i] then
      val w = build()
      cache[i] := w
      dirty[i] := False
      w
    else cache[i]
  fun body1( i : int ) : <local<_>,div,exn> string
    val v = cells[i]
    list(1, deep).map(fn(j) "item-" ++ j.show ++ "-" ++ v).join(",")
  val t0 = ticks()
  list(1, frames).foreach fn(fr)
    if all-dirty then
      list(1, wide).foreach fn(i)
        cells[i] := "v" ++ fr.show
        dirty[i] := True
    else
      cells[1] := "v" ++ fr.show
      dirty[1] := True
    list(1, wide).map(fn(i) memo1(i, fn() body1(i))).join("|").count.ignore
  val ms = (ticks() - t0).milli-seconds
  println(label ++ ": " ++ ms.show ++ " ms for " ++ frames.show ++ " frames  ("
          ++ (ms.float64 / frames.float64).show ++ " ms/frame)")

fun bench-o1-nomemo( label : string, frames : int ) : <div,ndet,console,exn> ()
  var cells : vector<string> := vector(wide + 1, "seed")
  fun body1( i : int ) : <local<_>,div,exn> string
    val v = cells[i]
    list(1, deep).map(fn(j) "item-" ++ j.show ++ "-" ++ v).join(",")
  val t0 = ticks()
  list(1, frames).foreach fn(fr)
    cells[1] := "v" ++ fr.show
    list(1, wide).map(fn(i) body1(i)).join("|").count.ignore
  val ms = (ticks() - t0).milli-seconds
  println(label ++ ": " ++ ms.show ++ " ms for " ++ frames.show ++ " frames  ("
          ++ (ms.float64 / frames.float64).show ++ " ms/frame)")

// G/H/I: the same memo semantics over PATRICIA TREES (std/data/int-map /
// int-set) -- the realistic store for SPARSE keytrie ids (a vector needs
// dense small ints; trie node ids are neither once trees grow/shrink).
fun bench-imap( label : string, frames : int, all-dirty : bool ) : <div,ndet,console> ()
  var cache : int-map<string> := int-map/empty()
  var dirty : int-set         := int-set/empty()
  var cells : int-map<string> := int-map/empty()
  list(1, wide).foreach fn(i) cells := cells.set(i.int64, "seed")
  fun memo1( i : int, build : () -> <local<_>,div> string ) : <local<_>,div> string
    val k = i.int64
    if dirty.member(k) then
      val w = build()
      cache := cache.set(k, w)
      dirty := dirty.remove(k)
      w
    else
      match cache.lookup(k)
        Just(w) -> w
        Nothing ->
          val w = build()
          cache := cache.set(k, w)
          w
  fun body1( i : int ) : <local<_>,div> string
    val v = cells.lookup(i.int64).default("")
    list(1, deep).map(fn(j) "item-" ++ j.show ++ "-" ++ v).join(",")
  val t0 = ticks()
  list(1, frames).foreach fn(fr)
    if all-dirty then
      list(1, wide).foreach fn(i)
        cells := cells.set(i.int64, "v" ++ fr.show)
        dirty := dirty.insert(i.int64)
    else
      cells := cells.set(1.int64, "v" ++ fr.show)
      dirty := dirty.insert(1.int64)
    list(1, wide).map(fn(i) memo1(i, fn() body1(i))).join("|").count.ignore
  val ms = (ticks() - t0).milli-seconds
  println(label ++ ": " ++ ms.show ++ " ms for " ++ frames.show ++ " frames  ("
          ++ (ms.float64 / frames.float64).show ++ " ms/frame)")

fun bench-imap-nomemo( label : string, frames : int ) : <div,ndet,console> ()
  var cells : int-map<string> := int-map/empty()
  list(1, wide).foreach fn(i) cells := cells.set(i.int64, "seed")
  fun body1( i : int ) : <local<_>,div> string
    val v = cells.lookup(i.int64).default("")
    list(1, deep).map(fn(j) "item-" ++ j.show ++ "-" ++ v).join(",")
  val t0 = ticks()
  list(1, frames).foreach fn(fr)
    cells := cells.set(1.int64, "v" ++ fr.show)
    list(1, wide).map(fn(i) body1(i)).join("|").count.ignore
  val ms = (ticks() - t0).milli-seconds
  println(label ++ ": " ++ ms.show ++ " ms for " ++ frames.show ++ " frames  ("
          ++ (ms.float64 / frames.float64).show ++ " ms/frame)")

// J/K: int-map writes through PR716's unique-local `update` -- the var's
// value is taken out at refcount 1, so int-map's fbip zipper reuses the
// spine IN PLACE instead of copying it (a plain `m := m.set(..)` reads the
// var while it still holds the value: rc=2, no reuse, full spine copy).
fun bench-imap-u( label : string, frames : int, all-dirty : bool ) : <div,ndet,console> ()
  var cache : int-map<string> := int-map/empty()
  var dirty : int-set         := int-set/empty()
  var cells : int-map<string> := int-map/empty()
  list(1, wide).foreach fn(i)
    std/core/types/@byref(cells).update(fn(t) t.set(i.int64, "seed"))
  fun memo1( i : int, build : () -> <local<_>,div> string ) : <local<_>,div> string
    val k = i.int64
    if dirty.member(k) then
      val w = build()
      std/core/types/@byref(cache).update(fn(t) t.set(k, w))
      std/core/types/@byref(dirty).update(fn(t) t.remove(k))
      w
    else
      match cache.lookup(k)
        Just(w) -> w
        Nothing ->
          val w = build()
          std/core/types/@byref(cache).update(fn(t) t.set(k, w))
          w
  fun body1( i : int ) : <local<_>,div> string
    val v = cells.lookup(i.int64).default("")
    list(1, deep).map(fn(j) "item-" ++ j.show ++ "-" ++ v).join(",")
  val t0 = ticks()
  list(1, frames).foreach fn(fr)
    if all-dirty then
      list(1, wide).foreach fn(i)
        std/core/types/@byref(cells).update(fn(t) t.set(i.int64, "v" ++ fr.show))
        std/core/types/@byref(dirty).update(fn(t) t.insert(i.int64))
    else
      std/core/types/@byref(cells).update(fn(t) t.set(1.int64, "v" ++ fr.show))
      std/core/types/@byref(dirty).update(fn(t) t.insert(1.int64))
    list(1, wide).map(fn(i) memo1(i, fn() body1(i))).join("|").count.ignore
  val ms = (ticks() - t0).milli-seconds
  println(label ++ ": " ++ ms.show ++ " ms for " ++ frames.show ++ " frames  ("
          ++ (ms.float64 / frames.float64).show ++ " ms/frame)")

pub fun main()
  val frames = 2000
  bench("A no-memo full rebuild ", frames) fn(fr)
    cell-write(1, "v" ++ fr.show)          // one cell animates
    view-nomemo().count.ignore
  bench("B memo, 1 dirty/frame  ", frames) fn(fr)
    cell-write(1, "v" ++ fr.show)
    view-memo().count.ignore
  bench("C memo, ALL dirty/frame", frames) fn(fr)
    list(1, wide).foreach fn(i) cell-write(i, "v" ++ fr.show)
    view-memo().count.ignore
  bench-o1("D O(1)-store, 1 dirty  ", frames, False)
  bench-o1("E O(1)-store, ALL dirty", frames, True)
  bench-o1-nomemo("F O(1) no-memo baseline", frames)
  bench-imap("G int-map, 1 dirty     ", frames, False)
  bench-imap("H int-map, ALL dirty   ", frames, True)
  bench-imap-nomemo("I int-map no-memo base ", frames)
  bench-imap-u("J int-map+u716, 1 dirty", frames, False)
  bench-imap-u("K int-map+u716, ALLdrty", frames, True)
