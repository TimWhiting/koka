/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Microbenchmark for the layout / reconcile passes (see ../readme.md
// "Performance" and this directory's readme.md). Isolates tree building from
// the backends: a stub text measurer, no window, no Impeller. Measures the
// per-frame allocation of laying out a fixed grid, two ways:
//
//   koka -O2 --fallocstats -o bench reuse.kk
//   MIMALLOC_SHOW_STATS=1 ./bench fresh        # rebuild the ltree each frame
//   MIMALLOC_SHOW_STATS=1 ./bench reconcile    # reconcile against the last ltree
//
// Read the mimalloc `total#` column (cumulative allocation count) for the
// small size classes, and the `total:` byte row. Wall time:
//   koka -O2 --showtime -e reuse.kk -- fresh
//
// NOTE: this measures the tree passes in isolation, NOT the live native app
// (which shapes real paragraphs and renders at a display rate). The stub
// measurer is char-count * size. Treat the numbers as the reuse mechanism's
// effect on tree allocation, not an end-to-end frame profile.
module reuse

import std/num/float64
import std/num/int32
import std/os/env
import std/core/undiv
import ui/widget
import ui/keytrie   // root-key: this bench builds trees outside a keytree scope

val grid-size = 20      // grid-size x grid-size cells
val frames    = 20000   // iterations (each = one frame's tree work)

// stub `measure` handler: no backend, deterministic (char-count * size)
fun with-measure<a,e>( action : () -> <measure,div|e> a ) : <div|e> a
  with fun measure-text( content : string, font : font, max-w : float64 )
    (content.count.float64 * font.size * 0.55, font.size * 1.4)
  action()

fun mk-row( r : int ) : div widget<int>
  row( list(1, grid-size).map( fn(c) rect(16.0, 16.0, bg = Just(Fill(rgb(0.2, 0.8, 0.4), 2.0)), ?key = root-key) ), gap = 1.0, ?key = root-key )

fun build-tree() : div widget<int>
  column( list(1, grid-size).map(mk-row), gap = 1.0, ?key = root-key )

val root-c = tight(400.0, 400.0)

// a structural fingerprint of a laid-out tree: kind + geometry at each node
fun fingerprint( t : ltree<int> ) : div string
  match t
    LText(o, c, font, _, _, w, h) -> "T(" ++ int32/show(o) ++ "," ++ c ++ "," ++ font.size.show ++ "," ++ w.show ++ "," ++ h.show ++ ")"
    LLink(o, to, w, h, _, _, ch) -> "L(" ++ int32/show(o) ++ "," ++ to ++ "," ++ w.show ++ "," ++ h.show ++ ":" ++ ch.fingerprint ++ ")"
    LScroll(o, k, w, h, cn, off, _, ch) -> "Sc(" ++ int32/show(o) ++ "," ++ k.show ++ "," ++ w.show ++ "," ++ h.show ++ "," ++ cn.show ++ "," ++ off.show ++ ":" ++ ch.fingerprint ++ ")"
    LAct(o, _, w, h, _, _, ch) -> "Ac(" ++ int32/show(o) ++ "," ++ w.show ++ "," ++ h.show ++ ":" ++ ch.fingerprint ++ ")"
    LInteractive(o, k, _, _, w, h, _, _, ch) -> "In(" ++ int32/show(o) ++ "," ++ k.show ++ "," ++ w.show ++ "," ++ h.show ++ ":" ++ ch.fingerprint ++ ")"
    LBox(o, _, _, w, h, dx, dy, ch) ->
      "B(" ++ int32/show(o) ++ "," ++ w.show ++ "," ++ h.show ++ "," ++ dx.show ++ "," ++ dy.show ++ ":" ++ ch.fingerprint ++ ")"
    LFlex(o, w, h, kids) ->
      "F(" ++ int32/show(o) ++ "," ++ w.show ++ "," ++ h.show ++ "[" ++ kids.map(fn(e) e.fst.show ++ "/" ++ e.snd.show ++ "/" ++ e.thd.pretend-decreasing.fingerprint).join(",") ++ "])"
    LLayer(o, w, h, kids) ->
      "Y(" ++ int32/show(o) ++ "," ++ w.show ++ "," ++ h.show ++ "[" ++ kids.map(fn(e) e.fst.show ++ "/" ++ e.snd.show ++ "/" ++ e.thd.pretend-decreasing.fingerprint).join(",") ++ "])"
    LInput(o, _, v, _, _, _, w, h) -> "I(" ++ int32/show(o) ++ "," ++ v ++ "," ++ w.show ++ "," ++ h.show ++ ")"
    LSlider(o, _, _, _, v, _, w, h) -> "S(" ++ int32/show(o) ++ "," ++ v.show ++ "," ++ w.show ++ "," ++ h.show ++ ")"
    _ -> "?"

// a grid whose cells depend on a seed (so successive frames differ)
fun cell-seeded( r : int, c : int, seed : int ) : widget<int>
  val on = (r * 31 + c * 7 + seed) % 3 == 0
  val col = if on then rgb(0.6, 0.8, 0.4) else rgb(0.2, 0.2, 0.3)
  rect(16.0, 16.0, bg = Just(Fill(col, 2.0)), ?key = root-key)

fun row-seeded( r : int, seed : int ) : div widget<int>
  row( list(1, grid-size).map( fn(c) cell-seeded(r, c, seed) ), gap = 1.0, ?key = root-key )

fun grid-seeded( seed : int ) : div widget<int>
  column( list(1, grid-size).map( fn(r) row-seeded(r, seed) ), gap = 1.0, ?key = root-key )

// reconcile(layout(A), B) must produce the SAME laid-out tree as layout(B)
fun check() : <div,measure> string
  var ok := True
  var prev := grid-seeded(0).layout(root-c)
  list(1, 30).foreach fn(seed)
    val spec-r = grid-seeded(seed)
    val spec-f = grid-seeded(seed)
    val reconciled = reconcile(prev, spec-r, root-c)
    val fresh = spec-f.layout(root-c)
    if reconciled.fingerprint != fresh.fingerprint then ok := False
    prev := reconciled
  if ok then "check: ok (reconcile == fresh layout over 30 changing frames)"
        else "check: MISMATCH"

// fresh: build a new widget tree and lay it out from scratch each frame
fun go-fresh( n : int, acc : float64 ) : <div,measure> float64
  if n <= 0 then acc else
    val t = build-tree().layout(root-c)
    go-fresh(n - 1, acc + t.size.fst)

// reconcile: retain the previous ltree, reconcile the new widget tree against
// it (taking it out of the ref uniquely, exactly as the native backend does)
fun go-reconcile( r : ref<global,ltree<int>>, n : int, acc : float64 ) : <div,st<global>,measure> float64
  if n <= 0 then acc else
    val old = !r
    r := LFlex(no-owner, 0.0, 0.0, [])       // placeholder: old is now unique
    val t = reconcile(old, build-tree(), root-c)
    val w = t.size.fst
    r := t
    go-reconcile(r, n - 1, acc + w)

pub fun main()
  val mode = get-args().head.default("fresh")
  match mode
    "check"     -> println(with-measure(check))
    "reconcile" -> println("reconcile: " ++ with-measure(fn() go-reconcile(ref(build-tree().layout(root-c)), frames, 0.0)).show)
    _           -> println("fresh: " ++ with-measure(fn() go-fresh(frames, 0.0)).show)
