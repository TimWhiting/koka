/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Builder lists: lazy/virtualized scrolling over the unified scroll model.
// A list that treats its children as a function of index -- only the visible
// window (+/- a cache margin) is built, laid out, and stateful; scrolled-out
// items unmount through the EXISTING key-retention machinery (ui/keytrie);
// infinite lists work from day one. One implementation for every backend.
// See docs/superpowers/specs/2026-07-25-lazy-lists-design.md for the design.
module ui/lazy

import std/num/float64
import ui/keytrie
import ui/widget
import ui/state

// `item(i, key)` builds row `i`'s widget under identity `key` (mint further
// identity from `key` by ordinary implicit resolution, as any stateful
// component does -- see ui/ident). `count = Nothing` is an infinite list:
// content stays one viewport ahead of the scroll position, so the scrollbar
// thumb keeps shrinking as the user scrolls; `Just(n)` gives an EXACT content
// height of `n * item-extent`. `item-extent` is documented as an ESTIMATE
// from day one (the seam for variable extents, a follow-up); this MVP treats
// it as exact -- every row is wrapped in `fixed(height = Just(item-extent))`
// (ui/widget), which REPORTS exactly `item-extent` to the enclosing column
// regardless of what the item actually measures, so the lead/trail spacer
// math (computed from `item-extent` alone) is EXACT BY CONSTRUCTION, not
// merely by convention -- geometry can no longer desync. A child that
// measures taller/shorter than `item-extent` overflows/underflows visually
// at its own row (no clip) instead of corrupting every later row's position;
// see the `oversize` scenario in test/ui/lazy.kk for the repro this closes.
// `cache` is the number of extra items materialized past each edge of the
// viewport (scroll a notch without a visible pop-in).
//
// `keep` is UNIFORM PER LIST, stamped into every item's `idx(i)` identity at
// FIRST MINT (a keytrie invariant: an identity's unmount policy is fixed
// where it is first created -- see ui/keytrie's RETENTION note). It is NOT
// per-item in this MVP: every row shares the same policy. Nesting an inner
// `KeepAlive` INSIDE a `Transient` row does NOT survive scroll-out either --
// pruning is subtree-rooted at the unmounted key (`idx(i)` itself), so the
// row's own Transient policy is what decides, regardless of what a nested
// descendant declares (see ui/keytrie: `close-node` looks at the STALE
// CHILD's own `keep`, and an unclaimed idx(i) is that stale child -- whatever
// hangs off it goes with it, subtree-rooted, nested policy or not). A
// designed (not yet built) follow-up adds `keep-of : int -> keep` plus
// dynamic "last claim wins" retention, the Flutter `updateKeepAlive` analog.
//
// `name` names the scroll region (scrollbar linking / tests / `t.scroll`),
// exactly like `scroll`'s own `name`.
pub fun lazy-column<msg>( item : (int, key) -> <keytree,uistate,ioc> widget<msg>,
                          count : maybe<int> = Nothing,
                          item-extent : float64 = 40.0,
                          cache : int = 4,
                          keep : keep = Transient,
                          name : string = "",
                          ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
  // THE WIRING SUBTLETY (see docs/superpowers/specs/2026-07-25-lazy-lists-design.md
  // and .superpowers/sdd/task-1-brief.md): the region key the windowing READS
  // (`scroll-state(sk)` below) must be the SAME key `scroll(...)` WRITES
  // metrics/offsets to at the bottom of this function. `?kk-file-line` is a
  // compiler-synthesized implicit -- UNLIKE an ordinary implicit, a call site
  // that does not pass it explicitly gets a FRESH file:line for THAT literal
  // call expression, not the value flowing through lexical/ambient scope.
  // Both the `scroll-key` call right below and the `scroll` call at the
  // bottom of this function are literal call sites INSIDE lazy-column's own
  // body (i.e. inside lazy.kk, not inside the caller), so left to their own
  // defaults they would resolve to two DIFFERENT ?kk-file-line values (two
  // different lines of lazy.kk) -- and, when `name` is empty, two DIFFERENT
  // keys (`Slot("sc", <line-of-scroll-key-call>)` vs
  // `Slot("sc", <line-of-scroll-call>)`), silently splitting the region the
  // windowing reads from the region `scroll` actually publishes into. We
  // avoid that by threading lazy-column's OWN received `?kk-file-line` (the
  // caller's call site, one single value) EXPLICITLY into both calls below,
  // so both resolve `Slot("sc", ?kk-file-line)` with the identical `fl`
  // string -- and `kt-child(of, seg)` is deterministic in `(of, seg)` alone
  // (ui/keytrie: `kt-child-id` re-roots to `of` and re-derives `seg`; it does
  // not care which call in the frame reached it, or in what order), so the
  // two calls mint/find the SAME node. When `name` is non-empty this is moot
  // -- both sides use `Named(name)`, which agrees regardless of file:line --
  // but we thread `?kk-file-line` unconditionally so the invariant holds for
  // BOTH the named and the auto (empty-name) case, and does not silently
  // regress if `name` reverts to "" later.
  val sk = scroll-key(name, ?key = ?key, ?kk-file-line = ?kk-file-line)
  val st = scroll-state(sk)
  // items are `lk`'s ONLY children: a dedicated key so the kt-open/kt-close
  // consumption boundary below prunes/retains exactly the item set, never
  // brushing the scroll region's own node (`sk`, minted separately above).
  // Namespaced the SAME way `scroll-key` namespaces `sk` (Named(name) when
  // given, else a Slot at this call site) -- two `lazy-column` calls reached
  // through a shared helper (same literal call site, same ?kk-file-line)
  // still get distinct `lk`s as long as they pass distinct `name`s; only the
  // fully-anonymous (both empty-name, same call site) case would collide,
  // same as `scroll-key` itself.
  val lk = if name.is-empty then kt-child(?key, Slot("lz", ?kk-file-line))
                             else kt-child(?key, Named("lz:" ++ name))
  val vis = if st.viewport > 0.0 then (st.viewport / item-extent).ceiling.int + 1 else 1
  // clamp `first` to `count`: not reachable today (a static `count` and an
  // externally-clamped `offset` keep `first <= count` in steady state, see
  // docs/superpowers/specs/2026-07-25-lazy-lists-design.md), but a future
  // dynamic-count follow-up could shrink `count` out from under a stale
  // `offset` before the caller re-clamps it -- floor defensively so the lead
  // spacer alone can never overshoot `total*extent`.
  val first0 = ((st.offset / item-extent).int - cache).max(0)
  val first = match count
    Just(c) -> first0.min(c)
    Nothing -> first0
  val n0 = vis + 2 * cache
  val (n, total) = match count
    Just(c) -> ((n0.min((c - first).max(0))).max(0), c)
    Nothing -> (n0, first + n0 + vis)              // infinite: one page ahead
  kt-open(lk.key-id)
  // `fixed` (ui/widget) pins every row's REPORTED height to `item-extent`
  // regardless of what `item(i, ...)` actually measures -- see the module
  // doc comment above.
  fun build-item( i : int ) : <keytree,uistate,ioc> _
    fixed(item(i, idx(i, keep = keep, ?key = lk)), height = Just(item-extent))
  val items = list(first, first + n - 1).map(build-item)
  val pruned = kt-close(lk.key-id)
  if !pruned.is-nil then drop-ids(pruned)
  val lead  = rect(0.0, first.float64 * item-extent)
  val trail = rect(0.0, ((total - first - n).max(0)).float64 * item-extent)
  scroll( column([lead] ++ items ++ [trail], gap = 0.0), name = name,
          ?key = ?key, ?kk-file-line = ?kk-file-line )
