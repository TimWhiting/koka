/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The `uistate` effect: ALL ephemeral UI state (use-state cells, hover/press/
// focus, field values, caret phase, the animation clock, scroll metrics,
// anchor rects) lives behind SEMANTIC operations, with the store held as
// LOCAL state by the handler the runtime installs (`with-uistate` in ui/app)
// -- not in module globals. Two apps mounted in one process get independent
// stores, tests get a fresh store per handler, and the threaded mode's
// "ui-state never crosses threads" invariant is structural.
//
// MEMOIZATION (the a-prime design, samples/ui/aprime): every read op ALSO
// records a dependency edge (channel -> innermost memo boundary), every write
// op ALSO collects its readers as pending-dirty. The renderer flushes pending
// ids into the keytrie's subtree-dirty bits before building; memo boundaries
// then hit (skip build+layout) unless their subtree contains a dirty reader.
// Past a threshold of dirty readers the frame becomes a DIRTY STORM: tracking
// stops and everything misses -- a plain full rebuild at the measured 2-4%
// overhead floor. Model-message renders FORCE a storm (messages are
// user-rate; only uistate reads need fine-grained tracking).
//
// The operations are the INTERFACE: the handler owns the representation --
// int32-keyed Patricia stores here (JS-cheap; see samples/ui/aprime).
//
// This module sits BELOW ui/widget (which cannot import ui/state): widget
// thunk types (`act`, `act-msg`) carry `uistate`. The store is only touched
// from the handler's own thread and strands are cooperative, so an op runs
// to completion -- no interleaving hazard.
module ui/reactive

import std/num/float64
import std/num/int32
import std/data/int32-map
import std/data/int32-set

// the live state of a scroll region: its offset plus the measured content and
// viewport extents ALONG the scroll axis (enough for a scrollbar's thumb)
pub struct scroll-info
  offset   : float64 = 0.0
  content  : float64 = 0.0
  viewport : float64 = 0.0

// the phase of an async computation's most recent (or in-flight) result, per
// identity. The snapshot value/error live erased (`any`) -- the typed view
// lives at the call site (see the future-boundary async widget, deferred).
// NOTE: a streaming `RActive(any)` variant slots in here later (partial
// progress mid-flight) -- deliberately not added yet; this is additive.
pub type raw-phase
  RPending
  RDone( value : any )
  RFailed( err : exception )

// one identity's async slot: the generation is the epoch -- a strand
// finishing at a stale generation (superseded by a retry/new inputs) is
// discarded rather than applied (see `bump-async-gen`)
pub struct async-entry
  gen   : int
  phase : raw-phase

// past this many dirty readers a frame stops tracking and fully rebuilds
val storm-threshold = 64

pub effect uistate
  // use-state cells (erased -- the typed view + the single guarded coercion
  // live in ui/state; one id is only ever used at one type)
  fun get-cell( id : int ) : maybe<any>
  fun set-cell( id : int, v : any ) : ()
  // interaction: the single primary pointer
  fun get-hover() : maybe<int>
  fun set-hover( k : maybe<int> ) : ()
  fun get-press() : maybe<int>
  fun set-press( k : maybe<int> ) : ()
  // keyboard focus (one or none)
  fun get-focus() : maybe<int>
  fun set-focus( k : maybe<int> ) : ()
  // uncontrolled text-field values
  fun get-field( id : int ) : string
  fun set-field( id : int, v : string ) : ()
  // caret blink phase (True = visible)
  fun get-caret() : bool
  fun set-caret( v : bool ) : ()
  // the animation clock (ms; advances only while animating) + frame demand.
  // `peek-clock` does NOT record a dependency: a SETTLED animation reads the
  // time without subscribing its memo boundary to every tick -- an unsettled
  // one calls `subscribe-clock` (via request-frame) to be woken per tick
  fun get-clock() : float64
  fun peek-clock() : float64
  fun subscribe-clock() : ()
  fun tick-clock( dt : float64 ) : ()
  fun get-frame-flag() : bool
  fun set-frame-flag( v : bool ) : ()
  // scroll regions
  fun get-scroll( id : int ) : scroll-info
  fun set-scroll( id : int, info : scroll-info ) : ()
  fun list-scrolls() : list<(int,scroll-info)>
  // regions with a MANUAL scrollbar this frame
  fun add-manual-bar( id : int ) : ()
  fun get-manual-bars() : list<int>
  fun clear-manual-bars() : ()
  // the last-published MAIN scene tree, erased (see ui/view's `scope-rect-of`):
  // one frame behind -- `Scope`/Panel targets resolve owner geometry against
  // it via `owner-rect`
  fun set-scene-tree( t : any ) : ()
  fun get-scene-tree() : maybe<any>
  // resolved Scope-anchored view rects, republished once per `raw-scene/finish`
  // (view key -> its RESOLVED owner rect, only entries that resolved this
  // frame). This is the resettle-trigger source for Scope targets -- see
  // ui/view/raw-scene/finish and the backend's anchor-sig read.
  fun set-scope-rects( kvs : list<(string,(float64,float64,float64,float64))> ) : ()
  fun list-scope-rects() : list<(string,(float64,float64,float64,float64))>
  // measured text metrics, keyed by (content,font,max-width): shaping text is
  // the expensive part of layout and most strings are identical frame to frame
  fun get-text-metrics( key : string ) : maybe<(float64,float64)>
  fun set-text-metrics( key : string, wh : (float64,float64) ) : ()
  // the PAINT epoch: bumps on any state the painters read directly (hover
  // rect, focus ring, caret, field text, scroll offsets) -- cached display
  // lists are valid only within one epoch
  fun paint-epoch() : int
  // ---- the memoization protocol (see module note) ----
  fun memo-get( id : int ) : maybe<any>          // cached built widget (erased)
  fun memo-put( id : int, w : any ) : ()
  fun memo-begin( id : int ) : ()                // push the read-attribution boundary
  fun memo-end() : ()
  fun current-boundary() : maybe<int>            // head of the read-attribution stack
  // ---- views as the memo boundary's 4th cached artifact (portals; see ui/view) ----
  fun record-view( id : int, v : any ) : ()       // append an erased view under boundary `id` this frame
  fun views-of( id : int ) : list<any>            // a boundary's recorded views (erased)
  fun memo-note-hit( id : int ) : ()              // boundary `id` hit (cache reused) this frame
  fun take-hit-boundaries() : list<int>           // this frame's hit boundary ids; CLEARS on read.
                                                  // Contract: called exactly once per frame (by the one
                                                  // with-scene composition) -- a second caller in the same
                                                  // frame would silently see an empty replay set
  fun take-dirty-readers() : list<int>           // pending reader ids; clears (the renderer
                                                 // flushes them into keytrie dirty bits)
  fun dirty-storm() : bool                       // this frame fully rebuilds
  fun force-storm() : ()                         // model-message renders call this
  fun clear-storm() : ()                         // end of frame
  // drop all state belonging to pruned identities (a Transient unmount --
  // see ui/keytrie): cells, fields, scrolls, memo cache, and dependency
  // edges in BOTH directions die with the identity
  fun drop-ids( ids : list<int> ) : ()
  // clear everything (e.g. on remount)
  fun reset-uistate() : ()
  // async-computation load state, per identity (see `async-entry` above):
  // the future-boundary widget reads this at build time; an async-pump
  // strand writes it via `set-async`/`bump-async-gen`
  fun get-async( id : int ) : maybe<async-entry>
  fun set-async( id : int, e : async-entry ) : ()
  fun bump-async-gen( id : int ) : int

// ---- dependency channels (task #54) --------------------------------------
//
// A "channel" is the unit a memo boundary subscribes to: a build that READS
// some state `record`s that state's channel, and a WRITE to it `invalidate`s
// the same channel, marking every boundary that read it dirty. Get this
// wrong in EITHER direction and the bug is silent: a read that forgets to
// `record` gives a memoized subtree that never refreshes (a boundary frozen
// on stale state -- exactly the async-image-under-a-memo bug this encoding's
// 4th slot was added for), and a write that forgets to `invalidate` gives
// the same freeze from the other side.
//
// KEYED stores (per-identity: one entry per widget id) share one integer
// space, tagged by slot: `id * slot-count + slot`. `slot-count` is DERIVED
// from `keyed-slots` below, so adding a store cannot overflow into a
// neighbouring id's channels -- the old hand-written `id*4+k` was full at
// four stores and a fifth would have silently aliased. SINGLETON stores (one
// global value: hover, focus, ...) get reserved NEGATIVE channels, which
// never collide with the non-negative keyed space (ids are minted from a
// monotonic counter -- see keytrie's `kt-child-id` -- so they are >= 0).
// Channels are recomputed from ids every frame and never persisted, so the
// numbering is free to change between builds.
//
// ADDING A KEYED STORE -- do all four, or memoization breaks silently:
//   1. add a slot constant here AND to `keyed-slots`
//   2. `record(keyed-chan(id, <slot>))` in the getter
//   3. `invalidate(keyed-chan(id, <slot>))` in EVERY setter
//   4. drop the store's entry in `drop-ids` (its edges are handled for you,
//      since `drop-ids` walks `keyed-slots`)
// `test/ui/async-store.kk` has the memo-tracking regression to copy.

val cell-slot   = 0
val field-slot  = 1
val scroll-slot = 2
val async-slot  = 3
// every keyed slot, in one place: the channel multiplier and `drop-ids`'
// edge cleanup are both derived from this, so they can never disagree
val keyed-slots = [cell-slot, field-slot, scroll-slot, async-slot]

fun keyed-chan( id : int, slot : int ) : int
  id * keyed-slots.length + slot

val hover-chan = -1
val press-chan = -2
val focus-chan = -3
val caret-chan = -4
val clock-chan = -5

// install the store as handler-local state (the runtime calls this once,
// around everything: mount, strands, backends)
pub fun with-uistate( action : () -> <uistate,div|e> a ) : <div|e> a
  var cells   : int32-map<any>    := int32-map/empty()
  var fields  : int32-map<string> := int32-map/empty()
  var scrolls : int32-map<scroll-info> := int32-map/empty()
  var hovered := Nothing
  var pressed := Nothing
  var focused := Nothing
  var caret   := True
  var clock   := 0.0
  var frame-flag  := False
  var manual-bars : list<int> := []
  var scene-tree : maybe<any> := Nothing
  var scope-rects : list<(string,(float64,float64,float64,float64))> := []
  var metrics : list<(string,(float64,float64))> := []
  // memo machinery
  var memos   : int32-map<any>       := int32-map/empty()   // boundary id -> built widget
  var bstack  : list<int>            := []                  // read-attribution stack
  var edges   : int32-map<int32-set> := int32-map/empty()   // channel -> reader boundary ids
  var redges  : int32-map<list<int>> := int32-map/empty()   // reader -> channels (re-tracking)
  var pending : int32-set            := int32-set/empty()   // readers to mark dirty
  var pcount  := 0
  var pepoch  := 0
  var storm   := True                                       // first frame: everything builds
  var bviews  : int32-map<list<any>> := int32-map/empty()   // boundary id -> its recorded views (erased) this frame
  var bparent : int32-map<int>       := int32-map/empty()   // boundary id -> parent boundary id (nesting)
  var bhits   : int32-set            := int32-set/empty()   // boundary ids that HIT this frame
  var asyncs  : int32-map<async-entry> := int32-map/empty() // async-computation load state, per identity
  fun record( chan : int )
    match bstack
      Cons(k, _) ->
        val cset = edges.lookup(chan.int32).default(int32-set/empty())
        if !cset.member(k.int32) then
          edges := edges.set(chan.int32, cset.insert(k.int32))
          redges := redges.set(k.int32, Cons(chan, redges.lookup(k.int32).default([])))
      Nil -> ()
  fun invalidate( chan : int )
    if !storm then
      val readers = edges.lookup(chan.int32).default(int32-set/empty())
      readers.list.foreach fn(r)
        if !pending.member(r) then
          pending := pending.insert(r)
          pcount := pcount + 1
      if pcount > storm-threshold then storm := True
  // is `id` a hit boundary, or nested (transitively) inside one? A boundary
  // that hits short-circuits its whole subtree: descendants' recorded views
  // must replay too even though the descendant boundary itself never ran
  // (and so is not itself in `bhits`) this frame. Walks the parent chain
  // recorded by `memo-begin` (persists across frames, so it is correct even
  // for a hit boundary whose descendants did not run this frame). Pure over
  // explicit snapshots (not the handler's vars) so the recursion stays total.
  fun hit-or-under-hit( id : int32, hits : int32-set, parents : int32-map<int> ) : div bool
    if hits.member(id) then True
    else match parents.lookup(id)
      Just(p : int) -> hit-or-under-hit(int32(p), hits, parents)
      Nothing -> False
  with handler
    fun get-cell(id)
      record(keyed-chan(id, cell-slot))
      cells.lookup(id.int32)
    fun set-cell(id, v)
      invalidate(keyed-chan(id, cell-slot))
      cells := cells.set(id.int32, v)
    fun get-hover()
      record(hover-chan)
      hovered
    fun set-hover(k)
      invalidate(hover-chan)
      hovered := k
    fun get-press()
      record(press-chan)
      pressed
    fun set-press(k)
      invalidate(press-chan)
      pressed := k
    fun get-focus()
      record(focus-chan)
      focused
    fun set-focus(k)
      invalidate(focus-chan)
      pepoch := pepoch + 1
      focused := k
    fun get-field(id)
      record(keyed-chan(id, field-slot))
      fields.lookup(id.int32).default("")
    fun set-field(id, v)
      invalidate(keyed-chan(id, field-slot))
      pepoch := pepoch + 1
      fields := fields.set(id.int32, v)
    fun get-caret()
      record(caret-chan)
      caret
    fun set-caret(v)
      if caret != v then
        invalidate(caret-chan)
        pepoch := pepoch + 1
      caret := v
    fun get-clock()
      record(clock-chan)
      clock
    fun peek-clock()          clock
    fun subscribe-clock()     record(clock-chan)
    fun tick-clock(dt)
      invalidate(clock-chan)
      clock := clock + dt
    fun get-frame-flag()      frame-flag
    fun set-frame-flag(v)     frame-flag := v
    fun get-scroll(id)
      record(keyed-chan(id, scroll-slot))
      scrolls.lookup(id.int32).default(Scroll-info())
    fun set-scroll(id, info)
      invalidate(keyed-chan(id, scroll-slot))
      pepoch := pepoch + 1
      scrolls := scrolls.set(id.int32, info)
    fun list-scrolls()        scrolls.list.map(fn(kv) (kv.fst.int, kv.snd))
    fun add-manual-bar(id)
      if !manual-bars.any(fn(i) i == id) then manual-bars := Cons(id, manual-bars)
    fun get-manual-bars()     manual-bars
    fun clear-manual-bars()   manual-bars := []
    fun set-scene-tree(t)     scene-tree := Just(t)
    fun get-scene-tree()      scene-tree
    fun set-scope-rects(kvs)  scope-rects := kvs
    fun list-scope-rects()    scope-rects
    fun get-text-metrics(k)   metrics.lookup(fn(kk) kk == k)
    fun set-text-metrics(k, wh)
      metrics := Cons((k, wh), metrics)   // k is not present (callers check first)
    fun paint-epoch()         pepoch
    fun memo-get(id)          memos.lookup(id.int32)
    fun memo-put(id, w)       memos := memos.set(id.int32, w)
    fun memo-begin(id)
      // re-tracking: drop this boundary's OLD edges, then push it
      redges.lookup(id.int32).default([]).foreach fn(chan)
        match edges.lookup(chan.int32)
          Just(cset) -> edges := edges.set(chan.int32, cset.remove(id.int32))
          Nothing -> ()
      redges := redges.remove(id.int32)
      // record the parent (current head, before pushing) for transitive replay
      // expansion on a HIT (see ui/view/with-scene) and clear this boundary's
      // OLD views: a re-run re-records whatever it emits
      match bstack
        Cons(p, _) -> bparent := bparent.set(id.int32, p)
        Nil -> bparent := bparent.remove(id.int32)
      bviews := bviews.remove(id.int32)
      bstack := Cons(id, bstack)
    fun memo-end()
      bstack := bstack.drop(1)
    fun current-boundary()
      match bstack
        Cons(k, _) -> Just(k)
        Nil -> Nothing
    fun record-view(id, v)
      bviews := bviews.set(id.int32, Cons(v, bviews.lookup(id.int32).default([])))
    fun views-of(id)
      bviews.lookup(id.int32).default([]).reverse
    fun memo-note-hit(id)
      bhits := bhits.insert(id.int32)
    fun take-hit-boundaries()
      val hits = bhits
      val parents = bparent
      val ids = bviews.list.map(fn(kv) kv.fst).filter(fn(k) hit-or-under-hit(k, hits, parents)).map(fn(i) i.int)
      bhits := int32-set/empty()
      ids
    fun take-dirty-readers()
      if storm then
        pending := int32-set/empty()
        pcount := 0
        []
      else
        val ps = pending.list.map(fn(i) i.int)
        pending := int32-set/empty()
        pcount := 0
        ps
    fun dirty-storm()         storm
    fun force-storm()         storm := True
    fun clear-storm()         storm := False
    fun drop-ids(ids)
      ids.foreach fn(id)
        cells := cells.remove(id.int32)
        fields := fields.remove(id.int32)
        scrolls := scrolls.remove(id.int32)
        asyncs := asyncs.remove(id.int32)
        memos := memos.remove(id.int32)
        bviews := bviews.remove(id.int32)
        bparent := bparent.remove(id.int32)
        // as a reader: unhook from every channel it was subscribed to
        redges.lookup(id.int32).default([]).foreach fn(chan)
          match edges.lookup(chan.int32)
            Just(cset) -> edges := edges.set(chan.int32, cset.remove(id.int32))
            Nothing -> ()
        redges := redges.remove(id.int32)
        // as a source: its id-space channels die with it. Derived from
        // `keyed-slots`, so a NEW keyed store's channel is cleaned up here
        // without touching this line (see the checklist by `keyed-chan`).
        keyed-slots.foreach fn(slot)
          edges := edges.remove(keyed-chan(id, slot).int32)
        pending := pending.remove(id.int32)
    fun get-async(id)
      record(keyed-chan(id, async-slot))
      asyncs.lookup(id.int32)
    fun set-async(id, e)
      invalidate(keyed-chan(id, async-slot))
      asyncs := asyncs.set(id.int32, e)
    fun bump-async-gen(id)
      val cur = asyncs.lookup(id.int32).map(fn(e) e.gen).default(0)
      val g = cur + 1
      invalidate(keyed-chan(id, async-slot))
      asyncs := asyncs.set(id.int32, Async-entry(g, RPending))
      g
    fun reset-uistate()
      cells := int32-map/empty()
      fields := int32-map/empty()
      scrolls := int32-map/empty()
      hovered := Nothing
      pressed := Nothing
      focused := Nothing
      caret := True
      clock := 0.0
      frame-flag := False
      manual-bars := []
      metrics := []
      memos := int32-map/empty()
      bstack := []
      edges := int32-map/empty()
      redges := int32-map/empty()
      pending := int32-set/empty()
      pcount := 0
      storm := True
      bviews := int32-map/empty()
      bparent := int32-map/empty()
      bhits := int32-set/empty()
      asyncs := int32-map/empty()
  action()
