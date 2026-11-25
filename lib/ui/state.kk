/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Ephemeral per-widget state -- hover-independent UI state that is NOT app
// model state (expand/collapse, uncontrolled fields, animation progress). A
// hooks-style `use-state` gives a component a typed cell that persists across
// frames, keyed by widget identity, updated through an `on-act` thunk that the
// runtime re-renders after (see `ui/app`). Nothing here is app state.
//
// The state itself lives behind the `uistate` EFFECT (see ui/reactive): one
// store record held as local state by the handler `ui/app` installs -- no
// module globals. This module is the TYPED API over that store.
//
// Type-safety: values live erased in one keyed store, but every USE site is
// fully typed -- the cell and its transition are manufactured together and the
// value's type pins the transition (`f : a -> a`). The single `from-any` cast
// is confined to this module and sound under the invariant "one key is only
// ever used at one type" (the same footing as any typed hook library).
//
// Identity: `use-state` keys by the ambient widget path `?key` plus the source
// line of the call (`?kk-line`, compiler-supplied) -- so there is NO
// call-order rule like other hook systems, and two `use-state`s in one
// component are distinct because they sit on different lines. A component
// propagates `?key` by declaring it; `child-key`/`scope`/`idx` extend the path.
module ui/state

import std/async
import std/core/undiv   // pretend-no-div: the anchor walk terminates on a finite tree
import std/core/unsafe
import std/num/float64
import std/num/int32
import ui/keytrie   // find-ids: resolve a scroll-to selector to its owner
import ui/widget
pub import ui/reactive // the uistate effect + store (handler installed by the runtime)
pub import ui/ident    // identity (?key node id + child-key/scope/idx), re-exported
pub import ui/keytrie  // segments + the keytree effect (handler installed by the runtime)

// ----------------------------------------------------------------
// typed cells: a phantom-typed key lifts the value type into the store's API,
// so entries are key/value type-paired BY CONSTRUCTION. The only coercion lives
// in `cell-lookup`, guarded by key-id equality: a `cell-key<a>` matches only a
// value stored under the same id. Koka has no type-equality witness across the
// erased store, so this one cast is unavoidable; the point of `cell-key<a>` is
// to make it the ONLY one and keep every public signature fully typed.

inline extern to-any( x : a ) : any
  inline "#1"
inline extern from-any( x : any ) : a
  inline "#1"

// generic chokepoints: the inline casts are only sound at a POLYMORPHIC
// boundary (the generic calling convention boxes); calling them at a
// concrete datatype miscompiles on the C backend
pub noinline fun erase<a>( x : a ) : any
  to-any(x)
pub noinline fun unerase<a>( x : any ) : a
  from-any(x)

// a key naming a cell of value-type `a`. The `a` is phantom: only the id
// exists at runtime. Built by `use-state` from the widget identity.
pub value struct cell-key<a>( id : int )

fun cell-lookup( k : cell-key<a> ) : uistate maybe<a>
  get-cell(k.cell-key/id).map(fn(v) from-any(v))

fun cell-put( k : cell-key<a>, v : a ) : uistate ()
  set-cell(k.cell-key/id, to-any(v))

// clear all ephemeral state (e.g. on remount)
pub fun reset-state() : uistate ()
  reset-uistate()

// ----------------------------------------------------------------
// async-phase store: the load state of an async computation, per identity
// (`raw-phase`/`async-entry` are defined in ui/reactive, re-exported via the
// `pub import` above). The future-boundary async widget (deferred) reads
// `async-phase`/`current-async-gen` at build time to decide whether to kick a
// pump strand; the pump strand writes the result through `set-async-phase`
// and a stale caller retries through `retry-async` (bumps the generation and
// resets the entry to RPending -- a strand that finishes at an older
// generation is discarded by the boundary rather than applied).

// this identity's async slot, or `Nothing` if never started
pub fun async-phase( id : int ) : uistate maybe<async-entry>
  get-async(id)

// this identity's current generation (0 if never started) -- the build
// compares this against the generation an in-flight strand is running to
// decide whether that strand's eventual result is still wanted
pub fun current-async-gen( id : int ) : uistate int
  get-async(id).map(fn(e) e.gen).default(0)

// publish a phase transition (RPending/RDone/RFailed) at generation `gen`;
// enqueued through the transition channel like any other write (see
// `emit-transition`) so it lands via `drain-state` and re-renders
pub fun set-async-phase( id : int, gen : int, phase : raw-phase ) : <uistate,ioc> ()
  emit-transition(fn() set-async(id, Async-entry(gen, phase)))

// discard the current (or in-flight) result and start a fresh generation:
// bumps the generation and resets the entry to RPending -- the basis for
// stale-result discard (a strand still running the OLD generation checks
// `current-async-gen` before applying and no-ops if it has been superseded)
pub fun retry-async( id : int ) : <uistate,ioc> ()
  emit-transition(fn() { bump-async-gen(id); () })

// ----------------------------------------------------------------
// the state channel: a msg-free channel of transitions (thunks that mutate the
// store). A `use-state` setter writes to it; the runtime's `drain-state` strand
// applies each transition and re-renders (see `ui/app`). This is how a write
// from anywhere -- a click's `on-act`, an animation tick, a background task --
// reaches the render loop WITHOUT going through the app's typed msg channel.
// Runtime WIRING (not state): created by the runtime, installed here, read by
// the setters -- the one deliberate module global left in this layer.

val state-ch : ref<global, maybe<channel<() -> <uistate,ioc> ()>>> = unsafe-total{ ref(Nothing) }

// the runtime installs its transition channel here on startup
pub fun install-state-channel( ch : channel<() -> <uistate,ioc> ()> ) : ioc ()
  val r = state-ch
  r := Just(ch)

// enqueue a transition; if no runtime is installed yet (e.g. a unit test),
// apply it synchronously so `use-state` still works standalone
fun emit-transition( g : () -> <uistate,ioc> () ) : <uistate,ioc> ()
  match !state-ch
    Just(ch) -> ch.emit-io(g)
    Nothing  -> g()

// ask the runtime to re-render the current model (no state change). Used by the
// backends on a window resize so layout re-runs at the new size.
pub fun request-render() : <uistate,ioc> ()
  emit-transition(fn() ())

// ----------------------------------------------------------------
// interaction state: hover / press by widget identity. Only one element is
// hovered (and one pressed) at a time -- the local primary pointer -- so a
// single key each; multi-cursor / multi-selection is app state. Backends write
// these on pointer events (web listeners, native pump); `interactive` reads
// them and rebuilds, so a hover can change ANY visual, not just a color.

pub fun is-hovered( k : int ) : uistate bool
  get-hover().map(fn(h) h == k).default(False)
pub fun is-pressed( k : int ) : uistate bool
  get-press().map(fn(p) p == k).default(False)

// WHERE the press landed, in the pressed element's OWN coordinates (0,0 = its
// top-left). An ink ripple starts at the touch point, and that is the only
// thing this is for.
//
// A plain ref, deliberately, not a tracked store. The point changes at exactly
// one instant: the same `set-pressed` that changes the pressed KEY, which is a
// tracked write and already invalidates and re-renders. A store of its own
// would add a second dependency channel carrying no information the press
// channel does not already carry (see design-notes 17 on what adding a store
// costs).
//
// The constraint that buys: read this only where the press key is ALSO read.
// A reader that depends on the point without depending on the press is
// untracked, and would sit on a stale value inside a memo boundary -- the same
// silent-staleness failure a missing `record` produces, just arrived at from a
// different direction.
val press-point-ref : ref<global,(float64,float64,float64)> = unsafe-total{ ref((0.0, 0.0, 0.0)) }

// Set by a backend pointer handler, alongside `set-pressed`. Stamps the
// ANIMATION clock (not `ticks`), so the timestamp stays comparable to
// `anim-time()` and slow motion stretches a press-driven effect like everything
// else.
//
// `request-frame` here is load-bearing: the clock only advances while frames
// run, so on a press arriving into a settled app it would otherwise sit frozen
// at its last value and any effect measuring "time since the press" would read
// zero forever. Asking for a frame at the press is what starts it moving.
pub fun set-press-point( x : float64, y : float64 ) : <uistate,ioc> ()
  val r = press-point-ref
  r := (x, y, anim-time())
  request-frame()

// where and WHEN the last press landed: (x, y, anim-time-at-press)
pub fun press-point() : ioc (float64, float64, float64)
  !press-point-ref

// set the hovered / pressed element (from a backend pointer handler) and
// re-render so the interactive rebuilds with the new state
pub fun set-hovered( k : maybe<int> ) : <uistate,ioc> ()
  emit-transition fn()
    set-hover(k)
pub fun set-pressed( k : maybe<int> ) : <uistate,ioc> ()
  emit-transition fn()
    set-press(k)

// clear only if `k` is the current one (so leaving A after entering B, whatever
// the event order, never clears B) -- the web mouseleave/mouseup path
pub fun clear-hovered( k : int ) : <uistate,ioc> ()
  emit-transition fn()
    if is-hovered(k) then set-hover(Nothing)
pub fun clear-pressed( k : int ) : <uistate,ioc> ()
  emit-transition fn()
    if is-pressed(k) then set-press(Nothing)

// the currently hovered key (for the native pump to detect changes)
pub fun get-hovered() : uistate maybe<int>
  get-hover()

// ----------------------------------------------------------------
// focus: which widget receives KEYBOARD input. Exactly one (or none) at a
// time, like hover/press. Backends set it on click (click-to-focus) and route
// key/char events to handlers registered under the focused key; Tab traversal
// is a follow-up. Focus persists until something else takes it or it is
// cleared (clicking empty space blurs).

pub fun is-focused( k : int ) : uistate bool
  get-focus().map(fn(f) f == k).default(False)

// set (or clear, with Nothing) the focused element and re-render; the caret
// snaps solid on every focus change
pub fun set-focused( k : maybe<int> ) : <uistate,ioc> ()
  emit-transition fn()
    set-focus(k)
    set-caret(True)

// clear only if `k` is the current one
pub fun clear-focused( k : int ) : <uistate,ioc> ()
  emit-transition fn()
    if is-focused(k) then set-focus(Nothing)

pub fun get-focused() : uistate maybe<int>
  get-focus()

// ----------------------------------------------------------------
// UNCONTROLLED text-field values, by widget identity. The app model never sees
// keystrokes: the backend writes here as the user types (via the transition
// channel, so each edit re-renders), and the app READS a value at decision
// points (e.g. a submit click computing its message with `act-msg`).

// the current text of field `k` ("" if never edited)
pub fun field-text( k : int ) : uistate string
  get-field(k)

// write field `k` (backend, on key events) and re-render
pub fun set-field-text( k : int, v : string ) : <uistate,ioc> ()
  emit-transition fn()
    set-field(k, v)

// EDIT field `k`: the current value is read INSIDE the queued transition, so
// a burst of edits in one input batch (fast typing, paste, synthetic events)
// cannot lose keystrokes to a stale read -- each transition sees the one
// before it applied. (Reading at the call site and queueing the write drops
// all but the last edit of a batch; ui/test-live caught exactly that.)
pub fun edit-field-text( k : int, f : string -> string ) : <uistate,ioc> ()
  emit-transition fn()
    set-field(k, f(get-field(k)))

// read field `k` AT TRANSITION TIME and hand it on (e.g. Enter emitting the
// committed value after every queued edit has applied)
pub fun with-field-text( k : int, action : string -> <uistate,ioc> () ) : <uistate,ioc> ()
  emit-transition fn()
    action(get-field(k))

// ----------------------------------------------------------------
// caret blink: the simplest animation, driven exactly the way the state
// channel was designed for -- the runtime's blink strand toggles the phase
// (each toggle is a transition, so it re-renders) while something is focused,
// and sleeps cheaply otherwise. Typing resets the phase to SOLID (standard
// caret behavior: the caret never blinks away mid-keystroke).

// is the caret visible this frame? (painters; True whenever phase is on)
pub fun caret-visible() : uistate bool
  get-caret()

// toggle the phase (the runtime blink strand; a transition -> re-render)
pub fun toggle-caret() : <uistate,ioc> ()
  emit-transition fn()
    set-caret(!get-caret())

// snap the caret solid (on focus and on every edit)
pub fun reset-caret() : <uistate,ioc> ()
  if !caret-visible() then
    emit-transition fn()
      set-caret(True)

// ----------------------------------------------------------------
// the animation clock: a demand-driven frame ticker. Builders that have an
// UNSETTLED animation call `request-frame()`; the runtime's anim-driver strand
// (blocked on the frame channel) waits a frame, advances the clock (a
// transition, so it re-renders), and the re-render either requests again
// (still animating) or does not (settled / unmounted) -- self-healing demand,
// no release bookkeeping. When nothing requests, the driver blocks idle.

val frame-ch : ref<global, maybe<channel<()>>> = unsafe-total{ ref(Nothing) }

// the current animation time in ms (builders; advances only while animating).
// UNRECORDED on purpose: reading the time must not subscribe the enclosing
// memo boundary to the clock -- 150 settled hover-fades would otherwise pin
// their boundary dirty whenever ANYTHING animates. The clock dependency is
// registered by `request-frame` (below), i.e. exactly while unsettled.
pub fun anim-time() : uistate float64
  peek-clock()

// SLOW-MOTION, for looking at an animation rather than using it (Flutter calls
// this `timeDilation`). 1.0 is real time; 8.0 makes every animation take eight
// times as long.
//
// It scales TIME, not the frame rate: frames keep arriving at the usual pace,
// so what you see is the same curve stretched out, still smooth. Slowing the
// fps instead would show you a stutter and tell you nothing about the easing.
//
// The dilation is applied where the clock is ADVANCED (ui/app's `anim-driver`
// divides its delta by this), not where it is read -- so every `animate` and
// `animate-color` cell slows together, with no change to `anim-time`'s
// signature and nothing for a widget to opt into.
val time-dilation-ref : ref<global,float64> = unsafe-total{ ref(1.0) }

// `factor` is clamped to at least 1.0: this is a debug aid for SLOWING things
// down, and a factor below 1 would speed animations past real time, which is
// not something worth supporting by accident.
pub fun set-time-dilation( factor : float64 ) : ioc ()
  val r = time-dilation-ref
  r := factor.max(1.0)

pub fun time-dilation() : ioc float64
  !time-dilation-ref

// the runtime installs the frame-request channel its anim-driver BLOCKS on
pub fun install-frame-channel( ch : channel<()> ) : <uistate,ioc> ()
  val r = frame-ch
  r := Just(ch)
  // demand can PRE-DATE installation (the mount build runs first): deliver it
  if get-frame-flag() then ch.emit-io(())

// ask for another frame (an unsettled animation). The flag coalesces the many
// requests of one build into ONE wake of the driver.
pub fun request-frame() : <uistate,ioc> ()
  subscribe-clock()   // wake this boundary on the tick it asked for
  if !get-frame-flag() then
    set-frame-flag(True)
    match !frame-ch
      Just(ch) -> ch.emit-io(())
      Nothing  -> ()

// the driver: consume the request flag (True = someone wants a frame)
pub fun take-frame-request() : uistate bool
  val v = get-frame-flag()
  set-frame-flag(False)
  v

// advance the clock by `dt` ms and re-render (the driver, once per frame)
pub fun anim-tick( dt : float64 ) : <uistate,ioc> ()
  emit-transition fn()
    tick-clock(dt)

// ----------------------------------------------------------------
// easing: plain functions over normalized time t in [0,1]

pub alias easing = float64 -> float64

pub fun linear( t : float64 ) : float64
  t
pub fun ease-in( t : float64 ) : float64
  t * t * t
pub fun ease-out( t : float64 ) : float64
  val u = 1.0 - t
  1.0 - u * u * u
pub fun ease-in-out( t : float64 ) : float64
  if t < 0.5 then 4.0 * t * t * t
  else 1.0 - 8.0 * (1.0 - t) * (1.0 - t) * (1.0 - t) / 2.0

// an animation cell: where we started, where we are going, and when we left
pub struct anim-cell( from : float64, to : float64, start : float64 )

// A value that MOVES: returns the current interpolated value, easing toward
// `target` over `duration` ms. Retargeting mid-flight starts from the current
// position (no jump). Keyed like use-state (ambient ?key + this call site), so
// each call site animates independently. While unsettled it requests frames;
// settled or unmounted, it goes quiet and the app stops re-rendering.
pub fun animate( target : float64, duration : float64 = 200.0, ease : easing = ease-out,
                 ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> float64
  val now = anim-time()
  // QUIET cell: the retarget write happens mid-build and the requested next
  // frame reads it -- a transition here would render an identical echo frame
  val (cell, set-cell) = use-state-quiet(Anim-cell(target, target, now - duration),
                                         ?key = ?key, ?kk-file-line = ?kk-file-line)
  val t = if duration <= 0.0 then 1.0 else ((now - cell.start) / duration).min(1.0).max(0.0)
  val cur = cell.from + (cell.to - cell.from) * ease(t)
  if cell.to != target then          // retarget: continue from the current position
    set-cell(fn(_) Anim-cell(cur, target, now))
    request-frame()
    cur
  elif t < 1.0 then
    request-frame()
    cur
  else target

// an animating color cell (see `animate`: same shape, color-typed)
pub struct color-anim( from : color, to : color, start : float64 )

// A color that MOVES: eases toward `target`, retargeting from the CURRENT mix
// (hover in/out mid-transition never jumps). Keyed like use-state.
pub fun animate-color( target : color, duration : float64 = 200.0, ease : easing = ease-out,
                       ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> color
  val now = anim-time()
  val (cell, set-cell) = use-state-quiet(Color-anim(target, target, now - duration),
                                         ?key = ?key, ?kk-file-line = ?kk-file-line)
  val t = if duration <= 0.0 then 1.0 else ((now - cell.start) / duration).min(1.0).max(0.0)
  val cur = cell.from.color/mix(cell.to, ease(t))
  if !cell.to.color/same(target) then
    set-cell(fn(_) Color-anim(cur, target, now))
    request-frame()
    cur
  elif t < 1.0 then
    request-frame()
    cur
  else target

// ----------------------------------------------------------------
// scroll state, keyed by scroll-region identity (the widget path + line of the
// `scroll` call, or an explicit `name`). A region's state is its scroll offset
// plus the content and viewport heights -- enough for a SCROLLBAR widget to
// draw a thumb and for `use-state`-style subscription: read `scroll-state(k)`
// in a build and it re-renders when the offset changes. The native backend
// owns writes. (`scroll-info` itself is defined in ui/reactive.)

// the full scroll state of region `k` (a zeroed default if never seen)
pub fun scroll-state( k : int ) : uistate scroll-info
  get-scroll(k)

// every known scroll region with its metrics -- the scene composer walks these
// to auto-emit a scrollbar view for each region that overflows
pub fun all-scroll-states() : uistate list<(int,scroll-info)>
  list-scrolls()

// regions that already have a MANUAL `scrollbar(...)` placed this frame; the
// auto-scrollbar pass skips them (manual placement wins). Registered during the
// view build, cleared by the scene composer before each build.
pub fun register-manual-scrollbar( k : int ) : uistate ()
  add-manual-bar(k)

pub fun manual-scrollbar-keys() : uistate list<int>
  get-manual-bars()

pub fun clear-manual-scrollbars() : uistate ()
  clear-manual-bars()

// the current scroll offset for region `k` (0 if never scrolled)
pub fun scroll-offset( k : int ) : uistate float64
  scroll-state(k).offset

// set region `k`'s scroll offset (the caller clamps to [0, content - viewport])
pub fun set-scroll-offset( k : int, v : float64 ) : uistate ()
  set-scroll(k, get-scroll(k)(offset = v))

// record region `k`'s measured metrics (backend, at paint/layout time)
pub fun publish-scroll-metrics( k : int, content : float64, viewport : float64 ) : uistate ()
  set-scroll(k, get-scroll(k)(content = content, viewport = viewport))

// keep ui/state's per-region scroll metrics in step with the laid-out tree.
// Returns whether anything changed (so the caller can re-view -- a scrollbar
// reads these at build time).
pub fun sync-scroll-metrics<msg>( t : ltree<msg> ) : <uistate,ioc> bool
  val changed = ref(False)
  t.each-scroll fn(key, contenth, vh)
    val s = scroll-state(key)
    if s.content != contenth || s.viewport != vh then
      publish-scroll-metrics(key, contenth, vh)
      changed := True
  !changed

// write each scroll region's current ui/state offset (clamped to its content)
// into its LScroll node. Native only; the offset drives both paint and hit.
// The pending scroll-to-anchor request: a SELECTOR string (ui/keytrie's
// grammar -- a section's `?key = scope(slug)` makes the slug a selector), or
// Nothing. A plain ref: the request only matters at the next bake, which the
// paired `request-render` guarantees happens.
val anchor-ref : ref<global, maybe<string>> = unsafe-total{ ref(Nothing) }

// Scroll so the widget named by `sel` sits at the top of its enclosing scroll
// region -- the cross-page "#anchor" primitive, portable because it goes
// through ui/state's scroll offsets rather than any browser behaviour.
//
// Resolution happens inside `bake-scroll`, which every backend (and the test
// harness) already runs between layout and paint -- so a navigation that sets
// a route AND an anchor scrolls in the SAME frame the new page first paints:
// no land-at-top-then-jump. The request stays pending while the selector
// matches nothing (the target page may not be built yet -- e.g. an animation
// frame slips in between the navigate and the route re-render) and is
// consumed the moment it resolves; a bad slug therefore pends until the next
// `scroll-to` overwrites it, which is the cheap failure mode.
// `ioc` ONLY, deliberately: the ref write and the empty-transition post are
// channel mechanics, and keeping uistate out of the row lets a router SUB
// (which runs outside the uistate handler on the threaded runtime) request
// anchors. With no runtime installed there is no render loop to poke -- the
// pending request still resolves at the next bake, which is all a headless
// caller needs.
pub fun scroll-to( sel : string ) : ioc ()
  val r = anchor-ref
  r := Just(sel)
  match !state-ch
    Just(ch) -> ch.emit-io(fn() ())    // an empty transition: re-render only
    Nothing  -> ()

// Consume the pending anchor against THIS laid-out tree, if it resolves.
//
// "Resolves" means present IN THE TREE, not merely known to the keytree: the
// registry retains ids for widgets that are no longer mounted (a page you
// visited and left), and a stale id must not consume the request -- the docs
// site hit exactly that, a cross-page anchor silently swallowed when its
// target page had been visited before. So the id that consumes is the first
// find-ids match the tree actually contains; with none mounted the request
// keeps pending for the render that mounts one.
fun resolve-anchor<msg>( t : ltree<msg> ) : <keytree,uistate,ioc> ()
  match !anchor-ref
    Just(sel) ->
      val mounted = find-ids(sel).filter(fn(id) pretend-no-div( fn() t.owner-present(id) ))
      match mounted
        Cons(id, _) ->
          val r = anchor-ref
          r := Nothing            // the target is MOUNTED: consume, scroll if geometry allows
          match pretend-no-div( fn() t.scroll-anchor-pos(id) )
            Just((key, y, content, vp)) ->
              set-scroll-offset(key, y.min((content - vp).max(0.0)).max(0.0))
            Nothing -> ()         // mounted but not inside a vertical scroll: nothing to do
        Nil -> ()                 // not mounted (or not built) yet: keep pending
    Nothing -> ()

pub fun bake-scroll<msg>( t : ltree<msg> ) : <keytree,uistate,ioc> ltree<msg>
  resolve-anchor(t)   // BEFORE baking, so the jump paints this same frame
  t.bake-go

fun bake-go<msg>( t : ltree<msg> ) : <uistate,ioc> ltree<msg>
  match t
    LScroll(o, key, w, h, content, _, horizontal, child) ->
      val vp = if horizontal then w else h   // viewport ALONG the scroll axis
      val off = scroll-offset(key).max(0.0).min((content - vp).max(0.0))
      LScroll(o, key, w, h, content, off, horizontal, child.bake-go)
    LField(o, key, _, ph, onenter, w, h) -> LField(o, key, field-text(key), ph, onenter, w, h)
    LActMsg(o, g, w, h, dx, dy, child) -> LActMsg(o, g, w, h, dx, dy, child.bake-go)
    LBox(o, bg, on, w, h, dx, dy, child) -> LBox(o, bg, on, w, h, dx, dy, child.bake-go)
    LLink(o, to, w, h, dx, dy, child) -> LLink(o, to, w, h, dx, dy, child.bake-go)
    LAct(o, a, w, h, dx, dy, child) -> LAct(o, a, w, h, dx, dy, child.bake-go)
    LRotate(o, deg, w, h, child) -> LRotate(o, deg, w, h, child.bake-go)
    LMemo(o, mid, srcw, lc, child) -> LMemo(o, mid, srcw, lc, child.bake-go)
    LInteractive(o, k, oc, s, w, h, dx, dy, child) -> LInteractive(o, k, oc, s, w, h, dx, dy, child.bake-go)
    LFlex(o, w, h, kids) -> LFlex(o, w, h, kids.map(fn(e) (e.fst, e.snd, e.thd.bake-go)))
    LLayer(o, w, h, kids) -> LLayer(o, w, h, kids.map(fn(e) (e.fst, e.snd, e.thd.bake-go)))
    other -> other

// apply an accumulated wheel delta to a scroll region under (x,y). Prefers
// the nearest region on the axis the gesture is ACTUALLY driving (a
// vertical wheel drives a vertical region, a horizontal trackpad swipe
// drives a horizontal one) over the innermost region regardless of axis --
// so a vertical wheel tick that starts over a nested horizontal scroll (a
// code block, a carousel) still reaches an enclosing vertical scroll rather
// than being trapped by whichever region happens to be under the cursor.
// Only when NO region on the scene under the cursor matches the gesture's
// axis does the innermost region fall back to consuming it on its own axis
// (dx as its horizontal delta, or vice versa) -- preserving the original
// "plain vertical wheel still scrolls a carousel with no vertical scroll
// around it" behavior for a true standalone horizontal carousel. Returns
// True iff a region's offset changed (the caller re-renders on True --
// through `request-render`, not just a repaint, so a linked scrollbar
// rebuilds with the new offset and the content re-lays-out at the offset).
pub fun apply-wheel<msg>( t : ltree<msg>, x : float64, y : float64,
                          dx : float64, dy : float64 ) : <uistate,ioc,exn> bool
  if dx == 0.0 && dy == 0.0 then False else
    val regions = t.scroll-at(x, y)
    val wants-horizontal = dx != 0.0
    val picked = match regions.find(fn(r) match r { (_,_,_,h) -> h == wants-horizontal } )
      Just((key, content, vp, horizontal)) -> Just((key, content, vp, horizontal, True))   // axis match: use its own axis
      Nothing -> match regions
        Cons((key, content, vp, horizontal), _) -> Just((key, content, vp, horizontal, False))  // fall back to the innermost
        Nil -> Nothing
    match picked
      Just((key, content, vp, horizontal, matched)) ->
        val delta  = if matched then (if horizontal then dx else dy)
                     else (if horizontal then (if dx != 0.0 then dx else dy) else dy)
        val cur    = scroll-offset(key)
        val maxoff = (content - vp).max(0.0)
        val next   = (cur - delta).max(0.0).min(maxoff)   // wheel-up (delta>0) reveals earlier content
        if next != cur then
          set-scroll-offset(key, next)
          True
        else False
      Nothing -> False

// ----------------------------------------------------------------
// the last-published MAIN scene tree (erased `ltree<a>`), one frame behind --
// `Scope`/Panel targets (ui/view) resolve owner geometry against it via
// `owner-rect`. Published by the backend right after each layout+bake.

pub fun publish-scene-tree( t : any ) : uistate ()
  set-scene-tree(t)

pub fun current-scene-tree() : uistate maybe<any>
  get-scene-tree()

// ----------------------------------------------------------------
// resolved Scope-anchored view rects: (view key, its resolved owner rect),
// republished once per `raw-scene/finish` (ui/view) with exactly the entries
// that resolved THIS frame (a not-yet-resolved target is simply absent, so
// its first appearance still changes the snapshot). This is what the backend
// hashes into `anchor-sig` to decide "re-render once more".

// publish this frame's resolved Scope-view rects (ui/view/raw-scene/finish)
pub fun publish-scope-rects( kvs : list<(string,(float64,float64,float64,float64))> ) : uistate ()
  set-scope-rects(kvs)

// a snapshot of all resolved Scope-view rects (the backend's resettle trigger reads this)
pub fun all-scope-rects() : uistate list<(string,(float64,float64,float64,float64))>
  list-scope-rects()

// ----------------------------------------------------------------
// text-metrics cache: shaping text is the expensive part of layout and most
// strings are identical frame after frame. Backends wrap their `measure`
// handler with this -- identical (content,font,max-width) asks hit the cache
// behind the uistate effect (the handler owns representation + eviction).

pub fun measure-cached( content : string, font : font, max-w : float64,
                        measure : () -> <uistate,ioc> (float64, float64) ) : <uistate,ioc> (float64, float64)
  val k = content ++ "\x01" ++ font.css-font ++ "\x01" ++ max-w.show
  match get-text-metrics(k)
    Just(wh) -> wh
    Nothing ->
      val wh = measure()
      set-text-metrics(k, wh)
      wh

// ----------------------------------------------------------------
// MEMOIZATION (the a-prime design; see samples/ui/aprime). `memo` establishes
// a boundary at this call site's identity: while no state its subtree READ
// has been written (subtree-dirty bit in the keytrie) it returns the CACHED
// widget -- the same pointer, so reconcile skips the subtree's relayout via
// ptr-eq. Reads inside the builder auto-track (no dependency lists); model-
// message renders force a full rebuild (dirty storm), so only uistate reads
// need tracking. The builder receives the boundary's key: derive ALL inner
// identities from it (subtree-dirt must live under this node).

pub fun memo<msg,e>( build : (key) -> <keytree,uistate,ioc|e> widget<msg>,
                     ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc|e> widget<msg>
  val k = kt-child(?key, Slot("m", ?kk-file-line))
  val id = k.key-id
  if !dirty-storm() && !kt-subtree-dirty(id) then
    match memo-get(id)
      Just(w) ->
        memo-note-hit(id)   // views recorded under this boundary (or nested inside it)
                            // must replay this frame: the cache hit skips the build
                            // that would otherwise re-emit them (see ui/view)
        Memo(id.int32, id, unerase(w))
      Nothing -> memo-run(id, k, build)
  else memo-run(id, k, build)

fun memo-run<msg,e>( id : int, k : key, build : (key) -> <keytree,uistate,ioc|e> widget<msg> ) : <keytree,uistate,ioc|e> widget<msg>
  memo-begin(id)
  kt-open(id)          // children -> stale; the build's descends claim survivors
  val w = build(k)
  // unclaimed stale = unmounted: KeepAlive subtrees move to the retained
  // store (state intact until the same path remounts); Transient subtrees
  // prune, and their ids are dropped from the state store too
  val pruned = kt-close(id)
  if !pruned.is-nil then drop-ids(pruned)
  memo-end()
  kt-clean-dirty(id)
  memo-put(id, erase(w))
  Memo(id.int32, id, w)

// renderer hooks (ui/app): flush pending dirty readers into the keytrie's
// subtree bits BEFORE building; clear the storm flag after the frame; force
// a storm for model-message renders.
pub fun flush-dirty() : <keytree,uistate,ioc> ()
  take-dirty-readers().foreach(fn(id) kt-mark-dirty(id))
pub fun frame-done() : uistate ()
  clear-storm()
pub fun invalidate-frame() : uistate ()
  force-storm()

// the interaction state a builder sees
pub struct interaction
  hovered  : bool = False
  pressed  : bool = False
  focused  : bool = False
  disabled : bool = False

// An interactive region: owns the click, tracks hover/press by widget identity,
// and builds its content from the LIVE interaction state. State flows through
// ui/state and re-renders, so `build` can change any visual (color, border,
// even structure). `disabled` blocks the click and is passed to the builder.
// `hit-slop` widens the hit area beyond the visual (layout-neutral) -- e.g. a
// small icon with a larger touch target.
pub fun interactive<msg>( on-click : msg, build : (interaction) -> <keytree,uistate,ioc> widget<msg>,
                          disabled : bool = False, hit-slop : float64 = 0.0,
                          ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
  val k = kt-child( ?key, Slot("i", ?kk-file-line) ).key-id
  val s = Interaction(hovered = is-hovered(k), pressed = is-pressed(k), focused = is-focused(k), disabled = disabled)
  val oc = if disabled then Nothing else Just(on-click)
  // owner = the AMBIENT identity (like a leaf), so `?key = scope("x")` names
  // the interactive as "x"; `k` (its Slot mint) stays the STATE key only.
  // Addressing and state are different concerns: state must be per-call-site
  // unique (the Slot), the addressable identity is whatever the caller scoped.
  Interactive(?key.key-id.int32, k, oc, hit-slop, build(s))

// the runtime strand: apply each queued transition, then re-render. `rerender`
// re-views the CURRENT model (the transition changed the store, not the model).
// Transitions are BATCHED: everything already queued applies before the ONE
// re-render (a drag burst or a multi-widget write costs one frame, not N).
pub fun drain-state( rerender : () -> <keytree,uistate,ioc,exn> () ) : <async,keytree,uistate,ioc,exn> ()
  match !state-ch
    Just(ch) ->
      val g = ch.receive
      g()
      drain-queued(ch)
      rerender()
      drain-state(rerender)
    Nothing -> ()

fun drain-queued( ch : channel<() -> <uistate,ioc> ()> ) : <async,uistate,ioc> ()
  match ch.try-receive
    Just(g) ->
      g()
      drain-queued(ch)
    Nothing -> ()

// apply every transition ALREADY queued, without blocking for more (unlike
// `drain-state`, which parks waiting on the next one). Used by hosts/tests
// that synchronously reset the store (e.g. ui/test-live's reset-app between
// scenarios) to flush any write in flight from BEFORE the reset -- so a
// leftover transition from the prior scenario's tail burst applies (and is
// then immediately wiped by `reset-state`) instead of landing AFTER the
// reset, against the next scenario's fresh state.
pub fun flush-pending-transitions() : <async,uistate,ioc> ()
  match !state-ch
    Just(ch) -> drain-queued(ch)
    Nothing -> ()

// ----------------------------------------------------------------
// the hook

// A typed ephemeral cell. Returns the latest value (seeding `init` on first
// use) and a transition applier `(a -> a) -> ()`. Identity is SEAMLESS: the key
// is the ambient path plus this call's source line, so `use-state(0)` just works
// and distinct call sites never collide -- no name needed. `name` is an optional
// disambiguator for the rare case of two `use-state`s on ONE source line. The
// applier mutates the cell; the runtime re-renders after running it (see `on-act`).
pub fun use-state( init : a, name : string = "", ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> (a, (a -> a) -> <uistate,ioc> ())
  val (cur, quiet) = use-state-quiet(init, name, ?key = ?key, ?kk-file-line = ?kk-file-line)
  // the setter enqueues a transition that reads the LATEST value at apply time
  // (so queued transitions compose, not clobber)
  fun apply( f : (_) -> _ ) : <uistate,ioc> ()
    emit-transition fn()
      quiet(f)
  (cur, apply)

// `use-state` whose setter writes WITHOUT scheduling a re-render: for writes
// made DURING a frame build that the next frame reads anyway (an animation
// cell's retarget, an fps meter's bookkeeping). The transition-based setter
// would re-render a second, identical frame -- on native that second present
// blocks on the Metal drawable and HALVES the animation rate.
pub fun use-state-quiet( init : a, name : string = "", ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> (a, (a -> a) -> uistate ())
  // the key's phantom type is pinned to `init`'s type via `cell-put(_, k, init)`
  val slot = kt-child( ?key, Slot("s", ?kk-file-line) )
  val k : cell-key<_> = Cell-key( (if name.is-empty then slot else kt-child(slot, Named(name))).key-id )
  val cur : _ = match cell-lookup(k)
    Just(v) -> v
    Nothing ->
      cell-put(k, init)
      init
  // `f`, `init` and the reads all sit at type `a` -- the erasure is entirely
  // inside `cell-lookup`/`cell-put`.
  fun apply( f : (_) -> _ ) : uistate ()
    val latest : _ = cell-lookup(k).default(init)
    cell-put(k, f(latest))
  (cur, apply)
