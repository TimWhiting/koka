/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The scene: a collection of positioned VIEWS. A view is a widget tree anchored
// to a target (the display, or another view / widget region by key) via
// `ui/anchor` alignments. Overlays, dropdowns, dialogs, secondary windows and
// scrollbars are ALL views -- they differ only in their target and in how the
// backend realizes them (an in-window layer, or later a real native window).
//
// Portals are an EFFECT: a widget anywhere in the main tree calls `overlay(...)`
// to emit a view into the scene, WITHOUT the app threading an entry list through
// its model. The app runtime handles `scene` (accumulating the emitted views),
// then builds them in anchor-dependency order -- a view's layout needs its
// target's RECT, so once that rect is known the view lays out (and can do so on
// another thread; the dependency is on geometry, not on paint). Ordering is
// relative: a view paints above its anchor (structural), and its `band`
// (ui/anchor) orders it against otherwise-unordered views; the default is just
// above the anchor.
module ui/view

import std/num/float64
import std/core/undiv   // pretend-no-div (owner-rect's finite-tree walk)
import ui/widget
import ui/anchor
import ui/keytrie  // root-key + find-ids: Scope targets resolve selectors through the keytree
import ui/state   // erase/unerase + the last-published scene tree (Scope targets resolve owner-rect over it)

// what a view hangs off. `Display` is the root (the whole viewport); `Scope(sel)`
// is another view/widget's OWNER geometry, addressed by selector (see
// ui/keytrie's selector-queries doc) and resolved via `owner-rect` against the
// last-published scene tree (one frame behind, like a keyed/anchored region's
// rect always was). As an internal-only convenience, auto-scrollbars and Panel
// placement pass a scroll region's DECIMAL id (`k.show`) as `sel` -- scroll
// region ids are minted separately from the selector/name trie (`scroll-key`,
// usually an unnamed `Slot` segment, which selectors can never match), so an
// all-digit `sel` is read as a literal owner id instead of being parsed as a
// selector (see `scope-rect-of`).
pub type target
  Display
  Scope( sel : string )

// how a view is anchored to its target: a point on the target, a point on the
// view, and an offset (see `ui/anchor/place`). Defaults anchor the view's
// top-left to the target's top-left (i.e. overlapping the target origin).
pub struct anchoring
  target       : target = Display
  target-align : alignment = top-left
  self-align   : alignment = top-left
  offset-x     : float64 = 0.0
  offset-y     : float64 = 0.0

// how the backend realizes a view: an in-window layer (today), a real titled
// resizable window, or a borderless non-activating panel that escapes the
// parent window's bounds. Web backends realize everything InLayer.
pub type chrome
  InLayer
  Titled( title : string, width : float64 = 480.0, height : float64 = 360.0 )
  Panel

// a positioned view in the scene: its identity (which also publishes its rect
// for others to anchor to), its content tree, how it is anchored, and its
// z-band relative to otherwise-unordered siblings. `dim` draws a translucent
// modal scrim beneath the content; `on-dismiss` (Just) makes an outside click on
// the scrim fire that message (a transparent scrim still captures the click).
// `anchor` is `Nothing` for `Titled` chrome (OS-placed); `InLayer` treats
// `Nothing` as the default `Anchoring()`; `Panel` requires `Just`.
pub struct view<a>
  key        : string
  content    : widget<a>
  anchor     : maybe<anchoring> = Nothing
  band       : band = Attached
  dim        : bool = False
  on-dismiss : maybe<a> = Nothing
  max-width  : float64 = unbounded-w   // cap the content width  (wrapping / filling content); default uncapped
  max-height : float64 = unbounded-w   // cap the content height
  chrome     : chrome = InLayer

// the portal effect: emit a view into the current scene. Handled by the app
// runtime, which collects the views and builds them in anchor order.
pub effect scene<a>
  fun emit-view( v : view<a> ) : ()

// emit an overlay view anchored to `target`. The common cases:
//  * a cursor menu:      overlay(k, menu, target = Display, offset = pt)
//  * a dropdown:         overlay(k, menu, target = Scope("btn"), target-align = bottom-left)  -- btn = ?key = scope("btn")
//  * a centered modal:   overlay(k, dialog, target = Display, target-align = center, self-align = center, band = Modal)
pub fun overlay<a>( key : string, content : widget<a>,
                      target : target = Display,
                      target-align : alignment = top-left, self-align : alignment = top-left,
                      offset-x : float64 = 0.0, offset-y : float64 = 0.0,
                      band : band = Attached, dim : bool = False, on-dismiss : maybe<a> = Nothing,
                      max-width : float64 = unbounded-w, max-height : float64 = unbounded-w,
                      chrome : chrome = InLayer ) : scene<a> ()
  emit-view( View(key, content, Just(Anchoring(target, target-align, self-align, offset-x, offset-y)),
                  band, dim, on-dismiss, max-width, max-height, chrome) )

// a titled native window as a Window-band view: OS placement (no anchoring),
// declarative lifecycle (emit = open; stop = close; close button -> on-dismiss)
pub fun window<a>( key : string, content : widget<a>, title : string,
                   width : float64 = 480.0, height : float64 = 360.0,
                   on-dismiss : maybe<a> = Nothing ) : scene<a> ()
  emit-view( View(key, content, Nothing, Window, False, on-dismiss,
                  unbounded-w, unbounded-w, Titled(title, width, height)) )

// anchoring rules per chrome (validated when the scene is composed)
fun check-chrome<a>( v : view<a> ) : exn view<a>
  match v.chrome
    Titled -> match v.anchor
      Just(_) -> throw("view '" ++ v.key ++ "': titled-window anchoring is not supported yet (pass no anchoring)")
      Nothing -> v
    Panel -> match v.anchor
      Nothing -> throw("view '" ++ v.key ++ "': a Panel view needs an anchoring")
      Just(_) -> v
    InLayer -> v

// a reliable in-layer check (auto `is-` names are unreliable across ctor casing)
fun chrome/is-in-layer( c : chrome ) : bool
  match c
    InLayer -> True
    _       -> False

// ----------------------------------------------------------------
// building the scene: collect the emitted views, then composite them over the
// main view as positioned layers. This IN-WINDOW realization reuses the single
// laid-out tree (a `stack`): each view becomes an optional dimming/dismiss scrim
// plus a `positioned` content layer, ordered by band then emission. (A future
// per-view-tree realization builds each view as its own retained tree in
// anchor-dependency order -- same model, different lowering.)

// the translucent black of a dimmed modal scrim
val scrim-color : color = Color(0.0, 0.0, 0.0, 0.4)

// run `action` under the scene handler, returning the main widget and the views
// it emitted (in emission order). Also RECORDS each emitted view under the
// innermost enclosing memo boundary (if any) -- views are a memo boundary's 4th
// cached artifact (alongside the built widget and per-backend display lists): a
// re-run re-emits (and re-records, `memo-begin` clears the old record), so what
// is recorded here is always this build's fresh truth. A boundary that HITS
// instead (see `ui/state/memo`) never re-runs `action`'s emitting code -- its
// last-recorded views are replayed by `with-scene` below, or the portal would
// vanish on the very next settle frame.
pub fun collect-views<a,e>( action : () -> <scene<a>,uistate|e> widget<a> ) : <uistate|e> (widget<a>, list<view<a>>)
  var acc := Nil
  with fun emit-view(v)
    acc := Cons(v, acc)
    match current-boundary()
      Just(b) -> record-view(b, erase(v))
      Nothing -> ()
  val main = action()
  (main, acc.reverse)

// a full-viewport scrim box that (when dim) tints the view and (when on-dismiss
// is Just) captures an outside click
fun scrim<a>( dim : bool, on-dismiss : maybe<a> ) : widget<a>
  box( column([spacer(?key = root-key)], fill = True, ?key = root-key),
       bg = if dim then Just(Fill(scrim-color)) else Nothing,
       on-click = on-dismiss, ?key = root-key )

// resolve a `Scope` selector against a (possibly absent) previously-published
// tree: an all-digit `sel` is read as a literal owner id directly (scroll
// region ids are minted outside the name/selector trie -- see `target`'s doc);
// anything else resolves through `find-ids` (first matching id that yields a
// rect wins -- an ambiguous selector silently picks one here, unlike the
// tester's `resolve1`, since a view target has no natural place to report an
// ambiguity error to)
pub fun scope-rect-of<a>( sel : string, ot : maybe<ltree<a>> ) : keytree maybe<(float64,float64,float64,float64)>
  match ot
    Nothing -> Nothing
    Just(t) ->
      val ids = match sel.parse-int
        Just(i) -> [i]
        Nothing -> find-ids(sel)
      ids.foldl(Nothing) fn(acc : maybe<(float64,float64,float64,float64)>, id)
        match acc
          Just(_) -> acc
          Nothing -> pretend-no-div( fn() t.owner-rect(id) )

// which scroll regions (present THIS frame) qualify for an AUTO scrollbar:
// overflowing, no manual bar. Whether the region's RECT is already known is
// NOT checked here -- that needs `owner-rect` over the scene tree, which
// needs `keytree`, which this function doesn't have (see `with-scene`'s doc
// on the inference wall that keeps `keytree` out of its body). The rect-known
// guard is instead applied in `raw-scene/finish` (which DOES have `keytree`),
// right before compositing: see `finish`'s `bar-ready` filter. Emitting the
// bar-shaped view here and dropping it later (rather than never emitting it)
// keeps this function simply-typed and keytree-free.
fun qualifying-bars( present : list<(int, bool)>, states : list<(int, scroll-info)>,
                     manual : list<int> ) : list<(int, scroll-info, bool)>
  present.flatmap fn((k, horizontal))
    match states.lookup(fn(kk) kk == k)
      Nothing -> []
      Just(info) ->
        if info.content > info.viewport + 0.5 && !manual.any(fn(kk) kk == k)
          then [(k, info, horizontal)] else []

// the layers one view contributes, in paint order (scrim under content)
fun view/layers<a,e>( v : view<a>, rect-of : (string) -> <keytree|e> maybe<(float64,float64,float64,float64)> ) : <keytree|e> list<widget<a>>
  val anchor = v.anchor.default(Anchoring())   // InLayer default restores today's behavior
  val mtarget = match anchor.target
    Display  -> Nothing
    Scope(k) -> rect-of(k)
  // if there is a dismiss scrim, the content must ABSORB clicks that land on it
  // (so a click on a modal's body / menu padding does not fall through and dismiss)
  val has-scrim = v.dim || v.on-dismiss.is-just
  // NOTE: `v.key` is the view's bookkeeping identity (window/scrollbar
  // dedup, `check-chrome`, etc.), not a widget-addressing identity -- unlike
  // the old string anchor registry, minting a keytrie identity from it here
  // would risk COLLIDING with whatever name the content scopes itself under
  // (a common, intentional pattern: `overlay("tip", text(..., ?key =
  // scope("tip", ...)))`). Content that wants to be test/anchor-addressable
  // scopes its OWN widgets (`?key = scope(name)`), same as anywhere else.
  val content = positioned( v.content, mtarget, anchor.target-align, anchor.self-align,
                            anchor.offset-x, anchor.offset-y, v.max-width, v.max-height,
                            absorb = has-scrim, ?key = root-key )
  if has-scrim
    then [ scrim(v.dim, v.on-dismiss), content ]
    else [ content ]

// composite the main view with its overlay views. `rect-of` resolves a Scope
// selector to its owner rect (Nothing if not yet known). With no views this
// is exactly `main`.
pub fun compose<a,e>( main : widget<a>, views : list<view<a>>,
                    rect-of : (string) -> <keytree|e> maybe<(float64,float64,float64,float64)> ) : <keytree|e> widget<a>
  match views
    Nil -> main
    _ ->
      // stable order by band priority, preserving emission order within a band
      val ordered = [Attached, Popover, Modal, Window].flatmap fn(b)
        views.filter(fn(v) v.band.priority == b.priority)
      val layers = ordered.flatmap(fn(v) v.layers(rect-of))
      stack( Cons( (0.0, 0.0, main), layers.map(fn(l) (0.0, 0.0, l)) ), ?key = root-key )

// A NEUTRAL default scrollbar (used when the app passes no themed builder): a
// semi-transparent rounded thumb over the region's edge, sized `viewport/content`
// and positioned by the offset. Purely visual (no messages), so it is polymorphic
// in the app's msg type. Style-using apps pass their themed builder to `app`.
pub fun neutral-scrollbar<a>( info : scroll-info, axis : scroll-axis ) : widget<a>
  val thumb-fill = Just(Fill(Color(0.5, 0.5, 0.55, 0.6), 3.0))
  val ratio = fn(vp, ct) if ct > 0.0 then (vp / ct).min(1.0) else 1.0
  val pos   = fn(off, mx) if mx > 0.0 then (off / mx).max(0.0).min(1.0) else 0.0
  match axis
    Vertical ->
      val th = (info.viewport * ratio(info.viewport, info.content)).max(20.0).min(info.viewport)
      val ty = (info.viewport - th) * pos(info.offset, (info.content - info.viewport).max(0.0))
      stack([ (0.0, ty, rect(6.0, th, bg = thumb-fill, ?key = root-key)) ], ?key = root-key)
    Horizontal ->
      val tw = (info.viewport * ratio(info.viewport, info.content)).max(20.0).min(info.viewport)
      val tx = (info.viewport - tw) * pos(info.offset, (info.content - info.viewport).max(0.0))
      stack([ (tx, 0.0, rect(tw, 6.0, bg = thumb-fill, ?key = root-key)) ], ?key = root-key)

// a scrollbar VIEW anchored to its region's owner rect: vertical bars hug the
// right edge (top-aligned), horizontal bars the bottom edge (left-aligned).
// `Scope(k.show)` -- the scroll id's decimal form -- is the internal id-target
// idiom `scope-rect-of` fast-paths (see `target`'s doc); a scroll region has no
// stable NAME to select by.
fun bar-view<a,e>( k : int, info : scroll-info, axis : scroll-axis,
                   build : (scroll-info, scroll-axis) -> <uistate,ioc|e> widget<a> ) : <uistate,ioc|e> view<a>
  val content = build(info, axis)
  match axis
    Vertical   -> View(k.show ++ ":vscroll", content, Just(Anchoring(Scope(k.show), top-right, top-right)), Attached)
    Horizontal -> View(k.show ++ ":hscroll", content, Just(Anchoring(Scope(k.show), bottom-left, bottom-left)), Attached)

// The app-facing composer: run `action` (which builds the main content and may
// `overlay(...)` / `emit-view(...)` from anywhere) and composite the result into
// a single `ioc widget`. `app` calls this around every view, so the `scene`
// effect is ambient during building (portals from anywhere) and the composition
// also AUTO-EMITS a scrollbar view for each overflowing scroll region that has no
// manual `scrollbar(...)` (manual placement wins). `scrollbar` builds the bar
// widget (a themed builder from the style, or the neutral default); it runs in
// the ambient effect, so a theme set around `app` themes the bar.
// the SPLIT scene result: `main` is the composited in-window tree (InLayer
// views + auto scrollbars), `windows` are the views whose chrome escapes it
// (Titled / Panel), band order preserved. Every consumer today realizes
// `windows` back into layers via `flatten` (real native windows land in a
// later task).
pub struct scene-out<a>
  main    : widget<a>
  windows : list<view<a>>     // chrome != InLayer, band order preserved

// `with-scene`'s result BEFORE `Scope` targets are resolved: the checked
// InLayer views (overlays + auto scrollbars) still need `compose`'s
// `rect-of` pass, which needs `keytree` (`find-ids`) -- a real Koka
// limitation keeps that resolution OUT of `with-scene`'s own body (see
// `raw-scene/finish`'s doc and the task report's Koka-gotchas note: mixing a
// `keytree`-only call with `with-scene`'s row-polymorphic `e` -- carried by
// the app's own `scrollbar` builder -- inside ONE explicitly-effect-typed
// function body does not unify cleanly, even though each part typechecks
// fine alone). Every caller is already an UNANNOTATED local `composed`
// wrapper that runs under `with-keytree`, so `.finish()` right after
// `with-scene(...)` is the fix: same net effect, inference just handles it
// when `keytree` is introduced by a SEPARATE, simply-typed function instead.
pub struct raw-scene<a>
  main   : widget<a>
  layers : list<view<a>>     // checked, includes auto scrollbars; InLayer only
  native : list<view<a>>     // chrome != InLayer, band order preserved

pub fun with-scene<a,e>( action : () -> <scene<a>,uistate,ioc,exn|e> widget<a>,
                         scrollbar : (scroll-info, scroll-axis) -> <uistate,ioc,exn|e> widget<a> = neutral-scrollbar ) : <uistate,ioc,exn|e> raw-scene<a>
  clear-manual-scrollbars()                 // reset the per-frame manual-bar registry
  val (main, fresh) = collect-views(action) // build (registers manual bars, emits overlays)
  // replay: memo boundaries that HIT this frame (see ui/state/memo) never ran
  // `action`'s emitting code, so their views were never re-collected above --
  // splice back in their LAST-recorded views (the boundary's 4th cached
  // artifact, alongside the built widget). `take-hit-boundaries` already
  // expands transitively to boundaries NESTED inside a hit one (an outer hit
  // short-circuits inner boundaries too, so their recorded views must replay
  // even though the inner boundary itself never ran/hit this frame). One
  // erased-cast chokepoint (`unerase`), same discipline as the memo widget
  // cache. Ordering: replayed views are appended AFTER fresh emissions --
  // `compose`'s band-then-emission-order already governs stacking, so within a
  // band replayed views sort by boundary id, an accepted approximation (exact
  // interleaving with fresh emissions is not reconstructed).
  fun unerase-view( v : any ) : view<a>
    unerase(v)
  val replayed = take-hit-boundaries().flatmap(fn(b) views-of(b).map(unerase-view))
  val views = fresh ++ replayed
  // auto scrollbars: for each scroll region present THIS frame that overflows
  // and has no manual bar, emit a vertical scrollbar view (see `qualifying-bars`)
  val checked = views.map(fn(v) check-chrome(v))
  val present = main.scroll-keys
  val manual  = manual-scrollbar-keys()
  val states  = all-scroll-states()
  val qualified = qualifying-bars(present, states, manual)
  val autobars = qualified.map fn((k, info, horizontal))
    bar-view(k, info, if horizontal then Horizontal else Vertical, scrollbar)
  val (native, layers) = checked.partition(fn(v) !v.chrome.is-in-layer)
  Raw-scene(main, layers ++ autobars, native)

// resolve `Scope(sel)` targets (owner geometry against the last-published
// scene tree, one frame behind -- see `scope-rect-of`) and composite: the
// second half of `with-scene`, kept a SEPARATE function (see `raw-scene`'s
// doc for why).
pub fun raw-scene/finish<a>( r : raw-scene<a> ) : <keytree,uistate> scene-out<a>
  fun unerase-tree( t : any ) : ltree<a>
    unerase(t)
  val rect-of = fn(k : string)
    match current-scene-tree()
      Nothing -> Nothing
      Just(t) -> scope-rect-of(k, Just(unerase-tree(t)))
  // auto-scrollbar rect guard (task-4-review Important #2): `qualifying-bars`
  // emits a bar-shaped view for every overflowing region regardless of
  // whether its owner rect is known yet -- an unresolved target falls back to
  // the WHOLE VIEWPORT (`compose`'s Positioned/Display rule), so without this
  // guard a newly-overflowing region's bar renders pinned to a window corner
  // for its first frame. Drop any bar view whose region rect isn't resolved
  // THIS frame; the resettle trigger below (built from these same resolved
  // rects) guarantees next frame re-renders and re-resolves it once the
  // region's rect appears, matching the pre-Task-4 `rect-of(...).is-just`
  // gate this restores (`bar-view` always keys a bar `"<id>:vscroll"` /
  // `"<id>:hscroll"`, the structural marker used to spot it here).
  fun bar-ready( v : view<a> ) : <keytree,uistate> bool
    if v.key.ends-with(":vscroll").is-just || v.key.ends-with(":hscroll").is-just then
      match v.anchor
        Just(a) -> match a.target
          Scope(k) -> rect-of(k).is-just
          Display  -> True
        Nothing -> True
    else True
  val layers = r.layers.filter(bar-ready)
  // the resettle trigger (task-4-review Important #1): a signature over every
  // Scope-anchored view actually emitted this frame (InLayer layers, incl.
  // auto scrollbars, + native/Panel views), keyed by view identity and its
  // RESOLVED owner rect -- the backend's "re-render once more, a target
  // moved/appeared" source (see backend.kk's `anchor-sig` read).
  // Only RESOLVED entries are included (Nothing is omitted, not zeroed), so a
  // target's first appearance (Nothing -> Just) still changes the signature
  // via list membership -- the settle behavior (converges once rects stop
  // moving) matches the old registry's.
  fun scope-sig-entries( vs : list<view<a>> ) : <keytree,uistate> list<(string,(float64,float64,float64,float64))>
    vs.flatmap fn(v)
      match v.anchor
        Just(a) -> match a.target
          Scope(k) -> match rect-of(k)
            Just(rect) -> [(v.key, rect)]
            Nothing    -> []
          Display -> []
        Nothing -> []
  publish-scope-rects(scope-sig-entries(layers) ++ scope-sig-entries(r.native))
  Scene-out( compose(r.main, layers, rect-of), r.native )

// realize native-chrome views as in-window layers (web / degrade path)
pub fun scene-out/flatten<a,e>( s : scene-out<a>,
                              rect-of : (string) -> <keytree|e> maybe<(float64,float64,float64,float64)> ) : <keytree|e> widget<a>
  match s.windows
    Nil -> s.main
    ws  -> compose(s.main, ws.map(fn(v) v(chrome = InLayer, anchor = Just(v.anchor.default(Anchoring())))), rect-of)

// a snapshot `rect-of` resolver over the last-published scene tree -- the same
// lookup `with-scene` builds, shared so `flatten`/Panel callers (the backends)
// don't each re-derive it
pub fun rect-of-snapshot<a,e>() : uistate ((string) -> <keytree|e> maybe<(float64,float64,float64,float64)>)
  fun unerase-tree( t : any ) : ltree<a>
    unerase(t)
  match current-scene-tree()
    Nothing -> fn(k : string) Nothing
    Just(t) ->
      val tt = unerase-tree(t)
      fn(k : string) scope-rect-of(k, Just(tt))
