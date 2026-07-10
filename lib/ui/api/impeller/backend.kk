/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The native backend: the shared layout runs with Impeller paragraph
// metrics; each render RECONCILES the new widget tree against the retained
// laid-out tree (reusing its node cells and list spine in place, see
// ui/widget/reconcile and lib/ui/bench) and paints one display list. Input
// arrives via `pump` -- a strand on the libuv
// event loop that polls the GLFW window, hit-tests against the current tree,
// and emits messages. Focus (for text inputs) is identified by the input's
// tree-order index so it survives re-renders.
module ui/api/impeller/backend

import std/num/float64
import std/core/unsafe
import std/core/undiv
import std/async
import std/async/thread
import std/num/int32
import std/data/int32-map   // xchannel / spawn-thread / native-threads (the platform/render split)
import std/time/duration
import ui/widget
import ui/transform   // mat4 (row-major 4x4) for LTransform3d's paint
import ui/anchor    // place() for Panel screen positioning
import ui/state
import ui/async     // future-boundary: the async-image loading boundary
import ui/image     // image-source / image-load (the async-image union)
import ui/view      // scene-out / main+windows split
import ui/api/impeller/impeller
import ui/api/impeller/nav

// The mounted app. The laid-out tree lives in its OWN ref so `render` can
// take it out uniquely (swap in a placeholder) before reconciling -- unique
// ownership is what lets Perceus reuse the tree cells in place.
// a cached repaint boundary: the widget that produced the subtree (validity
// by ptr-eq -- a memo hit keeps it stable), the paint epoch it recorded
// under, the recorded display list, and a re-record sequence (rainbow color)
pub struct dl-entry
  srcw  : any        // erased widget<a>
  epoch : int
  hov   : maybe<(float64,float64,float64,float64)>  // hover rect IF it intersected the boundary
  prs   : bool       // pressed state recorded (only meaningful when hov is Just)
  rx    : float64    // position recorded at (hover is boundary-local, so a
  ry    : float64    // hovered boundary that MOVES must re-record)
  dl    : any        // erased display-list
  seq   : int

// a real secondary OS window mounted from a scene view. Identity is the view's
// key (`vkey`); `win` is the host table slot. Each window owns its OWN retained
// laid-out tree and repaint-boundary cache (unique ownership, like the main
// tree). `dismiss` is the view's `on-dismiss` (re-read each render so it tracks
// the app), `pos` caches the last SCREEN position pushed for a Panel (so
// set-window-pos only fires on change).
pub struct win-mount<a>
  vkey      : string
  win       : int
  tree      : ref<global, ltree<a>>
  dlcache   : ref<global, int32-map<dl-entry>>
  dismiss   : maybe<a>
  pos       : ref<global, (float64,float64)>
  dismissed : ref<global, bool>     // rising-edge latch for window-close-requested (sticky flag)
  chrome    : chrome                // the chrome it was OPENED with (decoration is fixed at create time)

pub struct mounted<a>
  tree     : ref<global, ltree<a>>
  dragging : ref<global, maybe<drag-st<a>>>  // active drag (ghost + payload) since press
  hover    : ref<global, maybe<(float64,float64,float64,float64)>>  // rect of the hovered target
  pressed  : ref<global, bool>             // pointer currently down
  dlcache  : ref<global, int32-map<dl-entry>>  // repaint boundaries (keyed by memo id)
  wins     : ref<global, list<win-mount<a>>>  // mounted secondary OS windows (by view key)
  emit     : a -> ioc ()
  width    : float64
  height   : float64

// ref-field mutation goes through explicit bindings (m.field := x collides
// with field-setter sugar)
fun take-tree<a>( m : mounted<a> ) : ioc ltree<a>
  val r = m.tree
  val old = !r
  r := LFlex(no-owner, 0.0, 0.0, [])       // placeholder: old is now uniquely owned
  old
fun set-tree<a>( m : mounted<a>, t : ltree<a> ) : ioc ()
  val r = m.tree
  r := t
fun set-drag<a>( m : mounted<a>, d : maybe<drag-st<a>> ) : ioc ()
  val r = m.dragging
  r := d
fun set-hover<a>( m : mounted<a>, h : maybe<(float64,float64,float64,float64)> ) : ioc ()
  val r = m.hover
  r := h
fun set-press-flag<a>( m : mounted<a>, p : bool ) : ioc ()
  val r = m.pressed
  r := p
fun set-wins<a>( m : mounted<a>, ws : list<win-mount<a>> ) : ioc ()
  val r = m.wins
  r := ws
// take a window's tree out uniquely (swap in a placeholder) so reconcile can
// reuse its cells in place -- exactly the main tree's discipline
fun take-win-tree<a>( wm : win-mount<a> ) : ioc ltree<a>
  val r = wm.tree
  val old = !r
  r := LFlex(no-owner, 0.0, 0.0, [])
  old
fun set-win-tree<a>( wm : win-mount<a>, t : ltree<a> ) : ioc ()
  val r = wm.tree
  r := t
fun set-win-pos<a>( wm : win-mount<a>, p : (float64,float64) ) : ioc ()
  val r = wm.pos
  r := p
fun set-dismissed<a>( wm : win-mount<a>, v : bool ) : ioc ()
  val r = wm.dismissed
  r := v

// find a mounted window by its view key / by its host slot id (structural
// recursion -- total, no closures over the msg type var)
fun find-win<a>( ws : list<win-mount<a>>, k : string ) : maybe<win-mount<a>>
  match ws
    Nil          -> Nothing
    Cons(wm, rs) -> if wm.vkey == k then Just(wm) else find-win(rs, k)
fun win-with-id<a>( ws : list<win-mount<a>>, id : int ) : maybe<win-mount<a>>
  match ws
    Nil          -> Nothing
    Cons(wm, rs) -> if wm.win == id then Just(wm) else win-with-id(rs, id)
fun any-vkey<a>( vs : list<view<a>>, k : string ) : bool
  match vs
    Nil          -> False
    Cons(v, rs)  -> if v.key == k then True else any-vkey(rs, k)
// chrome -> host window code (matches host.m: 0 decorated/titled, 1 borderless panel)
fun chrome-code( c : chrome ) : int
  match c
    Titled -> 0
    Panel  -> 1
    InLayer -> 0

// The `measure` handler body: shape an Impeller paragraph and read back its
// box. `max-w` is finite for wrapping text and `unbounded-w` (see ui/widget)
// for a single line -- so shaping at `max-w` reproduces layout without the old
// fixed-width no-wrap bug. Font family / weight / italic beyond size are a
// native follow-up (needs the Impeller paragraph-builder C shim to accept
// them); size is honored today.
pub fun measure-native( content : string, font : font, max-w : float64 ) : ioc (float64, float64)
  val para = paragraph(content, font.size, Color(0.0, 0.0, 0.0), max-w)
  (para.width, para.height)

// build a multi-run paragraph matching `spans`' font overrides -- the SAME
// shape `paint-at`'s `LRich` case builds (see below), except color is a
// placeholder everywhere: only font size participates in measurement (Global
// Constraints), and this paragraph is thrown away after its metrics/glyph
// info are read, never painted.
fun measure-rich-paragraph( content : string, base-font : font, spans : list<(int,int,maybe<font>)>,
                            max-w : float64 ) : ioc paragraph
  val pb = rich-begin()
  pb.push-style(base-font.size, Color(0.0, 0.0, 0.0))
  fun emit( pos : int, remaining : list<(int,int,maybe<font>)> ) : ioc ()
    match remaining
      // NO `.truncate` here: `.truncate` zeroes a slice's length (meant to
      // be followed by `.extend` to a SHORTER length, as the `Cons` branch
      // below does) -- `content.slice.advance(pos)` alone already gives
      // "from `pos` to the end of the string", which is exactly the tail
      // this branch needs to emit.
      Nil -> pb.add-text(content.slice.advance(pos).string)
      Cons(sp, rest) ->
        val (s, e, mf) = sp
        if s > pos then pb.add-text(content.slice.advance(pos).truncate.extend(s - pos).string)
        pb.push-style(mf.default(base-font).size, Color(0.0, 0.0, 0.0))
        pb.add-text(content.slice.advance(s).truncate.extend(e - s).string)
        pb.pop-style()
        emit(e, rest)
  emit(0, spans)
  pb.pop-style()
  pb.rich-build(max-w)

// resolve one span's rect(s) (given as a UTF-16 code-unit range) against a
// built `rich` paragraph: walk the lines [su,eu) touches, one rect per line
// (matching `ui/test`'s deterministic `rect-for`'s shape) -- a span pushes
// exactly ONE style over its whole range, so its run is never split within a
// single line, and the union of the first and last glyph's grapheme-cluster
// bounds on a line brackets the whole slice the span occupies there.
fun span-rects( para : paragraph, lm : line-metrics, nlines : int, su : int, eu : int ) : ioc list<(float64,float64,float64,float64)>
  fun go( line : int, acc : list<(float64,float64,float64,float64)> ) : <ioc,div> list<(float64,float64,float64,float64)>
    if line >= nlines || su >= eu then acc.reverse
    else
      val ls = lm.line-start(line)
      val le = lm.line-end(line)
      val lo = su.max(ls)
      val hi = eu.min(le)
      val rest =
        if lo < hi then
          match (para.glyph-bounds-at(lo), para.glyph-bounds-at(hi - 1))
            (Just((x0, y0, w0, h0)), Just((x1, y1, w1, h1))) ->
              val x = x0.min(x1)
              val y = y0.min(y1)
              val right = (x0 + w0).max(x1 + w1)
              val bottom = (y0 + h0).max(y1 + h1)
              Cons((x, y, right - x, bottom - y), acc)
            _ -> acc
        else acc
      go(line + 1, rest)
  pretend-no-div( fn() go(0, []) )

// the real (non-test) `measure-rich` handler: shape the multi-run paragraph,
// read back width/height the way `measure-native` already does for plain
// text, then resolve every span's rect(s) via glyph info. Spans are indexed
// by CODEPOINT offset (ui/widget's `text-span` convention); `cp-to-u16`
// converts to the UTF-16 code-unit indices Impeller's glyph API wants.
pub fun measure-rich-native( content : string, base-font : font, spans : list<(int,int,maybe<font>)>,
                         max-w : float64 ) : ioc (float64, float64, list<list<(float64,float64,float64,float64)>>)
  val para = measure-rich-paragraph(content, base-font, spans, max-w)
  val tw = para.width
  val th = para.height
  val nlines = para.line-count
  val lm = para.line-metrics
  val rects = spans.map fn(sp)
    val (s, e, _) = sp
    val su = cp-to-u16(content, s)
    val eu = cp-to-u16(content, e)
    span-rects(para, lm, nlines, su, eu)
  (tw, th, rects)

// run layout / reconcile with the `measure` handler installed inline (a
// polymorphic wrapper can't introduce `ioc` over layout's effect).
// `pretend-no-div` discharges the `div` of a finite-tree traversal at this
// boundary, which also sidesteps Koka's handler-over-divergent-computation
// row limitation.
fun laid-out<msg>( w : widget<msg>, c : constraints ) : <uistate,ioc> ltree<msg>
  with handler
    fun measure-text(content, font, max-w) measure-cached(content, font, max-w, fn() measure-native(content, font, max-w))
    fun measure-rich(content, base-font, spans, max-w) measure-rich-native(content, base-font, spans, max-w)
  pretend-no-div
    w.layout(c)

fun re-laid<msg>( old : ltree<msg>, w : widget<msg>, c : constraints ) : <uistate,ioc> ltree<msg>
  with handler
    fun measure-text(content, font, max-w) measure-cached(content, font, max-w, fn() measure-native(content, font, max-w))
    fun measure-rich(content, base-font, spans, max-w) measure-rich-native(content, base-font, spans, max-w)
  pretend-no-div
    reconcile(old, w, c)

pub fun mount<msg>( s : scene-out<msg>, emit : msg -> ioc (), cfg : app-config ) : <keytree,uistate,ioc,exn> mounted<msg>
  // window 0 renders the composited MAIN tree (InLayer overlays + autobars);
  // secondary chrome (Titled / Panel) becomes real OS windows via sync-windows
  val w = s.main
  impeller/init(cfg.title, cfg.width, cfg.height)
  install-native-image-ops()   // ui/async's `image` decodes/uploads through these (task #53)
  val (cw, ch) = (cfg.width.float64, cfg.height.float64)
  val tree0 = w.laid-out(tight(cw, ch))
  val m = Mounted(ref(tree0), ref(Nothing), ref(Nothing), ref(False), ref(int32-map/empty()), ref([]), emit, cw, ch)
  set-live-scene(erase(tree0))
  publish-scene-tree(erase(tree0))   // Scope/Panel targets resolve owner-rect against this next frame
  present-tree(m)
  // open any windows the initial view already emits (nothing may re-render
  // otherwise, e.g. an app that opens a window at startup)
  sync-windows(m, s)
  set-live-window-scenes(m)
  m

pub fun render<msg>( m : mounted<msg>, s : scene-out<msg> ) : <keytree,uistate,ioc,exn> mounted<msg>
  val w = s.main   // window 0 is the composited main tree; windows escape below
  // reconcile the new widget tree against the previous laid-out tree, reusing
  // its node cells AND list spine in place (see lib/ui/bench: ~half the bytes
  // of a fresh layout). `take-tree` extracts the old tree uniquely (the
  // precondition for reuse); `set-tree` installs the reconciled result.
  val old = m.take-tree
  // lay out to the CURRENT window size (re-read each render) so a resize
  // re-flows; the pump requests a render when the size changes
  val new = re-laid(old, w, tight(window-width(), window-height()))
  // bake the current scroll offsets (ui/state) into the LScroll nodes, so paint
  // and hit-testing share one value; the offset is native paint state, not part
  // of the portable layout
  val baked = new.bake-scroll
  m.set-tree(baked)
  set-live-scene(erase(baked))
  publish-scene-tree(erase(baked))   // Scope/Panel targets resolve owner-rect against THIS tree next frame
  // the resettle trigger: `s` (already composed by `composed(...)` before
  // this call) resolved its Scope targets against the PREVIOUS scene tree,
  // publishing the resolved rects (`publish-scope-rects`, ui/view's `finish`)
  // for exactly the views that just got composited into `s`/`baked`. If any
  // of those rects changed since the last render (including first-appearance
  // Nothing -> Just, which changes the entry SET), the target may have
  // settled into a new position this frame that a downstream view (overlay,
  // auto-scrollbar, Panel) hasn't picked up yet -- request one more render so
  // the next `composed(...)` re-resolves against THIS frame's tree (published
  // just above). Stabilizes once rects stop moving, like scroll metrics.
  val sig = anchor-sig(all-scope-rects())
  if sig != !anchor-sig-ref then
    set-anchor-sig(sig)
    request-render()
  present-tree(m)
  // the SECONDARY-window diff: open new views, reconcile+present alive ones,
  // place Panels, close views no longer emitted (runs AFTER the main tree so
  // Panel anchors resolve against this frame's published rects)
  sync-windows(m, s)
  set-live-window-scenes(m)
  // retention: release GPU textures for images no longer mounted in ANY live
  // tree (main + secondary windows). Runs on the reconciled TREE (not the paint
  // walk), so a memo-cached boundary still keeps its images' owners live.
  // (skip the tree walk entirely when no image has ever been cached -- the
  // common case for imageless apps)
  if !(!imgcache-ref).is-empty then
    val live = (!m.wins).foldl((!m.tree).image-owners([]), fn(a, wm) (!wm.tree).image-owners(a))
    prune-images(live)
  m

// ----------------------------------------------------------------
// secondary windows: the declarative diff. `s.windows` is the desired set of
// real windows (keyed by view key); `!m.wins` is what is currently mounted.
// Create the missing, reconcile+present the alive, place the Panels, close the
// dropped. State pruning (a closed window's ephemeral state) is the app's
// retention concern; the backend only tracks the OS window + its tree.
fun sync-windows<msg>( m : mounted<msg>, s : scene-out<msg> ) : <keytree,uistate,ioc,exn> ()
  val existing = !m.wins
  var acc := []
  s.windows.foreach fn(v)
    match find-win(existing, v.key)
      Just(wm) | chrome-code(wm.chrome) != chrome-code(v.chrome) ->
        // decoration (Titled/Panel) is fixed at open-window time on GLFW and
        // can't be re-decorated in place -- identity is the KEY, the OS window
        // itself is disposable. Close it and drop the record (don't add to
        // acc); the key stays "missing" this frame so the create path above
        // reopens it next render with the new chrome.
        close-window(wm.win)
        request-render()
      Just(wm) ->
        // keep the retained refs (tree/dlcache/pos/dismissed), re-read the
        // app's on-dismiss; same chrome kind -- title may still have changed
        match (wm.chrome, v.chrome)
          (Titled(otitle, _, _), Titled(ntitle, _, _)) | otitle != ntitle ->
            set-window-title(wm.win, ntitle)
          _ -> ()
        val rec = Win-mount(v.key, wm.win, wm.tree, wm.dlcache, v.on-dismiss, wm.pos, wm.dismissed, wm.chrome)
        if window-alive(rec.win) then reconcile-window(m, rec, v)
        acc := Cons(rec, acc)
      Nothing ->
        val id = open-win-for(v)
        // -1 = host table full / ring full: skip recording entirely so the next
        // render's diff re-attempts the open cleanly (never store -1 as a slot)
        if id < 0 then () else
          acc := Cons(Win-mount(v.key, id, ref(LFlex(no-owner, 0.0, 0.0, [])), ref(int32-map/empty()),
                                v.on-dismiss, ref((-1.0e18, -1.0e18)), ref(False), v.chrome), acc)
          // async creation: the window isn't alive/reconciled THIS frame, so
          // nothing else schedules the follow-up paint -- request one so an
          // idle app that just opened a window doesn't sit blank
          request-render()
  // close every mounted window whose view is no longer emitted, then commit
  existing.foreach fn(wm)
    if !any-vkey(s.windows, wm.vkey) then close-window(wm.win)
  set-wins(m, acc.reverse)

// enqueue creation of the OS window for a view. Titled uses its declared title
// and size. A Panel's content SELF-SIZES, so lay it out once at loose
// constraints purely to size the window; the window's own reconcile lays out
// again at tight(actual size) once it is alive (this throwaway layout happens
// only at create time, once per window).
fun open-win-for<msg>( v : view<msg> ) : <uistate,ioc,exn> int
  match v.chrome
    Titled(title, tw, th) -> open-window(chrome-code(v.chrome), title, tw, th)
    Panel ->
      val lc = v.content.laid-out(Constraints(0.0, unbounded-w, 0.0, unbounded-w))
      val (cw, ch) = lc.size
      open-window(chrome-code(v.chrome), "", cw, ch)
    InLayer -> -1   // never reached (InLayer views stay in s.main), fail safe

// reconcile a window's content at its CURRENT size and present it. Same
// take/set unique-ownership discipline as the main tree; window trees do NOT
// publish anchor rects (their coords are window-local).
fun reconcile-window<msg>( m : mounted<msg>, wm : win-mount<msg>, v : view<msg> ) : <keytree,uistate,ioc,exn> ()
  val old = wm.take-win-tree
  val new = re-laid(old, v.content, tight(window-width(wm.win), window-height(wm.win)))
  val baked = new.bake-scroll
  wm.set-win-tree(baked)
  match v.chrome
    Panel -> place-panel(wm, v)
    _     -> ()
  present-win(m, wm)

// place a Panel: SCREEN position = main-window-origin() + place(...) resolved
// exactly as `view/layers` does (target rect via owner-rect over the
// last-published scene tree for Scope, else the main viewport for Display).
// set-window-pos only on change.
fun place-panel<msg>( wm : win-mount<msg>, v : view<msg> ) : <keytree,uistate,ioc,exn> ()
  val anch   = v.anchor.default(Anchoring())
  val mtarget = match anch.target
    Display  -> Nothing
    Scope(k) -> match current-scene-tree()
      Nothing -> Nothing
      Just(t) -> scope-rect-of(k, Just(unerase(t)))
  val (cw, ch) = (!wm.tree).size
  val (vw, vh) = (window-width(), window-height())    // main viewport (Display-target rect only)
  val (tx, ty, tw, th) = match mtarget
    Just(r) -> r
    Nothing -> (0.0, 0.0, vw, vh)
  // UNCLAMPED alignment (place() clamps into the viewport, but escaping the
  // main window's bounds is the whole point of a Panel): target point minus
  // self point plus offset, in main-window content coordinates
  val (tpx, tpy) = anch.target-align.at(tx, ty, tw, th)
  val (spx, spy) = anch.self-align.at(0.0, 0.0, cw, ch)
  val (lx, ly) = (tpx - spx + anch.offset-x, tpy - spy + anch.offset-y)
  val (ox, oy) = main-window-origin()
  val (sx, sy) = (ox + lx, oy + ly)
  val (px, py) = !wm.pos
  if sx != px || sy != py then
    set-window-pos(wm.win, sx, sy)
    wm.set-win-pos((sx, sy))

// present a secondary window: reuses present-tree's painting body but targets
// `wm.win` and OMITS the window-0-only extras (the drag ghost and the debug
// rainbow border).
fun present-win<msg>( m : mounted<msg>, wm : win-mount<msg> ) : <uistate,ioc> ()
  val t = !wm.tree
  val b = builder()
  b.scale(content-scale(wm.win), content-scale(wm.win))
  b.draw-background(solid(t.root-bg))
  b.paint-at(t, 0.0, 0.0, get-focused(), !m.hover, !m.pressed, wm.dlcache)
  present(b.build, win = wm.win)

fun set-live-scene( t : any ) : ioc ()      // avoid field-setter sugar collision
  val r = live-scene-ref
  r := Just(t)

fun set-anchor-sig( s : string ) : ioc ()   // avoid field-setter sugar collision
  val r = anchor-sig-ref
  r := s

// a change signature for the anchor-rect registry (keys + rounded positions)
val anchor-sig-ref : ref<global, string> = unsafe-total{ ref("") }

// the CURRENT laid-out scene, erased -- read by the ui/test-live driver
// (queries by keyed/anchored name walk this tree, same as headless tests)
val live-scene-ref : ref<global, maybe<any>> = unsafe-total{ ref(Nothing) }

// ---- image texture cache (identity-keyed) ----
// One decoded+uploaded GPU texture per image OWNER (the LImage's int32 id),
// created lazily on first paint and released when the owner is pruned (the
// image unmounted). A module-global (like live-scene-ref) rather than a
// `mounted` field: image owners are process-globally-unique int32 ids, there is
// one native app per process, and this keeps it off the recursive `paint-at`
// signature. MAIN + secondary windows share it (the prune sweep walks all live
// trees). `iw`/`ih` are the decoded native pixel size, needed by the fit math.
// `ImgReady` carries the `src` it was decoded from so a cache HIT can detect
// a stable-owner, changed-src swap (carousel / detail-swap: same `?key`, new
// picture) and re-decode instead of painting the stale texture forever --
// see `image-for` below. `ImgLoading`/`ImgFailed` don't need it: they carry
// no texture to keep or drop, so a src change on those states is a plain
// cache miss already (nothing to compare against).
pub type img-state
  ImgLoading
  ImgReady( tex : int, iw : float64, ih : float64, src : string )
  ImgFailed

val imgcache-ref : ref<global, int32-map<img-state>> = unsafe-total{ ref(int32-map/empty()) }

fun set-imgcache( c : int32-map<img-state> ) : ioc ()   // avoid field-setter sugar collision
  val r = imgcache-ref
  r := c

// test-only: the number of live image cache entries (Loading/Ready/Failed).
// The retention assert (ui/test-live) checks this drops to 0 when an image
// unmounts and returns to 1 when it re-mounts.
pub fun image-cache-size() : ioc int
  (!imgcache-ref).size

// test-only: currently-live GPU textures (pins that `prune-images` actually
// RELEASES the texture on unmount, not just drops the cache map entry -- a
// bug that skips `texture-release` would leak GPU memory while still passing
// the `image-cache-size` retention check above)
pub fun image-live-textures() : ioc int
  live-textures()

// test-only: the `src` the (single) currently-Ready cache entry was decoded
// from -- lets a src-change scenario assert the cache actually re-decoded the
// NEW src (not just that the live-texture count balanced) without threading
// an owner id through the test API. Assumes exactly one Ready image is
// mounted, which is the shape of the retention scenario's app.
pub fun image-cache-first-src() : ioc maybe<string>
  (!imgcache-ref).list.foldl(Nothing) fn(acc, kv)
    match acc
      Just(_) -> acc
      Nothing -> match kv.snd
        ImgReady(_, _, _, src) -> Just(src)
        _ -> Nothing

// decode `src` off the cache miss and upload it to a GPU texture on THIS (the
// render) thread. Synchronous on first paint of each distinct owner (a one-time
// per-image hitch); cached thereafter. NOTE: the plan prefers a worker-thread
// decode with a render-thread upload handoff; that is deferred (see the task
// report) -- the effect-row surgery to thread `async` through the whole
// recursive paint walk was judged too invasive for this cut.
fun load-image( src : string ) : ioc img-state
  match decode-image(src)
    Nothing -> ImgFailed
    Just((buf, w, h)) ->
      val tex = texture-create(buf, w, h)   // consumes buf (frees or uploads)
      if tex == 0 then ImgFailed
      else ImgReady(tex, w.float64, h.float64, src)

// the img-state for `owner`, decoding+uploading (and caching) on a miss.
// A cache HIT whose stored `src` no longer matches the current node's `src`
// (a stable `?key` whose content swapped -- carousel/detail-swap) is treated
// as a miss too: release the stale texture (balancing the upcoming create,
// so `g_live_tex` nets zero across the swap), drop the entry, and re-decode.
fun image-for( owner : int32, src : string ) : ioc img-state
  match (!imgcache-ref).lookup(owner)
    Just(ImgReady(tex, _, _, cached-src)) | cached-src != src ->
      texture-release(tex)                    // -- balances the ++ in load-image below
      val s = load-image(src)
      set-imgcache((!imgcache-ref).set(owner, s))
      s
    Just(s) -> s
    Nothing ->
      val s = load-image(src)
      set-imgcache((!imgcache-ref).set(owner, s))
      s

// ---- async image loading (task #53) ----
// PIN set: an async texture is uploaded (by the boundary's `run`) BEFORE its
// `ready` leaf is mounted, so for a brief window the texture lives in the cache
// while its owner is absent from the live tree -- a `prune-images` sweep in
// that window would wrongly release it. `put-image-texture` PINS the owner;
// `prune-images` UNPINS any owner it sees live (the leaf has mounted -> normal
// tree-retention takes over from here, including the eventual unmount-release).
// A retry re-uploads -> re-pins (fresh).
//
// GRACE PERIOD: a pin is NOT permanent. If the boundary unmounts before its
// ready leaf ever mounts (e.g. an image scrolled past a lazy list during its
// decode/min-load window), the owner is never seen live and a permanent pin
// would leak the texture/cache-entry/pin forever. So a pin carries a
// `pin-state`: `PinFresh` (this sweep's/the next sweep's grace) or `PinAged`
// (already survived one full sweep un-live). Each `prune-images` sweep that
// does NOT see the owner live ages a `PinFresh` pin to `PinAged`; a pin that
// is ALREADY `PinAged` and still not live is released (texture + cache entry
// + pin dropped) -- exactly one sweep of grace beyond the upload. The normal
// upload -> mount path only needs the grace because RDone -> drain ->
// re-render -> leaf-mounts happens within the render that follows the upload,
// and `prune-images` runs every render, so one sweep is always enough.
type pin-state
  PinFresh
  PinAged

val img-pinned-ref : ref<global, list<(int32, pin-state)>> = unsafe-total{ ref([]) }

fun pin-image( id : int32 ) : ioc ()
  val r = img-pinned-ref
  // (re)pin as FRESH -- a re-upload/retry resets the grace clock
  r := Cons((id, PinFresh), (!r).filter(fn(kv) kv.fst != id))
fun unpin-image( id : int32 ) : ioc ()
  val r = img-pinned-ref
  r := (!r).filter(fn(kv) kv.fst != id)
fun is-pinned( id : int32 ) : ioc bool
  (!img-pinned-ref).any(fn(kv) kv.fst == id)

// store an async-decoded+uploaded texture under `id` (called by the image
// `future-boundary`'s `run` -- via the installed image-ops -- on the render
// thread after `upload-pixels` / `upload-rgba`). Releases any texture already
// cached under `id` first so a re-run (retry / a second decode before a prune)
// never leaks -- `g_live_tex` nets to exactly one live texture per live async
// image. Marks the entry with the `async-image-src` marker so the paint arm's
// `image-for` HITS it (no re-decode) and `prune-images` still releases it.
pub fun put-image-texture( id : int, tex : int, iw : int, ih : int ) : ioc ()
  match (!imgcache-ref).lookup(id.int32)
    Just(ImgReady(old, _, _, _)) -> texture-release(old)   // balances the ++ from a prior upload
    _ -> ()
  set-imgcache((!imgcache-ref).set(id.int32, ImgReady(tex, iw.float64, ih.float64, async-image-src)))
  pin-image(id.int32)   // protect until the ready leaf mounts (see the PIN note)

// install the native decode/upload/put primitives into ui/async's backend-
// agnostic image front door (task #53). ui/async's `image` calls through these
// for its `Async` `future-boundary` run; when they are NOT installed (web /
// headless) `image` falls back to a plain `<img>`/leaf. Called once at mount.
// The decode externs are wrapped `ioc`; ui/async runs them inside `compute`
// (off the render thread) and the uploads on it.
pub fun install-native-image-ops() : ioc ()
  install-image-ops(Image-ops(
    fn(p)      decode-path(p),
    fn(bytes)  decode-bytes(bytes),
    fn(buf, w, h)  upload-pixels(buf, w, h),
    fn(rgba, w, h) upload-rgba(rgba, w, h),
    fn(id, tex, w, h) put-image-texture(id, tex, w, h) ))

// collect the owners of every LImage in a laid-out tree (structural walk;
// `pretend-decreasing` on the child lists discharges the div of the recursion,
// exactly like widget/scroll-keys)
fun image-owners<msg>( ^t : ltree<msg>, acc : list<int32> ) : list<int32>
  match t
    LImage(o, _, _, _, _) -> Cons(o, acc)
    // a box with an image SOURCE owns a texture too -- without this its entry
    // is pruned every frame and the picture re-decodes forever
    LBox(o, Just(Fill(_, _, Just(SImage(_, _)))), _, _, _, _, _, child) -> child.image-owners(Cons(o, acc))
    LBox(_, _, _, _, _, _, _, child) -> child.image-owners(acc)
    LLink(_, _, _, _, _, _, child) -> child.image-owners(acc)
    LScroll(_, _, _, _, _, _, _, child) -> child.image-owners(acc)
    LAct(_, _, _, _, _, _, child) -> child.image-owners(acc)
    LActMsg(_, _, _, _, _, _, child) -> child.image-owners(acc)
    LInteractive(_, _, _, _, _, _, _, _, child) -> child.image-owners(acc)
    LRotate(_, _, _, _, child) -> child.image-owners(acc)
    LTransform3d(_, _, _, _, child) -> child.image-owners(acc)
    LMemo(_, _, _, _, child) -> child.image-owners(acc)
    LFlex(_, _, _, children) -> children.foldl(acc, fn(a, e) e.thd.pretend-decreasing.image-owners(a))
    LLayer(_, _, _, kids) -> kids.foldl(acc, fn(a, e) e.thd.pretend-decreasing.image-owners(a))
    _ -> acc

// prune image cache entries whose owner is no longer present in ANY live tree,
// releasing each pruned texture (an unmounted image frees its GPU memory). An
// owner seen LIVE is UNPINNED (its ready leaf has mounted -> normal retention);
// an owner that is neither live nor PINNED is released (a pinned owner is an
// async texture uploaded but not yet mounted -- kept for its grace period, see
// the PIN note above `img-pinned-ref`).
// IMPORTANT 2 (final-review) note: aging a `PinFresh` pin to `PinAged` is
// NOT the end of the grace -- a follow-up sweep is still needed to actually
// release it. The normal path gets that follow-up for free (renders keep
// coming). But `settle-if-current`'s drop branch (ui/async.kk) now requests
// exactly ONE render to guarantee THIS sweep runs at all in an otherwise-
// idle app -- with nothing else asking for frames, that one render would
// age Fresh -> Aged and then stall (still elevated, never released). So
// this sweep requests ANOTHER render itself whenever it ages a pin, closing
// the loop: once a grace period starts, it always runs itself to completion
// (Fresh -> Aged -> released) with no dependency on outside render traffic,
// same as the normal mounted-app path.
fun prune-images( live : list<int32> ) : <uistate,ioc> ()
  (!imgcache-ref).list.foreach fn(kv)
    val (owner, st) = kv
    if live.any(fn(o) o == owner) then
      unpin-image(owner)
    elif !is-pinned(owner) then
      match st
        ImgReady(tex, _, _, _) -> texture-release(tex)
        _ -> ()
      set-imgcache((!imgcache-ref).remove(owner))
  // age (or release) every pin NOT seen live this sweep -- see the grace-period
  // note above `img-pinned-ref`. Any pin still in the list at this point
  // belongs to an owner not seen live above (live owners were unpinned).
  val r = img-pinned-ref
  var kept := []
  (!r).foreach fn(kv)
    val (owner, ps) = kv
    match ps
      PinFresh ->
        kept := Cons((owner, PinAged), kept)
        request-render()   // guarantee the follow-up sweep that finishes the grace (see note above)
      PinAged ->
        match (!imgcache-ref).lookup(owner)
          Just(ImgReady(tex, _, _, _)) -> texture-release(tex)
          _ -> ()
        set-imgcache((!imgcache-ref).remove(owner))
        // dropped -- not re-added to `kept`
  r := kept

// the CURRENTLY mounted secondary windows' laid-out trees, erased, in the
// SAME order as `mounted.wins` -- (view key, tree). Recorded right after
// `sync-windows` on every mount/render so it always reflects the windows
// that were just reconciled+presented this frame (a window opened this very
// frame has an empty placeholder tree until its first reconcile completes).
val live-window-scenes-ref : ref<global, list<(string, int, any)>> = unsafe-total{ ref([]) }

fun set-live-window-scenes<msg>( m : mounted<msg> ) : ioc ()
  val r = live-window-scenes-ref
  r := (!m.wins).map( fn(wm) (wm.vkey, wm.win, erase(!wm.tree)) )

// ---- the live-test surface (ui/test-live middleman driver) ----
// events go through the host's SYNTHETIC injection into the same rings the
// GLFW callbacks fill; the pump/dispatch path is the production one
pub fun test-scene-any() : ioc maybe<any>
  !live-scene-ref

// the mounted secondary windows' erased trees, (view key, tree), in mount
// order -- read by ui/test-live to build its combined main+windows tree
pub fun test-window-scenes() : ioc list<(string, any)>
  (!live-window-scenes-ref).map( fn((k, _, t)) (k, t) )

// the host window id for a mounted view key ( -1 if that key is not
// currently a live window ) -- used to route injected events to the right
// OS window
pub fun test-window-id( vkey : string ) : ioc int
  match (!live-window-scenes-ref).find( fn((k, _, _)) k == vkey )
    Just((_, win, _)) -> win
    Nothing -> -1

pub fun test-inject-click( x : float64, y : float64, win : int = 0 ) : ioc ()
  inject-cursor(x, y, win)
  inject-pointer(1.0, x, y, win)   // left press
  inject-pointer(2.0, x, y, win)   // release
pub fun test-inject-text( s : string, win : int = 0 ) : ioc ()
  s.list.foreach fn(c)
    inject-char(c.int, win)
pub val test-backend : string = "impeller"   // scenario gating (e.g. web scrolling is browser-owned)
pub fun test-inject-key( key : string, win : int = 0 ) : ioc ()
  inject-key((if key == "Backspace" then 259 elif key == "Enter" then 257 else 256), win)   // GLFW codes
pub fun test-inject-hover( x : float64, y : float64, win : int = 0 ) : ioc ()
  inject-cursor(x, y, win)
pub fun test-inject-scroll-at( x : float64, y : float64, dy : float64, win : int = 0 ) : ioc ()
  inject-cursor(x, y, win)   // drain-scroll reads the cursor for the target region
  inject-scroll(0.0, dy, win)
// discard whatever is sitting in the host rings right now (fixes #46: a
// scenario's tail burst could still be in flight -- injected but not yet
// drained by the pump -- when ui/test-live's reset-app runs between
// scenarios; left alone it lands LATE, in the next scenario's freshly-reset,
// same-keyed field, as a stray leading character)
pub fun test-drain-rings() : ioc ()
  drain-rings()
// pass/fail probe: browser runners read document.title; native is stdout-only
pub fun test-report( status : string ) : ioc ()
  ()
fun anchor-sig( rects : list<(string,(float64,float64,float64,float64))> ) : string
  rects.map(fn((k, (x, y, w, h))) k ++ ":" ++ x.show ++ "," ++ y.show ++ "," ++ w.show ++ "," ++ h.show).join(";")

// a text input/field box: surface, a focus RING (accent border on all sides),
// the value or placeholder, and a measured caret at the end of the text when
// focused (no blink yet -- that is the animation probe's job).
fun draw-input-box( b : builder, x : float64, y : float64, w0 : float64, h0 : float64,
                    focused : bool, value : string, ph : string ) : <uistate,ioc> ()
  if focused then   // ring: accent rect behind, surface rect inset over it
    b.draw-rounded-rect(x - 1.5, y - 1.5, w0 + 3.0, h0 + 3.0, 7.5, solid(Color(0.48, 0.64, 0.97)))
  b.draw-rounded-rect(x, y, w0, h0, 6.0, solid(Color(0.16, 0.17, 0.24)))
  if value.is-empty && !ph.is-empty then
    // the hint stays visible while focused-and-empty; the caret sits before it
    b.draw-paragraph(paragraph(ph, 14.0, Color(0.55, 0.55, 0.62)), x + 8.0, y + 7.0)
  else
    b.draw-paragraph(paragraph(value, 14.0, Color(0.90, 0.90, 0.94)), x + 8.0, y + 7.0)
  if focused && caret-visible() then   // caret: a thin bar after the measured text
    // never measure the empty string (the shim's empty paragraph is unreliable)
    val tw = if value.is-empty then 0.0
             else measure-native(value, sans(14.0), unbounded-w).fst
    b.draw-rounded-rect(x + 8.0 + tw + 1.0, y + 6.0, 1.5, h0 - 12.0, 0.75,
                        solid(Color(0.90, 0.90, 0.94)))

// the window clear color: the root box's fill (borrows the tree)
fun root-bg<msg>( ^t : ltree<msg> ) : color
  match t
    LBox(_, Just(Fill(color, _, _)), _, _, _, _, _, _) -> color
    _ -> Color(0.086, 0.086, 0.118)

fun present-tree<msg>( m : mounted<msg> ) : <uistate,ioc> ()
  val t = !m.tree
  val b = builder()
  b.scale(content-scale(), content-scale())   // render at native (retina) resolution
  b.draw-background(solid(t.root-bg))
  b.paint-at(t, 0.0, 0.0, get-focused(), !m.hover, !m.pressed, m.dlcache)
  // the drag ghost, if any, is a top layer that follows the pointer (a drag is
  // just another positioned view, composited last so it sits over everything)
  match !m.dragging
    Just(d) ->
      b.paint-at(d.ghost, d.x - d.grab-x, d.y - d.grab-y, Nothing, Nothing, False, m.dlcache)
    Nothing -> ()
  if debug-repaint() then
    // the rotating window border: content NOT inside a stable boundary is
    // re-recorded on every present -- the flashing frame makes that visible
    // (flutter tints its root layer the same way)
    val rs = rainbow-seq()
    val hue = ((rs * 47) % 360).float64 / 360.0
    val col = Color(0.5 + 0.5 * cos(hue * 6.283), 0.5 + 0.5 * cos((hue + 0.33) * 6.283),
                    0.5 + 0.5 * cos((hue + 0.67) * 6.283), 0.85)
    val (ww, wh) = (window-width(), window-height())
    b.draw-rounded-rect(0.0, 0.0, ww, 3.0, 0.0, solid(col))
    b.draw-rounded-rect(0.0, wh - 3.0, ww, 3.0, 0.0, solid(col))
    b.draw-rounded-rect(0.0, 0.0, 3.0, wh, 0.0, solid(col))
    b.draw-rounded-rect(ww - 3.0, 0.0, 3.0, wh, 0.0, solid(col))
  present(b.build)

// does a box's rect match the hovered target's rect? (same layout produced
// both, so the floats are equal up to a tiny epsilon)
fun hovered( x : float64, y : float64, w : float64, h : float64,
             hover : maybe<(float64,float64,float64,float64)> ) : bool
  match hover
    Just((hx, hy, hw, hh)) -> abs(x - hx) < 0.5 && abs(y - hy) < 0.5 && abs(w - hw) < 0.5 && abs(h - hh) < 0.5
    Nothing -> False

fun hover-changed( a : maybe<(float64,float64,float64,float64)>, b : maybe<(float64,float64,float64,float64)> ) : bool
  match (a, b)
    (Nothing, Nothing) -> False
    (Just((ax,ay,aw,ah)), Just((bx,by,bw,bh))) -> ax != bx || ay != by || aw != bw || ah != bh
    _ -> True

// ----------------------------------------------------------------
// paint: one walk of the laid-out tree (threading the input index for the
// focus ring, and the hovered rect / press state for the hover affordance).
// Borrows the tree.

fun paint-at<msg>( b : builder, ^t : ltree<msg>, x : float64, y : float64,
                   focus : maybe<int>,
                   hover : maybe<(float64,float64,float64,float64)>, pressed : bool,
                   dc : ref<global, int32-map<dl-entry>> ) : <uistate,ioc> ()
  match t
    LText(_, content, font, wrap, color, w0, _) ->
      // re-shape at the recorded width so wrapping reproduces layout; single
      // line uses `unbounded-w` (a large width, so no wrap)
      b.draw-paragraph(paragraph(content, font.size, color, if wrap then w0 else unbounded-w), x, y)
    LRich(_, content, base-font, base-color, spans, wrap, w0, _, _) ->
      // real multi-run painting: an incremental Impeller ParagraphBuilder,
      // pushing/popping each span's own style over the base run's
      val pb = rich-begin()
      pb.push-style(base-font.size, base-color)
      // walk `content` left to right, opening/closing a pushed style at
      // each span boundary and falling back to the base style in the gaps
      fun emit( pos : int, remaining : list<text-span<_>> ) : ioc ()
        match remaining
          // NO `.truncate` here: `.truncate` zeroes a slice's length (meant to
          // be followed by `.extend` to a SHORTER length, as the `Cons` branch
          // below does) -- `content.slice.advance(pos)` alone already gives
          // "from `pos` to the end of the string", which is exactly the tail
          // this branch needs to emit.
          Nil -> pb.add-text(content.slice.advance(pos).string)
          Cons(s, rest) ->
            if s.start > pos then pb.add-text(content.slice.advance(pos).truncate.extend(s.start - pos).string)
            pb.push-style(s.font.default(base-font).size, s.color.default(base-color))
            pb.add-text(content.slice.advance(s.start).truncate.extend(s.end - s.start).string)
            pb.pop-style()
            emit(s.end, rest)
      emit(0, spans)
      pb.pop-style()
      b.draw-paragraph(pb.rich-build(if wrap then w0 else unbounded-w), x, y)
    LLink(_, _, _, _, dx, dy, child) -> b.paint-at(child, x + dx, y + dy, focus, hover, pressed, dc)
    LScroll(_, _, w0, h0, _, offset, horizontal, child) ->
      // clip to the viewport, then paint the child shifted by the scroll offset
      // ALONG the axis. The offset is baked into the node by `bake-scroll` at
      // render time (from ui/state), so paint and hit-testing use the SAME value.
      b.save()
      b.clip-rect(x, y, w0, h0)
      val (cx, cy) = if horizontal then (x - offset, y) else (x, y - offset)
      b.paint-at(child, cx, cy, focus, hover, pressed, dc)
      b.restore()
    LAct(_, _, _, _, dx, dy, child) -> b.paint-at(child, x + dx, y + dy, focus, hover, pressed, dc)
    LMemo(_, mid, msrcw, _, child) ->
      // REPAINT BOUNDARY: reuse the recorded display list while (a) the
      // memoized widget is pointer-identical (layout unchanged), (b) the
      // paint epoch matches (focus/caret/field/scroll the painters read
      // directly), and (c) the hover state AS SEEN BY THIS SUBTREE is
      // unchanged -- the hover rect only matters if it intersects these
      // bounds, so hovering elsewhere leaves the cache untouched.
      // Recording happens at (0,0); drawing translates -- a moved-but-
      // unchanged boundary stays cached.
      val ep = paint-epoch()
      val (bw, bh) = child.size
      val hv = match hover
        Just((hx, hy, hw, hh)) ->
          if hx + hw < x || hx > x + bw || hy + hh < y || hy > y + bh then Nothing
          else hover
        Nothing -> Nothing
      val hit = match (!dc).lookup(mid.int32)
        Just(e) | e.epoch == ep && unsafe-ptr-eq(unerase(e.srcw), msrcw)
                  && e.hov == hv
                  && (hv.is-nothing || (e.prs == pressed && e.rx == x && e.ry == y)) ->
          Just(unerase(e.dl))
        _ -> Nothing
      val dl = match hit
        Just(d) -> d
        Nothing ->
          val seq = match (!dc).lookup(mid.int32) { Just(e) -> e.seq + 1; Nothing -> 0 }
          val nb = builder()
          // record in LOCAL space: shift the (clipped) hover rect instead of
          // the content, so in-boundary hover affordances paint correctly
          val lhov = match hv
            Just((hx, hy, hw, hh)) -> Just((hx - x, hy - y, hw, hh))
            Nothing -> Nothing
          nb.paint-at(child, 0.0, 0.0, focus, lhov, pressed, dc)
          if debug-repaint() then
            // rainbow: a NEW color on every re-record; stable = cached
            val hue = ((mid * 37 + seq * 97) % 360).float64 / 360.0
            nb.draw-rounded-rect(0.0, 0.0, bw, bh, 4.0,
              solid(Color(0.5 + 0.5 * cos(hue * 6.283), 0.5 + 0.5 * cos((hue + 0.33) * 6.283),
                          0.5 + 0.5 * cos((hue + 0.67) * 6.283), 0.28)))
          val d = nb.build
          val dr = dc
          dr := (!dc).set(mid.int32, Dl-entry(erase(msrcw), ep, hv, pressed, x, y, erase(d), seq))
          d
      b.save()
      b.translate(x, y)
      b.draw-display-list(dl)
      b.restore()
    LRotate(_, deg, w0, h0, child) ->
      // rotate about the node's center: translate the pivot to the origin,
      // rotate, translate back; the child then paints at its usual coords
      b.save()
      b.translate(x + w0 / 2.0, y + h0 / 2.0)
      b.rotate(deg)
      b.translate(0.0 - (x + w0 / 2.0), 0.0 - (y + h0 / 2.0))
      b.paint-at(child, x, y, focus, hover, pressed, dc)
      b.restore()
    LOverlay(_, _w0, _h0, child) ->
      b.paint-at(child, x, y, focus, hover, pressed, dc)   // decoration: paint only
    LClip(_, r, w0, h0, child) ->
      // clip to this node's rounded rect, then paint the child normally --
      // whatever it draws outside (an expanding ripple) is cut here. The web
      // half is `overflow:hidden` + a matching `border-radius`.
      b.save()
      b.clip-rrect(x, y, w0, h0, r)
      b.paint-at(child, x, y, focus, hover, pressed, dc)
      b.restore()
    LTransform3d(_, m3, w0, h0, child) ->
      // concat about the node's center: translate the pivot to the origin,
      // apply the 4x4, translate back -- mirrors LRotate's save/rotate/restore
      val cx = x + w0 / 2.0
      val cy = y + h0 / 2.0
      val m4 = m3.centered(cx, cy)
      b.save()
      b.transform(m4)
      b.paint-at(child, x, y, focus, hover, pressed, dc)
      b.restore()
    LInteractive(_, _, _, _, _, _, dx, dy, child) -> b.paint-at(child, x + dx, y + dy, focus, hover, pressed, dc)
    LBox(bown, bg, _, w0, h0, dx, dy, child) ->
      match bg
        Just(Fill(color, radius, src)) ->
          // brighten on hover / dim on press (matches the web CSS affordance)
          val lit = if hovered(x, y, w0, h0, hover) then (if pressed then 0.92 else 1.08) else 1.0
          val pnt = match src
            Nothing -> solid(color.brighten(lit))
            // fractions resolve against this box's absolute rect here; CSS
            // resolves the same fractions as an angle/percentage on its side
            Just(SLinear(fx, fy, tx, ty, c0, c1)) ->
              linear-paint(x + fx * w0, y + fy * h0, x + tx * w0, y + ty * h0,
                           c0.brighten(lit), c1.brighten(lit))
            Just(SRadial(cx, cy, rad, c0, c1)) ->
              radial-paint(x + cx * w0, y + cy * h0, rad * w0,
                           c0.brighten(lit), c1.brighten(lit))
            // an image source paints BELOW as a texture, not as a paint: the
            // rounded rect still needs a fill under it (the placeholder colour
            // shows through while the decode is in flight)
            Just(SImage(_, _)) -> solid(color.brighten(lit))
          b.draw-rounded-rect(x, y, w0, h0, radius, pnt)
          // then the texture itself, clipped to the same rounded rect so a
          // square picture cannot square off a rounded surface
          match src
            Just(SImage(isrc, ifit)) ->
              match image-for(bown, isrc)
                ImgReady(tex, iw, ih, _) | iw > 0.0 && ih > 0.0 ->
                  b.save()
                  b.clip-rrect(x, y, w0, h0, radius)
                  match ifit
                    // COVER crops the SOURCE to the box's aspect and fills it
                    Cover ->
                      val sc = (w0 / iw).max(h0 / ih)
                      val (cw, ch) = (w0 / sc, h0 / sc)
                      b.draw-texture-rect(tex, (iw - cw) / 2.0, (ih - ch) / 2.0, cw, ch, x, y, w0, h0)
                    // CONTAIN keeps the whole picture and insets the DEST
                    Contain ->
                      val sc = (w0 / iw).min(h0 / ih)
                      val (dw, dh) = (iw * sc, ih * sc)
                      b.draw-texture-rect(tex, 0.0, 0.0, iw, ih,
                                          x + (w0 - dw) / 2.0, y + (h0 - dh) / 2.0, dw, dh)
                    // Fill: stretch the whole picture over the whole box
                    _ -> b.draw-texture-rect(tex, 0.0, 0.0, iw, ih, x, y, w0, h0)
                  b.restore()
                _ -> ()
            _ -> ()
        Nothing -> ()
      b.paint-at(child, x + dx, y + dy, focus, hover, pressed, dc)
    LFlex(_, _, _, children) ->
      children.foreach fn(entry)
        val (dx, dy, child) = entry
        b.paint-at(child, x + dx, y + dy, focus, hover, pressed, dc)
    LLayer(_, _, _, children) ->
      children.foreach fn(entry)
        val (dx, dy, child) = entry
        b.paint-at(child, x + dx, y + dy, focus, hover, pressed, dc)
    LField(_, key, value, ph, _, w0, h0) ->
      val focused = focus.map(fn(i) i == key).default(False)
      b.draw-input-box(x, y, w0, h0, focused, value, ph)
    LActMsg(_, _, _, _, dx, dy, child) -> b.paint-at(child, x + dx, y + dy, focus, hover, pressed, dc)
    LInput(_, key, value, ph, _, _, w0, h0) ->
      val focused = focus.map(fn(i) i == key).default(False)
      b.draw-input-box(x, y, w0, h0, focused, value, ph)
    LSlider(_, lo, hi, _, value, _, w0, h0) ->
      val cy = y + h0 / 2.0
      val ratio = if hi > lo then (value - lo) / (hi - lo) else 0.0
      b.draw-rounded-rect(x, cy - 2.0, w0, 4.0, 2.0, solid(Color(0.25, 0.27, 0.38)))
      b.draw-rounded-rect(x, cy - 2.0, w0 * ratio.max(0.0).min(1.0), 4.0, 2.0,
                          solid(Color(0.48, 0.64, 0.97)))
      b.draw-rounded-rect(x + (w0 - 12.0) * ratio.max(0.0).min(1.0), cy - 6.0, 12.0, 12.0, 6.0,
                          solid(Color(0.90, 0.90, 0.94)))
    LImage(owner, src, fit, w0, h0) ->
      // decode+upload on first paint (identity-cached by `owner`); draw the
      // texture mapped onto the box per `fit`. A miss / decode failure paints
      // the neutral placeholder box (Task 4's fill).
      match image-for(owner, src)
        ImgReady(tex, iw, ih, _) | iw > 0.0 && ih > 0.0 ->
          match fit
            ui/image/Fill ->
              // stretch to the box (aspect not preserved)
              b.draw-texture-rect(tex, 0.0, 0.0, iw, ih, x, y, w0, h0)
            Contain ->
              // letterbox: scale to fit INSIDE, centered (whole image visible)
              val s = (w0 / iw).min(h0 / ih)
              val (dw, dh) = (iw * s, ih * s)
              b.draw-texture-rect(tex, 0.0, 0.0, iw, ih,
                                  x + (w0 - dw) / 2.0, y + (h0 - dh) / 2.0, dw, dh)
            Cover ->
              // scale to FILL, center-crop via the source rect (box fully covered)
              val s = (w0 / iw).max(h0 / ih)
              val (sw, sh) = (w0 / s, h0 / s)
              b.save()
              b.clip-rect(x, y, w0, h0)
              b.draw-texture-rect(tex, (iw - sw) / 2.0, (ih - sh) / 2.0, sw, sh, x, y, w0, h0)
              b.restore()
            ImgNone ->
              // native size, centered, clipped to the box (may under/overflow)
              b.save()
              b.clip-rect(x, y, w0, h0)
              b.draw-texture-rect(tex, 0.0, 0.0, iw, ih,
                                  x + (w0 - iw) / 2.0, y + (h0 - ih) / 2.0, iw, ih)
              b.restore()
        _ ->
          b.draw-rounded-rect(x, y, w0, h0, 0.0, solid(Color(0.16, 0.17, 0.24)))

// ----------------------------------------------------------------
// pump: the platform input strand (runs on the libuv event loop). Pointer
// events are infrequent, so hit-testing reads a fresh copy of the tree each
// time; the retained tree survives.

// the animation frame interval: pace to the DISPLAY's refresh rate (a 120Hz
// panel animates at 120fps; the drawable present syncs any timer drift)
pub fun frame-interval-ms() : ioc int
  refresh-ms().int.max(4).min(33)

// PLATFORM/RENDER THREAD SPLIT. The MAIN thread must own GLFW/Cocoa (events
// only arrive there) but the Cocoa modal resize loop BLOCKS it -- so the app
// itself runs on a dedicated RENDER thread: layout, reconcile, paint, present
// (CAMetalLayer presents are thread-safe), the uv loop and every strand.
// Main parks in `platform-loop`; its callbacks keep firing inside the modal
// loop and wake the render thread's pump -- which is what makes LIVE-resize
// re-rendering work. Order matters: spawn the render thread FIRST (uv loops
// must exist before Cocoa init), init the window on main, then release the
// render thread and park. Falls back to the single-thread embed loop where
// there are no OS threads.
pub fun with-platform( cfg : app-config, body : () -> <async,ioc,exn> () ) : <async,ioc,exn> ()
  if !native-threads() then body() else
    mark-split()                       // the render pump must NOT install the embed waiter
    val hand-ch = xchannel()           // render -> main: the render thread's release-sender
    val hand-send = hand-ch.sender
    spawn-thread fn()
      with handle/try fn(err)
        println("ui/impeller render thread: uncaught exception: " ++ err.show)
      val win-ready = xchannel()
      hand-send.xemit(win-ready.sender)
      val go : bool = win-ready.xreceive   // wait: the window exists (main initialized Cocoa)
      if go then body()                           // the WHOLE app runs here
    impeller/init(cfg.title, cfg.width, cfg.height)   // Cocoa/GLFW/Metal on MAIN
    val win-send = hand-ch.xreceive
    win-send.xemit(True)
    platform-loop()                    // main parks here for the app's lifetime
    shutdown()                         // window closed: tear down Cocoa on MAIN
    exit-loop()

// park the pump until the GLFW waiter reports fresh input (a single-shot
// uv_async, re-armed per iteration; same await shape as `wait`)
fun wait-input() : <async,ioc> ()
  await-error("wait-input") fn(evloop, resume)
    input-signal-setup(evloop, fn() resume(()))
  ()

// the laid-out tree an event should hit-test against: window 0 (or an unknown
// window) routes to the main tree, else that mounted window's own tree
fun tree-for<msg>( m : mounted<msg>, win : int ) : ioc ltree<msg>
  if win == 0 then !m.tree
  else match win-with-id(!m.wins, win)
    Just(wm) -> !wm.tree
    Nothing  ->
      // unknown window: its win-mount was dropped this frame (close race, or
      // a chrome swap tearing down the old OS window) between the event being
      // tagged and this hit-test. Drop the event rather than hit-testing it
      // against window 0's tree at the wrong (secondary-window-local) coords.
      LFlex(no-owner, 0.0, 0.0, [])
// repaint the window an event landed in (window 0 gets the full present-tree
// with ghost/border; a secondary window gets present-win)
fun present-for<msg>( m : mounted<msg>, win : int ) : <uistate,ioc> ()
  if win == 0 then present-tree(m)
  else match win-with-id(!m.wins, win)
    Just(wm) -> present-win(m, wm)
    Nothing  -> present-tree(m)

pub fun pump<msg>( m : mounted<msg> ) : <async,uistate,ioc> ()
  with handle/try fn(err)
    println("ui/impeller: uncaught exception: " ++ err.show)
  // EVENT-DRIVEN input: park on the input signal each iteration. Under the
  // platform split the MAIN thread's callbacks fire it; single-threaded, the
  // embed waiter does (installed here) -- either way input wakes the pump
  // instantly and an idle app burns no CPU.
  if !platform-split() then install-event-wait()
  var lw := window-width()
  var lh := window-height()
  while { !should-close() }
    wait-input()
    // window resize -> re-render (drain-state re-lays-out at the new size)
    val (cw, ch) = (window-width(), window-height())
    if cw != lw || ch != lh then
      lw := cw
      lh := ch
      request-render()
    // declarative dismiss: any window whose close button was hit (sticky flag,
    // stays true across pump iterations until close-window). Fire on-dismiss
    // only on the RISING EDGE (wm.dismissed latches it) -- the sticky flag
    // itself would otherwise re-fire the message every pump wake for as long
    // as the app keeps emitting the view (e.g. on-dismiss defers the actual
    // close by a render, or is a non-idempotent msg). The latch resets
    // naturally: it lives on the win-mount record, which is dropped when the
    // view stops being emitted and freshly allocated (False) if it reopens.
    (!m.wins).foreach fn(wm)
      if window-close-requested(wm.win) && !(!wm.dismissed) then
        wm.set-dismissed(True)
        match wm.dismiss
          Just(dmsg) -> (m.emit)(dmsg)
          Nothing    -> ()
    // hover: the front-most interactive rect under the LIVE cursor -- IN THE
    // WINDOW that last saw the cursor; repaint THAT window on change
    val cwin = cursor-win()
    val ctree = tree-for(m, cwin)
    val hv = ctree.hover-rect(cursor-x(cwin), cursor-y(cwin))
    if hover-changed(hv, !m.hover) then
      m.set-hover(hv)
      present-for(m, cwin)
    // `interactive` widgets: write the hovered key to ui/state (re-renders so
    // the builder reflects the state)
    val hk = ctree.hover-key(cursor-x(cwin), cursor-y(cwin))
    if hk != get-hovered() then set-hovered(hk)
    // an active drag ghost follows the live cursor (repaint on move)
    match !m.dragging
      Just(d) ->
        val (cx, cy) = (cursor-x(), cursor-y())
        if cx != d.x || cy != d.y then
          m.set-drag(Just(d(x = cx, y = cy)))
          present-tree(m)
      Nothing -> ()
    // keep ui/state's scroll metrics in sync with the laid-out tree (content /
    // viewport heights); a change (first layout, resize) re-views so a linked
    // scrollbar sizes correctly
    if sync-scroll-metrics(!m.tree) then request-render()
    // mouse-wheel / trackpad: move the scroll region under the cursor
    drain-scroll(m)
    drain-pointers(m)
    drain-text(m)
  // teardown: AppKit window ops are MAIN-thread-only -- under the split the
  // platform loop observes should-close, shuts down, and exits the process
  if !platform-split() then
    shutdown()
    exit-loop()

// exit the process when the window closes (the app loop never returns).
// _exit, NOT exit: exit() runs dylib static destructors (libimpeller/Skia)
// while the render thread may still be mid-frame inside Skia -- the OS
// reclaims everything at process death, so skip finalizers entirely.
extern exit-loop() : ioc ()
  c inline "(_Exit(0), kk_Unit)"

// apply the accumulated wheel delta to the scroll region under the cursor
// (ui/state's `apply-wheel` does the region lookup + clamp + write). Goes
// through `request-render` (not just a repaint) so a linked scrollbar rebuilds
// with the new offset; the content itself re-lays-out and paints at the offset.
fun drain-scroll<msg>( m : mounted<msg> ) : <uistate,ioc,exn> ()
  val win = scroll-win()               // the window the pending delta is tagged for
  val dy = take-scroll-dy(win)
  val dx = take-scroll-dx(win)
  if apply-wheel(tree-for(m, win), cursor-x(win), cursor-y(win), dx, dy) then request-render()

fun drain-pointers<msg>( m : mounted<msg> ) : <uistate,ioc,exn> ()
  val kind = next-pointer()
  if kind == 0 then () else
    val win = pointer-win()               // the window this event landed in
    val t = tree-for(m, win)              // hit-test against ITS tree
    val (px, py) = (pointer-x(), pointer-y())
    if kind == 1 then      // press: click targets + drag pickup + focus
      m.set-press-flag(True)
  // the ripple's origin: the press point in the pressed element's OWN frame.
  // `hover-rect` is the same walk `hover-key` just made, and returns that
  // element's absolute rect, so localizing is a subtraction. Set BEFORE
  // `set-pressed`: that call is the tracked write that re-renders, and the
  // rebuild it triggers must already see the new point.
      match t.hover-key-rect(px, py)
        Just((_k, rx, ry, _rw, _rh)) -> set-press-point(px - rx, py - ry)
        Nothing                      -> set-press-point(0.0, 0.0)
      set-pressed(t.hover-key(px, py))   // interactive press state (ui/state)
      // pick up a drag: snapshot the source's ghost subtree + grab offset
      match t.drag-at(px, py)
        Just((payload, ghost, ox, oy)) -> m.set-drag(Just(Drag-st(payload, ghost, px - ox, py - oy, px, py)))
        Nothing -> m.set-drag(Nothing)
      present-for(m, win)  // reflect the pressed affordance + drag ghost at the pickup point (no wait for the first move)
      match t.hit(px, py)
        Just(HitMsg(msg))        -> (m.emit)(msg)
        Just(HitAt(g, hx, hy))   -> (m.emit)(g(hx, hy))
        Just(HitSlider(g, v))    -> (m.emit)(g(v))
        Just(HitLink(to))        -> goto-hash("#/" ++ to)  // ui/router picks this up
        Just(HitAct(thunk))      -> thunk()
        Just(HitMsgIoc(g))       -> (m.emit)(g())          // act-msg: compute from ui/state at click time                 // ui/state write; drain-state re-renders (an opaque surface's no-op absorb lands here too)
        Just(HitInput(k)) ->
          set-focused(Just(k))   // ui/state identity focus; drain-state re-renders
        Nothing ->
          match get-focused()
            Just(_) -> set-focused(Nothing)   // click elsewhere: blur
            Nothing -> ()
    elif kind == 3 then    // right press: context-menu target at the cursor
      match t.hit-context(px, py)
        Just(g) -> (m.emit)(g(px, py))
        Nothing -> ()
    else                   // release: drop targets
      m.set-press-flag(False)
      present-for(m, win)
      set-pressed(Nothing)   // clear interactive press state
      match !m.dragging
        Just(d) ->
          m.set-drag(Nothing)
          match t.hit-drop(px, py)
            Just(g) -> (m.emit)(g(d.payload))
            Nothing -> ()
          present-for(m, win)   // clear the ghost
        Nothing -> ()
    drain-pointers(m)

fun drain-text<msg>( m : mounted<msg>, acc : maybe<(int,string)> = Nothing ) : <uistate,ioc,exn> ()
  val ch = next-char()
  val key = if ch.is-empty then next-key() else 0
  if ch.is-empty && key == 0 then () else
    reset-caret()   // typing snaps the caret solid
    val win = if ch.is-empty then key-win() else char-win()  // the event's window
    val t = tree-for(m, win)
    match get-focused()
      Nothing -> ()
      Just(k) ->
        match t.input-with-key(k)
          Just(LInput(_, _, value, _, oninput, onkey, _, _)) ->
            // CONTROLLED: value round-trips through the model, and the tree
            // is a render old -- a burst of chars in one drain would compute
            // every edit against the same stale value. `acc` carries the
            // accumulated value ACROSS this drain, so each oninput supersedes
            // the previous with the full text (last write is correct).
            val cur = match acc
              Just((ak, av)) | ak == k -> av
              _ -> value
            if !ch.is-empty then
              val nv = cur ++ ch
              (m.emit)(oninput(nv))
              return drain-text(m, Just((k, nv)))
            elif key == 1 then   // backspace
              val nv = cur.head-drop
              (m.emit)(oninput(nv))
              return drain-text(m, Just((k, nv)))
            elif key == 2 then   // enter: commits the ACCUMULATED value's key event
              match onkey
                Just(g) -> (m.emit)(g("Enter"))
                Nothing -> ()
            elif key == 3 then   // escape: blur
              set-focused(Nothing)
            else ()
          Just(LField(_, fk, _, _, onenter, _, _)) ->
            // UNCONTROLLED: edits write ui/state (each write re-renders); the
            // app only hears Enter (if it asked) or reads the value on demand.
            // Edits read the value INSIDE the transition (edit-field-text) --
            // the tree's value is a render old, and a same-batch burst of
            // chars would lose all but the last edit against a stale read
            if !ch.is-empty then edit-field-text(fk, fn(v) v ++ ch)
            elif key == 1 then edit-field-text(fk, fn(v) v.head-drop)
            elif key == 2 then
              match onenter
                Just(g) -> with-field-text(fk, fn(v) (m.emit)(g(v)))
                Nothing -> ()
            elif key == 3 then set-focused(Nothing)
            else ()
          _ -> ()
    drain-text(m, acc)

// the string without its last character
fun head-drop( s : string ) : string
  val n = s.count
  if n <= 1 then "" else s.first(n - 1).string
