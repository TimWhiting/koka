/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The web backend: the SHARED layout pass runs here too (text measured via
// the host's canvas), and the laid-out tree lowers to absolutely-positioned
// DOM -- html/vdom/dom from lib/web-ui are the internal machinery (value
// sync, keyed reconciliation, drag wiring, listener lifecycle). Input needs
// no pump: DOM listeners emit directly.
module ui/api/web/backend

import std/num/float64
import std/num/int32
import std/core/undiv
import std/core/unsafe
import std/async
import web-ui/html
import web-ui/vdom
import web-ui/dom
import ui/widget
import ui/transform   // mat4 (row-major 4x4) for LTransform3d's matrix3d lowering
import ui/state
import ui/async      // install-web-image-ops / Web-image-ops (task 4, web parity)
import ui/view      // scene-out / flatten (windows still flattened as layers)

// a mounted widget app: the vdom tree over the root element. Each render lays
// out to the CURRENT viewport (container width x window height) so it fills the
// screen and re-flows on resize; `maxw`/`maxh` are the configured fallbacks
// (used only before the viewport has a measured size).
//
// Input is UNIFIED with native: the laid-out `tree` is retained in a ref, and
// root-level pointer listeners run the SAME Koka `hit`/`hover-key` walks against
// it (not per-element DOM listeners). The lowering emits listener-free
// positioned divs; only `<a>` (links) and `<input>` (text / slider) keep their
// native DOM behavior, which the browser does better.
pub struct mounted<a>( root : element, node : node<a>, tree : ref<global,ltree<a>>,
                       dragging : ref<global, maybe<drag-st<a>>>,  // active drag ghost (unified with native)
                       emit : a -> ioc (),
                       evch : ref<global, maybe<channel<web-ev>>>, // raw input events (see `web-ev`)
                       width : float64, height : float64, maxw : float64, maxh : float64 )

// A raw web input event. DOM callbacks fire OUTSIDE any effect handler's
// dynamic extent (no evidence), so listeners only capture data and post it
// here; the `pump` strand -- which runs under the app's uistate handler --
// receives and dispatches. This unifies web input with native's
// ring-buffer + pump architecture.
pub type web-ev
  EvClick( x : float64, y : float64 )
  EvContext( x : float64, y : float64 )
  EvPress( x : float64, y : float64 )
  EvRelease( x : float64, y : float64 )
  EvMove( x : float64, y : float64 )
  EvWheel( x : float64, y : float64, dx : float64, dy : float64 )
  EvResize
  EvField( key : int, value : string )

// post an event from a DOM callback (inert until the pump installs the channel)
// ---- the live-test surface (ui/test-live middleman driver) ----
// synthetic events are REAL DOM events dispatched at the DOM fringe
// (web-ui/dom inject-click/inject-text): they bubble to the same root
// listeners real input reaches, so the pump/dispatch path is the
// production one -- the web analog of impeller's ring-buffer injection.
val live-scene-ref : ref<global, maybe<any>> = unsafe-total{ ref(Nothing) }

pub fun test-scene-any() : ioc maybe<any>
  !live-scene-ref

// the web tier has no secondary OS windows (browsers don't have them);
// stubs keep ui/test-live's shared routing code compiling for both hosts --
// there is simply always nothing to route to here
pub fun test-window-scenes() : ioc list<(string, any)>
  []

// no host rings on web (DOM events dispatch synchronously through real
// listeners); the reset-time drain is a no-op kept for driver parity
pub fun test-drain-rings() : ioc ()
  ()
pub fun test-window-id( vkey : string ) : ioc int
  -1

// `win` is accepted (and ignored) for signature parity with the native
// backend's test-inject-*, which the shared ui/test-live driver calls with a
// routed window id -- always 0 (the only "window") on web
pub fun test-inject-click( x : float64, y : float64, win : int = 0 ) : ioc ()
  inject-click(x, y)
pub fun test-inject-text( s : string, win : int = 0 ) : <uistate,ioc,exn> ()
  if !inject-text(s) then throw("ui/test-live: type-text: no input is focused")
pub val test-backend : string = "web"   // scenario gating (e.g. native windows)
// images are browser-managed (`<img>`); there is no native texture cache, so
// this is always 0 on web. Present so the shared retention scenario (which only
// ASSERTS on the impeller tier) still type-checks in the jsweb build.
pub fun image-cache-size() : ioc int
  0
// no native textures on web either (see image-cache-size above)
pub fun image-live-textures() : ioc int
  0
// no native texture cache on web (browser-managed `<img>`); the src-swap
// retention assert is impeller-tier-only, but main.kk references this on both
// tiers so the jsweb build must still resolve it -- always Nothing here.
pub fun image-cache-first-src() : ioc maybe<string>
  Nothing
pub fun test-inject-key( key : string, win : int = 0 ) : ioc ()
  inject-key(key)
pub fun test-inject-hover( x : float64, y : float64, win : int = 0 ) : ioc ()
  inject-move(x, y)
pub fun test-inject-scroll-at( x : float64, y : float64, dy : float64, win : int = 0 ) : ioc ()
  inject-wheel(x, y, dy)   // a real WheelEvent through OUR wheel listener (koka-owned scrolling)
// the pass/fail probe a browser runner reads (document.title)
pub fun test-report( status : string ) : ioc ()
  set-title(status)

fun set-live-scene( t : any ) : ioc ()      // avoid field-setter sugar collision
  val r = live-scene-ref
  r := Just(t)

fun post( chr : ref<global, maybe<channel<web-ev>>>, ev : web-ev ) : ioc ()
  match !chr
    Just(ch) -> ch.emit-io(ev)
    Nothing  -> ()

// The `measure` handler body: text set in a font, measured by the host. A max
// width at or above this sentinel means "single line, natural width"
// (`ui/widget` passes `unbounded-w` for non-wrapping text); anything smaller
// is a wrapping box whose height the host reflows.
val single-line-w : float64 = 1.0e6

fun measure-web( content : string, font : font, max-w : float64 ) : ioc (float64, float64)
  val css = font.css-font
  if max-w >= single-line-w
    then (measure-text-width(content, css), font.size * 1.4)
    else
      // wrapping: the box is as wide as the content, capped at max-w -- so
      // SHORT text (a number in a row) stays narrow instead of greedily filling
      // the width (matches Impeller's actual longest-line width on native).
      (measure-text-width(content, css).min(max-w), measure-text-box-height(content, css, max-w))

// the real `measure-rich` handler: build the SAME `<span>`-per-run
// structure Step 2's paint case emits (via the `measure-rich-box` extern,
// which measures a hidden, off-screen copy of exactly that structure), so
// measured geometry matches painted geometry. Spans are indexed by
// CODEPOINT offset (`ui/widget`'s `text-span` convention); `max-w` at or
// above `unbounded-w` means "single line, natural width" (mirrors
// `measure-web` above) -- passed straight through to the extern, which
// derives wrap-state from it the same way `is-unbounded` does.
fun measure-rich-web( content : string, base-font : font, spans : list<(int,int,maybe<font>)>,
                      max-w : float64 ) : ioc (float64, float64, list<list<(float64,float64,float64,float64)>>)
  val starts = spans.map(fn(s) s.fst.int32).vector
  val ends   = spans.map(fn(s) s.snd.int32).vector
  val fonts  = spans.map(fn(s) s.thd.default(base-font).css-font).vector
  val (tw, th, flat, counts) = measure-rich-box(content, base-font.css-font, starts, ends, fonts, max-w)
  // `flat` packs every span's rect(s) back-to-back, 4 float64s (x,y,w,h)
  // each, in span order; `counts.at(i)` says how many of those rects belong
  // to span `i` -- reassemble by walking both in lockstep.
  fun rect-at( i : int ) : (float64,float64,float64,float64)
    (flat.at(i*4).default(0.0), flat.at(i*4+1).default(0.0), flat.at(i*4+2).default(0.0), flat.at(i*4+3).default(0.0))
  fun take-groups( ridx : int, cs : list<int32> ) : list<list<(float64,float64,float64,float64)>>
    match cs
      Nil -> []
      Cons(n, rest) ->
        val cnt = n.int
        val grp = list(ridx, ridx + cnt - 1).map(rect-at)
        Cons(grp, take-groups(ridx + cnt, rest))
  (tw, th, take-groups(0, counts.list))

// run layout with the host `measure` handler installed inline (a polymorphic
// wrapper can't introduce `ioc` over layout's effect; the handler must be
// inline). `pretend-no-div` discharges layout's `div` at this boundary --
// layout terminates on a finite tree -- which also sidesteps Koka's
// handler-over-divergent-computation row limitation.
fun laid-out<msg>( w : widget<msg>, c : constraints ) : <uistate,ioc> ltree<msg>
  with handler
    fun measure-text(content, font, max-w) measure-cached(content, font, max-w, fn() measure-web(content, font, max-w))
    fun measure-rich(content, base-font, spans, max-w) measure-rich-web(content, base-font, spans, max-w)
  pretend-no-div
    w.layout(c)

// Interaction affordance for pointer targets: a brightness shift on hover /
// press, done entirely in CSS (the browser derives it -- no per-frame state).
// Injected once as a <style> sibling of the app node (vdom only patches its
// own node, so this survives re-renders). `.ui-i` is added to interactive
// boxes and links by the lowering.
val interaction-css : string =
  ".ui-i{transition:filter .12s ease}"
    ++ ".ui-i:hover{filter:brightness(1.08)}"
    ++ ".ui-i:active{filter:brightness(0.92)}"
    // scene layers are pointer-transparent (see the kk:layer lowering); the
    // DOM-native interactive leaves inside them opt back in
    ++ "input,a,.ui-i{pointer-events:auto}"

fun inject-interaction-css( root : element ) : ioc ()
  val s = create-element("style")
  s.set-text(interaction-css)
  root.append-child(s)

// the current viewport size: the container's width x the window's height (so
// the app fills the screen). Content is centered/capped by the app via
// `center`. `maxw`/`maxh` are only used before a measured size exists.
fun viewport( root : element, maxw : float64, maxh : float64 ) : ioc (float64, float64)
  val w = root.num-prop("clientWidth")
  val h = window().num-prop("innerHeight")
  ((if w > 0.0 then w else maxw), (if h > 0.0 then h else maxh))

// ----------------------------------------------------------------
// root pointer input: run the SAME Koka hit walks as native's `drain-pointers`,
// against the retained laid-out tree. `#app` is mounted at the page origin, so a
// mouse event's client coordinates ARE tree coordinates (a nonzero root offset
// would be subtracted here).

fun event-xy() : ioc (float64, float64)
  val ev = current-event()
  (ev.client-x, ev.client-y)

// a click (down+up on the same spot, or a programmatic .click()): dispatch the
// message. Using `click` (not mousedown) matches the browser's button semantics
// and works for synthetic clicks in tests.
fun web-click<msg>( tree : ref<global,ltree<msg>>, emit : msg -> ioc (), px : float64, py : float64 ) : <uistate,ioc> ()
  match (!tree).hit(px, py)
    Just(HitMsg(m))      -> emit(m)
    Just(HitAt(g, _, _)) -> emit(g(px, py))
    Just(HitAct(t))      -> t()          // ui/state write; drain-state re-renders
    Just(HitMsgIoc(g))   -> emit(g())    // act-msg: compute the message from ui/state at click time
    // HitLink is handled by the real <a href>; HitInput / HitSlider by the real
    // <input> -- left to the browser (native navigation / focus / typing / drag)
    _                    -> ()

// a right-click (contextmenu): the browser's native menu is suppressed by the
// dom host (preventDefault); we raise our own via `pointer.context-at`.
fun web-context<msg>( tree : ref<global,ltree<msg>>, emit : msg -> ioc (), px : float64, py : float64 ) : ioc ()
  match (!tree).hit-context(px, py)
    Just(g) -> emit(g(px, py))
    Nothing -> ()

// pressed visual + drag pickup: the front-most interactive under the pointer,
// and (if a drag source is there) snapshot its ghost subtree to follow the
// pointer -- the SAME model as native (no DOM-native drag on the framework path).
fun web-press<msg>( tree : ref<global,ltree<msg>>, drag : ref<global,maybe<drag-st<msg>>>, px : float64, py : float64 ) : <uistate,ioc> ()
  // the ripple's origin: the press point in the pressed element's OWN frame.
  // `hover-rect` is the same walk `hover-key` just made, and returns that
  // element's absolute rect, so localizing is a subtraction. Set BEFORE
  // `set-pressed`: that call is the tracked write that re-renders, and the
  // rebuild it triggers must already see the new point.
  match (!tree).hover-key-rect(px, py)
    Just((_k, rx, ry, _rw, _rh)) -> set-press-point(px - rx, py - ry)
    Nothing                      -> set-press-point(0.0, 0.0)
  set-pressed((!tree).hover-key(px, py))
  match (!tree).drag-at(px, py)
    Just((payload, ghost, ox, oy)) -> drag := Just(Drag-st(payload, ghost, px - ox, py - oy, px, py))
    Nothing -> drag := Nothing

fun web-release<msg>( tree : ref<global,ltree<msg>>, drag : ref<global,maybe<drag-st<msg>>>,
                      emit : msg -> ioc (), px : float64, py : float64 ) : <uistate,ioc> ()
  set-pressed(Nothing)
  match !drag
    Just(d) ->
      drag := Nothing
      match (!tree).hit-drop(px, py)
        Just(g) -> emit(g(d.payload))
        Nothing -> ()
      request-render()   // clear the ghost
    Nothing -> ()

fun web-move<msg>( tree : ref<global,ltree<msg>>, drag : ref<global,maybe<drag-st<msg>>>, px : float64, py : float64 ) : <uistate,ioc> ()
  val hk = (!tree).hover-key(px, py)
  if hk != get-hovered() then set-hovered(hk)
  // an active drag ghost follows the pointer (re-render moves it)
  match !drag
    Just(d) ->
      drag := Just(d(x = px, y = py))
      request-render()
    Nothing -> ()

// ----------------------------------------------------------------
// ui/async's web image parity (task 4): `image( ..., load = Async )` builds
// the SAME phase model on web as native -- the same `future-boundary`, in
// fact (task #58). All this backend supplies is the RESOLUTION primitive:
// `web-probe` (below) resolves the source to an `<img src>` and awaits the
// browser's own decode of it via an offscreen, never-mounted probe element.
// Once it resolves, the REAL `<img>` the `ready` leaf draws carries the exact
// same `src`, so the browser paints it from its own cache -- one fetch and
// one decode, not two.

// Base64 (RFC 4648, '=' padded) over `vector<int8>`, PURE Koka -- no host
// extern needed for `FromBytes`, and every byte value round-trips: int8's
// signed two's-complement `.int` + `+256 % 256` recovers the unsigned byte
// (see test/ui/basic.kk's `demo-png-bytes`, whose values already exercise
// this: -119 -> 137, -3 -> 253, ...).
val b64-chars : vector<char> =
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".list.vector

fun b64c( i : int32 ) : char
  b64-chars.at(i.int).default('A')

fun byte-at( v : vector<int8>, i : int ) : int32
  ((v.at(i).default(0.int8).int).int32 + 256.int32) % 256.int32

fun base64-encode( bytes : vector<int8> ) : string
  val n = bytes.length
  val four = 4.int32
  val sixteen = 16.int32
  val sixtyfour = 64.int32
  fun go( i : int, acc : list<char> ) : list<char>
    if i >= n then acc
    else
      val b0 = bytes.byte-at(i)
      val b1 = if i + 1 < n then bytes.byte-at(i + 1) else 0.int32
      val b2 = if i + 2 < n then bytes.byte-at(i + 2) else 0.int32
      val c0 = b64c(b0 / four)
      val c1 = b64c((b0 % four) * sixteen + b1 / sixteen)
      val c2 = if i + 1 < n then b64c((b1 % sixteen) * four + b2 / sixtyfour) else '='
      val c3 = if i + 2 < n then b64c(b2 % sixtyfour) else '='
      go((i + 3).pretend-decreasing, Cons(c3, Cons(c2, Cons(c1, Cons(c0, acc)))))
  go(0, []).reverse.listchar/string

// resolve an `image-source` to its FINAL `<img src>` string: `FromPath` uses
// its path/URL as-is (the browser fetches it); `FromBytes`/`FromPixels` are
// turned into a data-url first (pure-Koka base64 / the `pixels-to-dataurl`
// DOM extern's offscreen-canvas `putImageData` + `toDataURL`) -- so every
// variant probes through the identical `<img>`-onload wait below.
fun source-src( source : image-source ) : ioc string
  match source
    FromPath(p)              -> p
    FromBytes(bytes)         -> "data:image/png;base64," ++ base64-encode(bytes)
    FromPixels(rgba, pw, ph) -> pixels-to-dataurl(rgba, pw, ph)

// the onload probe: an offscreen `<img>` (never appended to the document) at
// `src`, AWAITED -- this is `future-boundary`'s `run` for a web image, so it
// blocks its own strand and nothing else (task #58; it used to post an
// `EvImageLoaded` through the input pump instead, see ui/async.kk's
// `web-image-ops`). Listeners are wired BEFORE `src` is set so a
// synchronous/cached fire can never race past them; a one-shot probe never
// appended to the document needs no explicit `unsubscribe` -- once neither
// listener is reachable from Koka anymore the element/closures are ordinary
// JS-GC garbage (a self-contained cycle, same as any detached DOM subtree).
fun web-probe( source : image-source ) : <async,ioc,exn> string
  val src = source-src(source)
  val ch : channel<bool> = channel()
  val probe = create-element("img")
  ignore(probe.subscribe("load",  fn() ch.emit-io(True)))
  ignore(probe.subscribe("error", fn() ch.emit-io(False)))
  probe.set-attribute("src", src)
  if ch.receive
    then src
    else throw("ui/image: failed to load " ++ src)

pub fun mount<msg>( s : scene-out<msg>, emit : msg -> ioc (), cfg : app-config ) : <keytree,uistate,ioc,exn> mounted<msg>
  val w = s.flatten(rect-of-snapshot())
  val root = match get-element-by-id(cfg.root-id)
    Just(el) -> el
    Nothing  -> throw("ui: no element with id '" ++ cfg.root-id ++ "'")
  inject-interaction-css(root)
  val evch : ref<global, maybe<channel<web-ev>>> = ref(Nothing)
  // ui/async's `image` probes onload through this (task 4, web parity)
  install-web-image-ops(Web-image-ops(web-probe))
  // re-lay-out on window resize: the resize fires a render, which re-reads size
  retain(window().subscribe("resize", fn() post(evch, EvResize)))
  val (maxw, maxh) = (cfg.width.float64, cfg.height.float64)
  val (cw, ch) = viewport(root, maxw, maxh)
  // bake scroll offsets (ui/state) into LScroll nodes before lowering, so the
  // clip+translate div paints at the SAME offset native's painter would use
  val tree = w.laid-out(tight(cw, ch)).bake-scroll
  val tree-ref = ref(tree)
  val drag-ref = ref(Nothing)   // maybe<drag-st<msg>>, unified by the handlers below
  // root-level pointer input: DOM callbacks only capture the coordinates and
  // POST them (no effect evidence in a DOM callback); the pump strand runs the
  // Koka hit-testing under the app's handlers -- unified with native.
  fun post-xy( mk : (float64, float64) -> web-ev ) : ioc ()
    val (px, py) = event-xy()
    post(evch, mk(px, py))
  retain(root.subscribe("click",       fn() post-xy(EvClick)))
  retain(root.subscribe("contextmenu", fn() post-xy(EvContext)))
  retain(root.subscribe("mousedown",   fn() post-xy(EvPress)))
  retain(root.subscribe("mouseup",     fn() post-xy(EvRelease)))
  retain(root.subscribe("mousemove",   fn() post-xy(EvMove)))
  // koka-owned scrolling: a non-passive listener (preventDefault suppresses
  // the browser's native scroll -- see web-ui/dom's `subscribe`/dom.js)
  fun post-wheel() : ioc ()
    val (px, py) = event-xy()
    post(evch, EvWheel(px, py, event-wheel-dx(), event-wheel-dy()))
  retain(root.subscribe("wheel", post-wheel))
  val node = vdom/mount(tree.to-html(cw, ch, Nothing, evch), root, emit)
  // keep ui/state's scroll metrics (content/viewport sizes) in sync with the
  // laid-out tree -- a change (first layout) re-renders so a linked scrollbar
  // sizes correctly; SAME shared walk native's pump uses
  if sync-scroll-metrics(!tree-ref) then request-render()
  set-live-scene(erase(tree))
  publish-scene-tree(erase(tree))   // Scope targets resolve owner-rect against this next frame
  Mounted(root, node, tree-ref, drag-ref, emit, evch, cw, ch, maxw, maxh)

pub fun render<msg>( m : mounted<msg>, s : scene-out<msg> ) : <keytree,uistate,ioc,exn> mounted<msg>
  val w = s.flatten(rect-of-snapshot())
  val (cw, ch) = viewport(m.root, m.maxw, m.maxh)   // responsive: re-read the viewport each render
  // bake scroll offsets before lowering (see `mount`); paint/hit/metrics agree
  val laid  = w.laid-out(tight(cw, ch)).bake-scroll
  val r = m.tree
  r := laid                                         // the root listeners read this
  val node2 = patch(m.node, laid.to-html(cw, ch, !m.dragging, m.evch), m.root, m.emit)
  if sync-scroll-metrics(!m.tree) then request-render()
  set-live-scene(erase(laid))
  publish-scene-tree(erase(laid))   // Scope targets resolve owner-rect against THIS tree next frame
  Mounted(m.root, node2, m.tree, m.dragging, m.emit, m.evch, cw, ch, m.maxw, m.maxh)

// the input pump: DOM listeners posted raw events; dispatch them here, under
// the app's uistate handler (a DOM callback itself has no effect evidence).
// `apply-wheel` (ui/state) is `exn` (shared with the native backend, which
// discharges it the same way) -- catch-and-report rather than let a bad
// scroll region crash the whole pump.
pub fun pump<msg>( m : mounted<msg> ) : <async,uistate,ioc> ()
  with handle/try fn(err)
    println("ui/web: uncaught exception: " ++ err.show)
  val ch : channel<web-ev> = channel()
  val r = m.evch
  r := Just(ch)
  pump-loop(m, ch)

fun pump-loop<msg>( m : mounted<msg>, ch : channel<web-ev> ) : <async,uistate,ioc,exn> ()
  match ch.receive
    EvClick(x, y)   -> web-click(m.tree, m.emit, x, y)
    EvContext(x, y) -> web-context(m.tree, m.emit, x, y)
    EvPress(x, y)   -> web-press(m.tree, m.dragging, x, y)
    EvRelease(x, y) -> web-release(m.tree, m.dragging, m.emit, x, y)
    EvMove(x, y)    -> web-move(m.tree, m.dragging, x, y)
    EvWheel(x, y, dx, dy) -> if apply-wheel(!m.tree, x, y, dx, dy) then request-render()
    EvResize        -> request-render()
    EvField(k, v)   -> set-field-text(k, v)
  pump-loop(m, ch)

// the animation frame interval (~60fps; a rAF-driven clock is the upgrade)
pub fun frame-interval-ms() : ioc int
  16

// no platform/render split on web: one cooperative loop
pub fun with-platform( cfg : app-config, body : () -> <async,ioc,exn> () ) : <async,ioc,exn> ()
  body()

// ----------------------------------------------------------------
// lowering: the laid-out tree as absolutely-positioned DOM. Positions are
// parent-relative (CSS absolute positioning nests), so offsets never
// accumulate. Interactive nodes carry web-ui event attributes; keys map to
// vdom keyed reconciliation.

fun px( v : float64 ) : string
  v.show ++ "px"

fun pos-style( x : float64, y : float64, w0 : float64, h0 : float64 ) : string
  "position:absolute;left:" ++ px(x) ++ ";top:" ++ px(y)
    ++ ";width:" ++ px(w0) ++ ";height:" ++ px(h0) ++ ";box-sizing:border-box"

// the CSS `object-fit` keyword for an `image-fit` (qualified `Fill` --
// `ui/widget`'s `fill` struct also mints an unqualified `Fill`)
fun fit-css( f : image-fit ) : string
  match f
    Contain -> "contain"
    Cover -> "cover"
    ui/image/Fill -> "fill"
    ImgNone -> "none"

fun to-html<msg>( t : ltree<msg>, root-w : float64, root-h : float64, drag : maybe<drag-st<msg>>,
                  evch : ref<global, maybe<channel<web-ev>>> ) : <uistate,ioc> html<msg>
  // the drag ghost (if any) is a top layer at (pointer - grab): a translucent,
  // pointer-transparent copy of the dragged subtree that follows the cursor --
  // the same "a drag is a positioned view" model native paints.
  val ghost = match drag
    Just(d) -> [html/elem("div",
                  [style("position:absolute;left:0;top:0;pointer-events:none;opacity:0.7")],
                  [d.ghost.node-html(d.x - d.grab-x, d.y - d.grab-y, [], evch)])]
    Nothing -> []
  div([style("position:relative;width:" ++ px(root-w) ++ ";height:" ++ px(root-h) ++ ";overflow:hidden")],
      [t.node-html(0.0, 0.0, [], evch)] ++ ghost)

// CSS `matrix3d(...)`'s 16 args are COLUMN-major; our `mat4.m` is ROW-major
// (`m[r*4+c]`) -- transpose on the way out, comma-joined.
fun css3d( m3 : mat4 ) : string
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15].map(fn(i)
    val r = i % 4
    val c = i / 4
    m3.m.at(r * 4 + c).default(if r == c then 1.0 else 0.0).show
  ).join(",")

fun node-html<msg>( t : ltree<msg>, x : float64, y : float64, extra : list<attr<msg>>,
                    evch : ref<global, maybe<channel<web-ev>>> ) : <uistate,ioc> html<msg>
  match t
    LText(_, content, font, wrap, color, w0, h0) ->
      // wrapping text fills its measured box (normal wrapping + top-aligned
      // line box); single-line text keeps one line and clips on overflow.
      // `pre`, not `nowrap`: both suppress line-breaking, but `nowrap`
      // COLLAPSES runs of consecutive spaces like normal HTML text does --
      // silently eating a code sample's leading indentation on the web
      // backend (native text shaping never collapses whitespace, so this
      // was web-only). `pre` keeps every space exactly as measured.
      val flow = if wrap
        then ";white-space:normal;overflow:hidden"
        else ";line-height:" ++ px(h0) ++ ";white-space:pre;overflow:hidden"
      html/elem("div",
        [style(pos-style(x, y, w0 + 1.0, h0)
               ++ ";font:" ++ font.css-font
               ++ ";color:" ++ color.to-css
               ++ flow ++ ";pointer-events:none")] ++ extra,
        [html/text(content)])
    LRich(_, content, base-font, base-color, spans, wrap, w0, h0, _) ->
      // real multi-span painting: one `<span>` per run (base-styled gaps and
      // span-styled runs, interleaved left to right), left in NORMAL inline
      // flow inside the positioned container div -- the browser's own reflow
      // wraps them for free (unlike native, which has to drive Impeller's
      // paragraph builder by hand). Click resolution does NOT go through a
      // DOM listener here: like every other pointer role in this backend
      // (LBox, LAct, ...), it is resolved by the root-level `hit-go` walk
      // against `span-rects` (see ui/widget's `LRich` hit-test case), so no
      // per-span `on-click` attr belongs on these nodes.
      fun span-html( pos : int, remaining : list<text-span<_>> )
        match remaining
          Nil ->
            // NO `.truncate` here -- see the note on the native paint case
            // (lib/ui/api/impeller/backend.kk): `.truncate` alone zeroes a
            // slice's length, so a bare `.truncate.string` is UNCONDITIONALLY
            // "", silently dropping any trailing content after the last span.
            // `content.slice.advance(pos)` alone already gives "from `pos` to
            // the end of the string", which is exactly the tail needed here.
            if pos < content.count
              then [html/elem("span", [style(";font:" ++ base-font.css-font ++ ";color:" ++ base-color.to-css)],
                     [html/text(content.slice.advance(pos).string)])]
              else []
          Cons(s, rest) ->
            val gap = if s.start > pos
              then [html/elem("span", [style(";font:" ++ base-font.css-font ++ ";color:" ++ base-color.to-css)],
                     [html/text(content.slice.advance(pos).truncate.extend(s.start - pos).string)])]
              else []
            val f = s.font.default(base-font)
            val c = s.color.default(base-color)
            val span-node = [html/elem("span", [style(";font:" ++ f.css-font ++ ";color:" ++ c.to-css)],
                     [html/text(content.slice.advance(s.start).truncate.extend(s.end - s.start).string)])]
            gap ++ span-node ++ span-html(s.end, rest)
      val flow = if wrap then ";white-space:normal;overflow:hidden"
                 else ";line-height:" ++ px(h0) ++ ";white-space:pre;overflow:hidden"
      html/elem("div",
        [style(pos-style(x, y, w0 + 1.0, h0) ++ flow ++ ";pointer-events:none")] ++ extra,
        span-html(0, spans))
    LLink(_, to, w0, h0, dx, dy, child) ->
      // a real anchor: right-click / open-in-new-tab / deep-link all work,
      // and changing the hash fires "hashchange" (no reload) -> route-sub.
      html/elem("a",
        [style(pos-style(x, y, w0, h0) ++ ";display:block;text-decoration:none;color:inherit"),
         attr("class", "ui-i"), attr("href", "#/" ++ to)] ++ extra,
        [child.node-html(dx, dy, [], evch)])
    LScroll(_, _, w0, h0, content, offset, horizontal, child) ->
      // koka-owned scrolling: a clipping viewport (overflow:hidden -- the
      // browser never scrolls it) wrapping a relative inner box sized to the
      // content along the scroll axis, shifted by the BAKED offset via
      // `transform:translate3d` -- the same convention native's painter uses
      // (child painted at x, y - offset for vertical; wheel-up reveals earlier
      // content). The offset comes from `ui/state` via `bake-scroll`, baked
      // into the tree before lowering, so paint/hit-testing/metrics agree.
      val (inner-w, inner-h) = if horizontal then (px(content), px(h0)) else (px(w0), px(content))
      val shift = if horizontal
        then "translate3d(-" ++ px(offset) ++ ",0,0)"
        else "translate3d(0,-" ++ px(offset) ++ ",0)"
      html/elem("div", [style(pos-style(x, y, w0, h0) ++ ";overflow:hidden")] ++ extra,
        [html/elem("div", [style("position:relative;width:" ++ inner-w ++ ";height:" ++ inner-h
                                   ++ ";transform:" ++ shift)],
          [child.node-html(0.0, 0.0, [], evch)])])
    LAct(_, _, w0, h0, dx, dy, child) ->
      // click handled by root hit-testing (-> HitAct); keep the visual affordance
      html/elem("div",
        [style(pos-style(x, y, w0, h0) ++ ";cursor:pointer"), attr("class", "ui-i")] ++ extra,
        [child.node-html(dx, dy, [], evch)])
    LInteractive(_, _, _, _, w0, h0, dx, dy, child) ->
      // click + hover/press are driven by root hit-testing (the builder paints
      // its own states from ui/state); `hit-go`/`hover-key` account for `slop`,
      // so no listeners and no slop overlay div are needed here.
      html/elem("div",
        [style(pos-style(x, y, w0, h0) ++ ";cursor:pointer")] ++ extra,
        [child.node-html(dx, dy, [], evch)])
    LLayer(_, w0, h0, children) ->
      // the reserved layer marker (Positioned's viewport-sized layer): wrap
      // in a box-less (display:contents) pointer-transparent element so a
      // composited layer's container never swallows elementFromPoint /
      // native focus for content beneath it -- the box itself lives on the
      // INNER div (identical to LFlex's own rendering) so it still anchors
      // its children's absolute positioning. Interactive DOM leaves (inputs,
      // links, .ui-i) opt back in via the injected CSS. Koka hit-testing is
      // unaffected (root listeners).
      html/elem("div", [style("display:contents;pointer-events:none")],
        [html/elem("div", [style(pos-style(x, y, w0, h0))] ++ extra,
          children.map(fn(entry) entry.thd.pretend-decreasing.node-html(entry.fst, entry.snd, [], evch)))])
    LMemo(_, _, _, _, child) ->
      child.node-html(x, y, extra, evch)
    LRotate(_, deg, w0, h0, child) ->
      // paint-only rotation about the child's center (positions unrotated)
      html/elem("div",
        [style(pos-style(x, y, w0, h0)
               ++ ";transform:rotate(" ++ deg.show ++ "deg);transform-origin:center center")] ++ extra,
        [child.node-html(0.0, 0.0, [], evch)])
    LOverlay(_, w0, h0, child) ->
      // painted at its natural size, but `pointer-events:none` so it can never
      // take the click that started it (the Koka hit walk skips it too)
      html/elem("div",
        [style(pos-style(x, y, w0, h0) ++ ";pointer-events:none")] ++ extra,
        [child.node-html(0.0, 0.0, [], evch)])
    LClip(_, r, w0, h0, child) ->
      // the browser's own clip: `overflow:hidden` plus a matching
      // `border-radius`, which is exactly what native's ClipRoundedRect does.
      // The child is positioned at the clip's origin, so anything it paints
      // outside (an expanding ripple) is cut by the box rather than spilling.
      html/elem("div",
        [style(pos-style(x, y, w0, h0)
               ++ ";overflow:hidden"
               ++ (if r > 0.0 then ";border-radius:" ++ r.show ++ "px" else ""))] ++ extra,
        [child.node-html(0.0, 0.0, [], evch)])
    LTransform3d(_, m3, w0, h0, child) ->
      // paint-only 4x4 about the child's center (positions unchanged); CSS
      // `matrix3d(...)` reads its 16 args COLUMN-major, same as `m3.css3d`
      html/elem("div",
        [style(pos-style(x, y, w0, h0)
               ++ ";transform:matrix3d(" ++ m3.css3d ++ ");transform-origin:center center")] ++ extra,
        [child.node-html(0.0, 0.0, [], evch)])
    LBox(_, bg, on, w0, h0, dx, dy, child) ->
      val bg-style = match bg
        Just(Fill(color, radius, src)) ->
          val paint = match src
            Nothing -> color.to-css
            Just(SLinear(fx, fy, tx, ty, c0, c1)) ->
              // CSS angles are clockwise from "to top", so a screen-space
              // direction (dx, dy) is atan2(dx, -dy)
              val ang = atan2(tx - fx, 0.0 - (ty - fy)) * 180.0 / pi
              "linear-gradient(" ++ ang.show-fixed(2) ++ "deg," ++ c0.to-css ++ "," ++ c1.to-css ++ ")"
            Just(SRadial(cx, cy, rad, c0, c1)) ->
              // CSS only accepts a LENGTH for a circle's radius -- a percentage
              // is legal for `ellipse` alone, and a percentage here makes the
              // whole declaration invalid, which the browser drops silently.
              // The box's pixel size is in hand, so resolve the fractions to px
              // exactly as the native side resolves them to absolute points.
              "radial-gradient(circle " ++ (rad * w0).show-fixed(2) ++ "px at "
                ++ (cx * w0).show-fixed(2) ++ "px " ++ (cy * h0).show-fixed(2) ++ "px,"
                ++ c0.to-css ++ "," ++ c1.to-css ++ ")"
            Just(SImage(isrc, ifit)) ->
              // `background-size` is exactly `object-fit` for a background box
              val size = match ifit
                Cover   -> "cover"
                Contain -> "contain"
                _       -> "100% 100%"   // Fill: stretch to the box
              "url(\"" ++ isrc ++ "\") center / " ++ size ++ " no-repeat"
          ";background:" ++ paint ++ ";border-radius:" ++ px(radius)
        Nothing -> ""
      // ALL pointer roles (click / click-at / context-at / drag / drop) are
      // handled by root hit-testing -- unified with native -- so no per-element
      // DOM listeners and no `draggable`/`ondrop`. `.ui-i` gives a clickable box
      // its CSS hover brightness; a drag source shows a grab cursor.
      val clickable = on.click.is-just || on.click-at.is-just || on.context-at.is-just
      val cursor = if on.drag.is-just then ";cursor:grab"
                   elif clickable then ";cursor:pointer" else ""
      val attrs =
        [style(pos-style(x, y, w0, h0) ++ bg-style ++ cursor)]
        ++ (if clickable then [attr("class", "ui-i")] else [])
        ++ extra
      html/elem("div", attrs, [child.node-html(dx, dy, [], evch)])
    LFlex(_, w0, h0, children) ->
      html/elem("div", [style(pos-style(x, y, w0, h0))] ++ extra,
        children.map(fn(entry) entry.thd.pretend-decreasing.node-html(entry.fst, entry.snd, [], evch)))
    LField(_, key, _, ph, onenter, w0, h0) ->
      html/input(
        [style(pos-style(x, y, w0, h0)), html/value(field-text(key)), placeholder(ph),
         on-value-do("input", fn(s) post(evch, EvField(key, s)))]
        ++ (match onenter { Just(g) -> [on-enter-value(g)]; Nothing -> [] })
        ++ extra)
    LActMsg(_, _, w0, h0, dx, dy, child) ->
      // click handled by root hit-testing (HitMsgIoc); just position the child
      child.node-html(x + dx, y + dy, extra, evch)
    LInput(_, _, value, ph, oninput, onkey, w0, h0) ->
      html/input(
        [style(pos-style(x, y, w0, h0)), html/value(value), placeholder(ph), on-input(oninput)]
        ++ extra
        ++ (match onkey { Just(g) -> [on-key(g)]; Nothing -> [] }))
    LSlider(_, lo, hi, step0, value, onchange, w0, h0) ->
      html/input(
        [style(pos-style(x, y, w0, h0)), type_("range"),
         attr("min", lo.show), attr("max", hi.show),
         attr("step", if step0 <= 0.0 then "any" else step0.show),
         html/value(value.show),
         on-input(fn(s) onchange(s.parse-float64.default(value)))] ++ extra)
    LImage(_, src, fit, w0, h0) ->
      // the browser fetches + decodes (path or URL, same as any `<img src>`);
      // `object-fit`/`object-position` map the decoded pixels onto the box
      // exactly like native's (task 5) texture placement will
      html/elem("img",
        [attr("src", src),
         style(pos-style(x, y, w0, h0) ++ ";object-fit:" ++ fit-css(fit) ++ ";object-position:center")]
        ++ extra, [])
