/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Headless UI / integration testing for lib/ui apps.
//
//   test-app( init, view, update ) fn(t)
//     t.click("add")
//     t.type-text("what", "buy milk")
//     t.click("add")
//     t.settle()
//     check-eq("todo appears", t.texts("list").any(fn(s) s == "buy milk"), True)
//
// The harness IS the app runtime minus the platform: the same channels
// (messages, ui/state transitions), the same strand interleaving, the same
// uistate/keytrie handlers, the same layout/reconcile -- driven by a TEST
// backend whose "screen" is the laid-out ltree and whose "platform events"
// are issued by the test script, which runs as just another strand of the
// app's one interleaving. A click dispatches through the SAME `hit` walk the
// real backends use, so what a test clicks is what a user can click.
//
// Widgets are addressed by SELECTOR (see ui/keytrie's selector-queries doc):
// a selector resolves against the harness's keytree to an owner identity
// (`find-ids`), and `owner-rect`/`owner-texts` (ui/widget) read that
// identity's geometry/text straight off the laid-out ltree -- a bare name is
// enough for a unique scope, exactly like the old string addressing it
// replaces, so most call sites are just the same name in a different clothes.
// Text metrics are DETERMINISTIC (a fixed-width model), so layout -- and
// therefore hit-testing -- is identical on every host: the same test binary
// runs under native, node, or wasmtime with no window, display, or browser.
//
// Checks follow koka-community's std/test in spirit (labels + expected vs
// got, ok/FAIL lines, nonzero exit on failure) at MVP size.
module ui/test

import std/num/float64
import std/core/undiv
import std/async
import std/async/interleave
import std/time/duration
import std/num/int32
import ui/widget
import ui/state
import ui/async      // future-boundary want-channel + async-pump strand
pub import ui/view   // scene effect in view signatures
import ui/keytrie
pub import ui/dispatch   // update's `spawn` doorway (re-exported for test mains)

// ----------------------------------------------------------------
// deterministic text metrics: a fixed-width character model. Not typographic
// truth -- STABLE truth: the same string always measures the same on every
// host, which is what layout assertions need.

pub fun with-test-measure( action : () -> <measure|e> a ) : e a
  with handler
    fun measure-text( content : string, font : font, max-w : float64 )
      val cw = font.size * 0.6
      val lh = font.size * 1.25
      val n  = content.count
      val w  = n.float64 * cw
      if w <= max-w then (w.max(0.0), lh) else
        val per   = (max-w / cw).int.max(1)          // chars per line
        val lines = (n + per - 1) / per              // ceil(n / per)
        (max-w, lines.float64 * lh)
    fun measure-rich( content : string, base-font : font, spans : list<(int,int,maybe<font>)>,
                      max-w : float64 )
      // every span here uses base-font's cw for simplicity (a real
      // per-span-width model isn't needed to prove wrap/hit-test LOGIC,
      // only that rects come out non-overlapping and geometrically sane) --
      // the font override is accepted for signature parity with the real
      // handlers but unused by this fixed-width model.
      // `wrap` isn't a parameter here (nor on `measure-text`): `layout`
      // already folds it into `max-w` via the `unbounded-w` sentinel before
      // calling in, so the SAME threshold `measure-text`'s callers use
      // (`is-unbounded`) recovers it here.
      val wrap = max-w.is-unbounded.not
      val cw = base-font.size * 0.6
      val lh = base-font.size * 1.25
      val n  = content.count
      val per = if wrap then (max-w / cw).int.max(1) else n.max(1)   // chars per line
      fun rect-for( start : int, end : int ) : list<(float64,float64,float64,float64)>
        // walk [start,end) in per-line chunks, one rect per line it touches
        // (pos strictly increases each step and is bounded by `end`, so this
        // terminates -- `pretend-no-div` discharges the `div` Koka can't
        // infer from a non-structural recursion)
        fun go( pos : int, acc : list<(float64,float64,float64,float64)> ) : <div> list<(float64,float64,float64,float64)>
          if pos >= end then acc.reverse
          else
            val line = pos / per
            val line-end = ((line + 1) * per).min(end)
            val x = (pos % per).float64 * cw
            val w = (line-end - pos).float64 * cw
            val y = line.float64 * lh
            go(line-end, Cons((x, y, w, lh), acc))
        pretend-no-div( fn() go(start, []) )
      val lines = if n == 0 then 1 else (n + per - 1) / per
      // shrink-wrap: content that fits on one line reports its actual width,
      // matching `measure-text`'s `if w <= max-w then w else max-w` -- a
      // short string in a wide container must NOT report the full `max-w`.
      val total-w = if wrap then (n.min(per).float64 * cw) else n.float64 * cw
      val total-h = lines.float64 * lh
      fun rect-for-span( sp : (int,int,maybe<font>) ) : list<(float64,float64,float64,float64)>
        val (s, e, _) = sp
        rect-for(s, e)
      val rects = spans.map(rect-for-span)
      (total-w, total-h, rects)
  action()

// ----------------------------------------------------------------
// the driver handed to a test script: the current laid-out scene + the app's
// real message channel. Everything else is functions over these.

pub struct tester<a>
  get-tree   : () -> ioc ltree<a>
  emit       : a -> ioc ()
  sync       : () -> <async,ioc> ()                       // one settle round-trip (see `settle`)
  send-click : (float64, float64) -> <uistate,ioc> ()     // a primary click at a point
  send-text  : (string) -> <uistate,ioc,exn> ()           // text to the FOCUSED field
  send-key   : (string) -> <uistate,ioc,exn> ()           // "Enter" | "Backspace" | "Escape" to the FOCUSED field
  send-hover : (float64, float64) -> <uistate,ioc> ()     // move the pointer to a point
  send-scroll: (float64, float64, float64) -> <uistate,ioc,exn> ()  // wheel dy at a point (dy > 0 = wheel up)

// resolve a selector to the single MOUNTED identity it names: `Nothing` if
// nothing matches; throws (through the same check/throw path as every other
// tester failure) listing every matching path via `segment/show` if the
// selector is ambiguous, so the failure names exactly what to disambiguate
// with (an ancestor-qualifying earlier step). `find-ids` scans the keytrie's
// whole id->path table, which retains KeepAlive-but-unmounted ids -- filter
// to those actually present in `tree` this frame before the ambiguity
// decision, so a retained ghost never masks a real unique match.
fun resolve1( tree : ltree<a>, sel : string ) : <keytree,exn> maybe<int>
  match find-ids(sel).filter(fn(id) pretend-no-div( fn() tree.owner-present(id) ))
    Nil -> Nothing
    Cons(id, Nil) -> Just(id)
    ids -> throw( "ui/test: selector \"" ++ sel ++ "\" is ambiguous, matches:\n" ++
                   ids.map(fn(id) "  " ++ id.show ++ " " ++ kt-path(id).map(segment/show).join).join("\n") )

// the laid-out rect (x,y,w,h) of the selector's target, if mounted (and not
// entirely scrolled out of an enclosing viewport -- see `owner-rect`'s clip)
pub fun find( t : tester<a>, sel : string )
  val tree = (t.get-tree)()
  match resolve1(tree, sel)
    Just(id) -> pretend-no-div( fn() tree.owner-rect(id) )
    Nothing -> Nothing

// click the CENTER of the selector's target; fails the test if nothing
// matches. The DRIVER decides what a click is: headless dispatches through
// the shared `hit` walk; live injects a synthetic pointer event into the
// real host.
pub fun click( t : tester<a>, sel : string )
  match t.find(sel)
    Just((x, y, w, h)) -> (t.send-click)(x + w / 2.0, y + h / 2.0)
    Nothing -> throw("ui/test: click(\"" ++ sel ++ "\"): no widget matches that selector")

pub fun click-at( t : tester<a>, px : float64, py : float64 )
  (t.send-click)(px, py)

// focus the field under the selector (a click) and type into it
pub fun type-text( t : tester<a>, sel : string, s : string )
  t.click(sel)
  (t.sync)()   // focus lands via a queued ui/state transition -- let it apply
  (t.send-text)(s)

// press a special key ("Enter" | "Backspace" | "Escape") on whatever is
// focused -- Enter commits a field's on-enter, Backspace edits, Escape blurs
pub fun press-key( t : tester<a>, key : string )
  (t.send-key)(key)

// move the pointer over the CENTER of the selector's target (hover
// affordances, `interactive` hovered state)
pub fun hover( t : tester<a>, sel : string )
  match t.find(sel)
    Just((x, y, w, h)) -> (t.send-hover)(x + w / 2.0, y + h / 2.0)
    Nothing -> throw("ui/test: hover(\"" ++ sel ++ "\"): no widget matches that selector")

// wheel-scroll the region under the CENTER of the selector's target by `dy`
// (dy < 0 scrolls DOWN, revealing later content -- wheel semantics)
pub fun scroll( t : tester<a>, sel : string, dy : float64 )
  match t.find(sel)
    Just((x, y, w, h)) -> (t.send-scroll)(x + w / 2.0, y + h / 2.0, dy)
    Nothing -> throw("ui/test: scroll(\"" ++ sel ++ "\"): no widget matches that selector")

// the HEADLESS click dispatch -- the SAME arms as the real backends' pointer
// handling (ui/api/impeller/backend.kk drain-pointers). Shared with test-app
// below; the live driver replaces it with host-level event injection.
pub fun dispatch-click( tree : ltree<a>, emit : a -> ioc (), px : float64, py : float64 ) : <uistate,ioc> ()
  match pretend-no-div( fn() tree.hit(px, py) )
    Just(HitMsg(m))        -> emit(m)
    Just(HitAt(g, hx, hy)) -> emit(g(hx, hy))
    Just(HitSlider(g, v))  -> emit(g(v))
    Just(HitLink(_to))     -> ()   // route navigation is host-side (hash/url); assert on the link's presence instead
    Just(HitAct(thunk))    -> thunk()
    Just(HitMsgIoc(g))     -> emit(g())
    Just(HitInput(k))      -> set-focused(Just(k))
    Nothing ->
      match get-focused()
        Just(_) -> set-focused(Nothing)   // click elsewhere: blur (real backend behavior)
        Nothing -> ()

// let the app quiesce: everything a click/emit queued (message loop, ui/state
// transitions, the renders they trigger) runs before this returns. Each round
// is a round-trip through the app's own state channel: FIFO order means every
// transition queued before it has applied (and re-rendered) when the sentinel
// runs; two rounds flush work that the first round's work queued.
pub fun settle( t : tester<a> ) : <async,ioc> ()
  (t.sync)()
  (t.sync)()

// all visible text inside the selector's target subtree ("" = the whole
// scene), in paint order -- field/input values and placeholders included. A
// selector that matches nothing (e.g. a `window()` view not currently open)
// reads as `[]`, the same "nothing there" reading `find` gives -- distinct
// from a mounted but empty subtree, which also reads `[]`.
pub fun texts( t : tester<a>, sel : string = "" )
  val tree = (t.get-tree)()
  if sel == "" then pretend-no-div( fn() collect-texts(tree) ) else
    match resolve1(tree, sel)
      Just(id) -> pretend-no-div( fn() tree.owner-texts(id) )
      Nothing  -> []

fun collect-texts<msg>( t : ltree<msg> ) : div list<string>
  match t
    LText(_, content, _, _, _, _, _) -> [content]
    LRich(_, content, _, _, _, _, _, _, _) -> [content]
    LField(_, _, value, ph, _, _, _) -> [if value == "" then ph else value]
    LInput(_, _, value, ph, _, _, _, _) -> [if value == "" then ph else value]
    LLayer(_, _, _, children) -> children.flatmap(fn(e) e.thd.collect-texts)
    LBox(_, _, _, _, _, _, _, child) -> child.collect-texts
    LFlex(_, _, _, children) -> children.flatmap(fn(e) e.thd.collect-texts)
    LLink(_, _, _, _, _, _, child) -> child.collect-texts
    LAct(_, _, _, _, _, _, child) -> child.collect-texts
    LActMsg(_, _, _, _, _, _, child) -> child.collect-texts
    LInteractive(_, _, _, _, _, _, _, _, child) -> child.collect-texts
    LRotate(_, _, _, _, child) -> child.collect-texts
    LMemo(_, _, _, _, child) -> child.collect-texts
    LScroll(_, _, _, _, _, _, _, child) -> child.collect-texts
    _ -> []

// ----------------------------------------------------------------
// checks: labeled assertions collected by the harness; a failed check does
// not abort the script (you see every failure of a run at once)

// the string without its last character (a Backspace edit)
fun drop-last( s : string ) : string
  val n = s.count
  if n <= 1 then "" else s.first(n - 1).string

// process exit with a code (stdlib has no portable `exit`); used for the
// failure path -- a thrown exception would be swallowed by the interleaving's
// strand cancellation and the process would still exit 0
extern test-exit( code : int32 ) : ioc ()
  c inline "(exit((int)(#1)), kk_Unit)"
  js inline "(typeof process !== 'undefined' ? process.exit(#1) : undefined)"

pub effect uicheck
  fun report-check( ok : bool, label : string, detail : string ) : ()

pub fun check( label : string, ok : bool, detail : string = "" ) : uicheck ()
  report-check(ok, label, detail)

pub fun check-eq<a>( label : string, actual : a, expected : a,
                     ?(==) : (a, a) -> bool, ?show : a -> string ) : uicheck ()
  report-check(actual == expected, label,
               "expected " ++ expected.show ++ ", got " ++ actual.show)

// ----------------------------------------------------------------
// the harness: the app runtime minus the platform. Mirrors ui/app run-single
// (same channels, same strand layout); `script` replaces the platform pump.

pub fun test-app<model,msg>( name : string,
                             init : model,
                             view : (model, key) -> <keytree,uistate,scene<msg>,ioc> widget<msg>,
                             update : (model, msg) -> dispatch<msg> model,
                             script : (tester<msg>) -> <async,keytree,uistate,uicheck,ioc,exn> (),
                             config : app-config = App-config(),
                             scrollbar : (scroll-info, scroll-axis) -> ioc widget<msg> = neutral-scrollbar ) : <async,ioc,exn> ()
  test-scenarios(name, init, view, update, [("", script)], config, scrollbar)

// several named scenarios against ONE app instance: model + ephemeral state
// + scene reset between scenarios, one combined report, one exit code
pub fun test-scenarios<model,msg>( name : string,
                             init : model,
                             view : (model, key) -> <keytree,uistate,scene<msg>,ioc> widget<msg>,
                             update : (model, msg) -> dispatch<msg> model,
                             scenarios : list<(string, (tester<msg>) -> <async,keytree,uistate,uicheck,ioc,exn> ())>,
                             config : app-config = App-config(),
                             scrollbar : (scroll-info, scroll-axis) -> ioc widget<msg> = neutral-scrollbar ) : <async,ioc,exn> ()
  var fails := 0
  var count := 0
  with handler
    fun report-check( ok, label, detail )
      count := count + 1
      if ok then println("  ok   " ++ label)
      else
        fails := fails + 1
        println("  FAIL " ++ label ++ (if detail == "" then "" else ": " ++ detail))
  println("ui/test: " ++ name)
  with with-uistate
  with with-keytree
  val ch = channel()
  val emit = fn(m) ch.emit-io(m)
  // window()/Panel views are laid out at the harness's fixed window size for
  // hit-testing purposes; a plain `stack` append via `flatten` is acceptable
  // for the headless tier and keeps ONE walk (find/texts/dispatch-click all
  // reach both the main composite AND every window's content this way)
  fun composed( m )
    val s = with-scene( fn() view(m, root-key), scrollbar ).finish
    s.flatten(rect-of-snapshot())
  val state-ch : channel<() -> <uistate,ioc> ()> = channel()
  install-state-channel(state-ch)
  val async-ch : channel<async-want> = channel()   // future-boundary wants -> async-pump
  install-async-channel(async-ch)
  val frame-ch : channel<()> = channel()
  install-frame-channel(frame-ch)
  val cons = tight(config.width.float64, config.height.float64)
  // layout, then BAKE each scroll region's ui/state offset into its LScroll node
  // -- exactly what the native/web backends do before hit-testing and owner
  // geometry (`bake-scroll` in ui/api/{impeller,web}/backend.kk). Without it
  // the tree the harness hit-tests/addresses keeps offset 0, so a scrolled
  // list's items sit at their un-shifted absolute y (below the viewport): `hit`
  // clips them away and, since `owner-rect` clips too, `find` would miss them
  // -- diverging from what a real backend paints and lets the user click.
  fun laid( w )
    with with-test-measure
    pretend-no-div( fn() w.layout(cons) ).bake-scroll
  fun re-laid( old, w )
    with with-test-measure
    pretend-no-div( fn() reconcile(old, w, cons) ).bake-scroll
  val model-ref = ref(init)
  val tree-ref  = ref(laid(composed(init)))
  // publish scroll metrics, exactly like the real backends do "at
  // paint/layout time" (ui/state's `sync-scroll-metrics` doc comment) -- a
  // headless build that reads `scroll-state` (e.g. `ui/lazy`'s windowing)
  // otherwise never sees a nonzero viewport/content, since nothing else in
  // this harness calls it. One frame behind, same as the real backends: this
  // frame's layout feeds the NEXT build, not the one that produced it.
  fun publish-scroll()
    if sync-scroll-metrics(!tree-ref) then request-render()
  publish-scroll()
  fun rerender()
    flush-dirty()
    tree-ref := re-laid(!tree-ref, composed(!model-ref))
    publish-scroll()
    frame-done()
  fun sync-once() : <async,ioc> ()
    val done = channel()
    state-ch.emit-io( fn() done.emit-io(()) )
    done.receive
  fun headless-text( s2 : string ) : <uistate,ioc,exn> ()
    match get-focused()
      Just(k) ->
        match pretend-no-div( fn() (!tree-ref).input-with-key(k) )
          Just(LInput(_, _, value, _, oninput, _, _, _)) -> ch.emit-io(oninput(value ++ s2))  // controlled: through the model
          _ -> set-field-text(k, field-text(k) ++ s2)                                // uncontrolled: ui/state
      Nothing -> throw("ui/test: type-text: clicking the target focused no input field")
  // special keys: the SAME semantics as the backends' drain-text key arms
  fun headless-key( key : string ) : <uistate,ioc,exn> ()
    if key == "Escape" then set-focused(Nothing)
    else
      match get-focused()
        Just(k) ->
          match pretend-no-div( fn() (!tree-ref).input-with-key(k) )
            Just(LInput(_, _, value, _, oninput, onkey, _, _)) ->
              if key == "Backspace" then ch.emit-io(oninput(value.drop-last))
              elif key == "Enter" then
                match onkey
                  Just(g) -> ch.emit-io(g("Enter"))
                  Nothing -> ()
              else throw("ui/test: press-key: unknown key " ++ key)
            Just(LField(_, fk, _, _, onenter, _, _)) ->
              if key == "Backspace" then edit-field-text(fk, fn(v) v.drop-last)
              elif key == "Enter" then
                match onenter
                  Just(g) -> with-field-text(fk, fn(v) ch.emit-io(g(v)))
                  Nothing -> ()
              else throw("ui/test: press-key: unknown key " ++ key)
            _ -> ()
        Nothing -> throw("ui/test: press-key(\"" ++ key ++ "\"): nothing is focused")
  // hover: the pump's interactive-hover write (`interactive` builders read it)
  fun headless-hover( px : float64, py : float64 ) : <uistate,ioc> ()
    set-hovered(pretend-no-div( fn() (!tree-ref).hover-key(px, py) ))
  // wheel: the SAME clamp semantics as the backends' drain-scroll
  fun headless-scroll( px : float64, py : float64, dy : float64 ) : <uistate,ioc,exn> ()
    match pretend-no-div( fn() (!tree-ref).scroll-at(px, py) )
      Cons((k, content, vp, _horizontal), _) ->
        val maxoff = (content - vp).max(0.0)
        set-scroll-offset(k, (scroll-offset(k) - dy).max(0.0).min(maxoff))
        request-render()
      Nil -> throw("ui/test: scroll: no scroll region under that point")
  val t = Tester( fn() !tree-ref, fn(m) ch.emit-io(m), fn() sync-once(),
                  fn(px, py) dispatch-click(!tree-ref, fn(m) ch.emit-io(m), px, py),
                  fn(s2) headless-text(s2),
                  fn(k2) headless-key(k2),
                  fn(px, py) headless-hover(px, py),
                  fn(px, py, dy) headless-scroll(px, py, dy) )
  fun reset-app()   // between scenarios: model, ephemeral state, a fresh scene
    reset-state()
    model-ref := init
    invalidate-frame()
    tree-ref := laid(composed(init))
    publish-scroll()
    frame-done()
  forking fn(fork)
    fun msg-loop()
      val msg = ch.receive
      val tasks = ref([])
      val model2 =
        with fun spawn(task)
          tasks := Cons(task, !tasks)
        update(!model-ref, msg)
      model-ref := model2
      invalidate-frame()   // model changed: full rebuild (same rule as ui/app)
      tree-ref := re-laid(!tree-ref, composed(model2))
      publish-scroll()
      frame-done()
      (!tasks).foreach fn(task)
        fork( fn() ch.emit-io(task()) )
      msg-loop()
    // the anim-driver's role, deterministic: every frame REQUEST advances the
    // clock exactly one 16ms frame and re-renders -- animations progress a
    // fixed step per queued frame, so tests never race wall time
    fun frame-loop()
      frame-ch.receive
      take-frame-request()
      tick-clock(16.0)
      rerender()
      frame-loop()
    fork( fn() drain-state(rerender) )   // ui/state writes -> re-render, as in ui/app
    fork( fn() async-pump(fork) )        // future-boundary runs, as in ui/app
    fork( fn() msg-loop() )              // the message loop, as in ui/app
    fork( fn() frame-loop() )            // frame demand (request-frame) sink
    // the "platform": the test script strand. NOTE the summary must print
    // HERE: when the main strand finishes, forking CANCELS the parked loop
    // strands and the cancellation takes test-app's continuation with it --
    // code after `forking` never runs (ui/app never has any either).
    fun on-err( err : exception )
      fails := fails + 1
      println("  FAIL (exception): " ++ err.show)
    scenarios.foreach fn(sc)
      val (sname, sscript) = sc
      if sname != "" then
        println("  -- " ++ sname)
        reset-app()
      handle/try(on-err) fn()
        sscript(t)
    if fails > 0
      then
        println("ui/test: " ++ name ++ ": " ++ fails.show ++ " of " ++ count.show ++ " checks FAILED")
        test-exit(1.int32)   // explicit: an exn is swallowed by strand cancellation
      else println("ui/test: " ++ name ++ ": " ++ count.show ++ " checks passed")
