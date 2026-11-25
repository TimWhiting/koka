/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The LIVE (middleman) driver for ui/test: the same tester API, but events
// are INJECTED into the real platform host and the production pipeline runs
// -- real text measurement, real layout, real paint/present, and the real
// input path (the backend's pump drains a synthetic pointer event from the
// same ring buffer a GLFW callback fills; it cannot tell the difference).
//
// One script, two tiers: pass the SAME script to ui/test's `test-app`
// (headless: deterministic metrics, no window, milliseconds -- app logic)
// and to `live-app` here (a real window -- backend integration; this tier
// catches paint/measure/input bugs the headless tier cannot see).
//
// live-app mirrors ui/app's single-thread runtime (same channels and strand
// layout, plus one extra strand: the test script). Queries walk the scene
// the backend REGISTERS after each render (test-scene-any), so find/texts
// address the very tree that was painted.
//
// ---- secondary (real OS) windows on the native live tier ----
//
// The tester struct (ui/test) is SHARED between the headless and live
// drivers and its public fields are NOT window-aware (get-tree returns ONE
// tree; send-click/hover/scroll take only (x,y)). Rather than change that
// shared surface, this driver folds the backend's main tree AND every
// currently-mounted secondary window's tree into ONE combined tree that
// `find`/`click`/`texts`/etc. (all defined once, in ui/test, over `get-tree`)
// walk exactly as they walk the headless composite -- so no code in ui/test
// itself needs to know windows exist.
//
// The fold is a synthetic LFlex whose children are offset FAR apart on the
// x-axis: the main tree at (0,0), and window k (1-based, in backend mount
// order) at (`win-slot-w` * k, 0). Window trees are already window-LOCAL
// (the backend never publishes their rects into the main tree's geometry),
// so no coordinate translation is needed beyond that offset -- `find`'s
// `owner-rect` walk naturally reports a widget inside window k at
// x in [k*win-slot-w, (k+1)*win-slot-w). `win-slot-w` (100000px) is far
// larger than any real window, so the slots never overlap.
//
// `click`/`hover`/`scroll` (ui/test) resolve a name to a rect via that
// combined tree, then call send-click/send-hover/send-scroll(x, y) -- so
// THIS driver's send-* closures are where the coordinate decodes back into
// (window id, window-local x): `route(x)` divides by `win-slot-w` to
// recover the slot, 0 = main. That window id is passed to
// test-inject-click/-hover/-scroll-at's `win` parameter (backend.kk), which
// forwards to the impeller injectors -- the SAME ring buffer a real GLFW
// callback on that window would fill.
//
// send-text/send-key take no coordinate (they target "whatever is
// focused"), so they can't be routed by decoding an (x,y). Real keyboard
// input follows the OS's key-window focus, which our synthetic pointer
// injection does NOT change (GLFW's synthetic path has no window-manager
// focus semantics) -- so this driver tracks the last window a click/hover
// routed to, in `last-vkey-ref`, and sends chars/keys to THAT window's input
// ring explicitly. This matches how a test script naturally reads: click a
// field inside a window, then type-text/press-key follow it there.
//
// `last-vkey-ref` stores the routed window's VIEW KEY (a string), not its
// numeric host slot id -- host slot ids get reused (`imp_host_open_window`
// hands out the first free slot), so if window A closes and a new window B
// is opened before the next send-text/send-key, B could inherit A's old slot
// id and silently receive input meant to fall back to main. A view key is
// stable and unique for as long as that view's window exists, so at
// injection time we re-resolve vkey -> slot id via `test-window-id` and fall
// back to 0 (main) whenever that vkey is no longer a live window (closed, or
// never routed to) -- stale slot reuse becomes harmless by construction.
//
// What this tier covers for windows: injecting real host events (click,
// hover, scroll, and char/key on the last-routed window) into ANY mounted
// window by its selector-addressed identities; asserting retention/dismiss behavior
// via the app's own messages (close-button widgets, `on-dismiss`), since
// those run through the SAME update/render path as everything else.
//
// What it does NOT cover: native window-chrome close-button dismissal --
// GLFW has no synthetic "click the OS close box", so window-close-requested
// paths are exercised headless only (ui/test, which drives them via
// messages/state directly); Panel SCREEN-position assertions -- a live
// Panel's on-screen (x,y) depends on the host's real window manager and
// multi-monitor layout, so this tier only asserts a Panel window is ALIVE
// and its CONTENT is reachable, not its absolute screen geometry; and OS
// focus semantics in general (which window the desktop considers "key" --
// see the send-text/send-key note above).
module ui/test-live

import std/num/float64
import std/async
import std/async/interleave
import std/time/duration
import ui/widget
import ui/state
import ui/async     // async-pump / install-async-channel / async-want (task #53)
import ui/view
import ui/keytrie
import ui/backend
import ui/test
pub import ui/dispatch

// the combined-tree window-slot width -- see the module doc comment above.
// Far larger than any real window, so slots never overlap.
val win-slot-w : float64 = 100000.0

// live-app: the real app + a script strand. Exits the process when the
// script completes (0 = all checks passed, 1 = failures).
pub fun live-app<model,msg>( name : string,
                             init : model,
                             view : (model, key) -> <keytree,uistate,scene<msg>,ioc> widget<msg>,
                             update : (model, msg) -> dispatch<msg> model,
                             script : (tester<msg>) -> <async,keytree,uistate,uicheck,ioc,exn> (),
                             config : app-config = App-config(),
                             scrollbar : (scroll-info, scroll-axis) -> ioc widget<msg> = neutral-scrollbar ) : <async,ioc> ()
  live-scenarios(name, init, view, update, [("", script)], config, scrollbar)

// several named scenarios against ONE live app: model + ephemeral state reset
// between scenarios (the window stays up), one combined report + exit
pub fun live-scenarios<model,msg>( name : string,
                             init : model,
                             view : (model, key) -> <keytree,uistate,scene<msg>,ioc> widget<msg>,
                             update : (model, msg) -> dispatch<msg> model,
                             scenarios : list<(string, (tester<msg>) -> <async,keytree,uistate,uicheck,ioc,exn> ())>,
                             config : app-config = App-config(),
                             scrollbar : (scroll-info, scroll-axis) -> ioc widget<msg> = neutral-scrollbar ) : <async,ioc> ()
  println("ui/test-live: " ++ name)
  with handle/try fn(err)
    println("ui/test-live: uncaught exception: " ++ err.show)
  with-platform(config) fn()
    var fails := 0
    var count := 0
    with handler
      fun report-check( ok, label, detail )
        count := count + 1
        if ok then println("  ok   " ++ label)
        else
          fails := fails + 1
          println("  FAIL " ++ label ++ (if detail == "" then "" else ": " ++ detail))
    with with-uistate
    with with-keytree
    val ch = channel()
    val emit = fn(m) ch.emit-io(m)
    fun composed( m )
      with-scene( fn() view(m, root-key), scrollbar ).finish
    val state-ch : channel<() -> <uistate,ioc> ()> = channel()
    install-state-channel(state-ch)
    val frame-ch : channel<()> = channel()
    install-frame-channel(frame-ch)
    val async-ch : channel<async-want> = channel()   // future-boundary wants -> async-pump (task #53)
    install-async-channel(async-ch)
    val model-ref   = ref(init)
    val mounted-ref = ref(mount(composed(init), emit, config))
    fun rerender()
      flush-dirty()
      set-mounted(mounted-ref, render(!mounted-ref, composed(!model-ref)))
      frame-done()
    // the tester over the REAL pipeline: queries read the scene(s) the
    // backend registered at its last render; events go through host-level
    // injection. `live-tree()` folds main + every mounted window into ONE
    // combined tree -- see the module doc comment for the offset scheme.
    fun live-tree()
      val main-t = match test-scene-any()
        Just(t) -> unerase(t)
        Nothing -> LFlex(no-owner, 0.0, 0.0, [])    // before first registration (unreachable after mount)
      val win-kids = test-window-scenes().map-indexed fn(i, kv)
        val (_, te) = kv
        ((i + 1).float64 * win-slot-w, 0.0, unerase(te))
      LFlex(no-owner, 0.0, 0.0, Cons((0.0, 0.0, main-t), win-kids))
    // decode a combined-tree x-coordinate back into (window id, local x,
    // routed vkey) -- the inverse of live-tree's offset. 0/Nothing = main
    // window.
    val last-vkey-ref : ref<global,maybe<string>> = ref(Nothing)
    fun route( x : float64 ) : ioc (int, float64, maybe<string>)
      val slot = (x / win-slot-w).int
      if slot <= 0 then (0, x, Nothing)
      else
        val vkeys = test-window-scenes()
        match vkeys.drop(slot - 1)
          Cons((vkey, _), _) -> (test-window-id(vkey), x - slot.float64 * win-slot-w, Just(vkey))
          Nil -> (0, x, Nothing)   // stale index (window closed since `find` walked it): fall back to main
    fun routed-click( x : float64, y : float64 ) : <uistate,ioc> ()
      val (win, lx, vkey) = route(x)
      last-vkey-ref := vkey
      test-inject-click(lx, y, win)
    fun routed-hover( x : float64, y : float64 ) : <uistate,ioc> ()
      val (win, lx, vkey) = route(x)
      last-vkey-ref := vkey
      test-inject-hover(lx, y, win)
    fun routed-scroll( x : float64, y : float64, dy : float64 ) : <uistate,ioc,exn> ()
      val (win, lx, vkey) = route(x)
      last-vkey-ref := vkey
      test-inject-scroll-at(lx, y, dy, win)
    // re-resolve the last-routed vkey to a live host slot id at injection
    // time -- 0 (main) if that vkey is no longer a mounted window (closed,
    // or nothing has ever routed to a window yet). See the module doc
    // comment: this makes stale host-slot reuse harmless by construction.
    fun routed-win() : ioc int
      match !last-vkey-ref
        Nothing -> 0
        Just(vkey) -> match test-window-id(vkey)
          -1 -> 0
          id -> id
    val t = Tester( fn() live-tree(),
                    emit,
                    fn() wait(35.milli-seconds),   // ~2 real frames; the pump/loop strands drain meanwhile
                    fn(px, py) routed-click(px, py),
                    fn(s) test-inject-text(s, routed-win()),   // follows the last-clicked/-hovered window
                    fn(k2) test-inject-key(k2, routed-win()),
                    fn(px, py) routed-hover(px, py),
                    fn(px, py, dy) routed-scroll(px, py, dy) )
    forking fn(fork)
      fun msg-loop()
        val msg = ch.receive
        val tasks = ref([])
        val model2 =
          with fun spawn(task)
            tasks := Cons(task, !tasks)
          update(!model-ref, msg)
        set-model(model-ref, model2)
        invalidate-frame()   // model changed: full rebuild (same rule as ui/app)
        set-mounted(mounted-ref, render(!mounted-ref, composed(model2)))
        frame-done()
        (!tasks).foreach fn(task)
          fork( fn() ch.emit-io(task()) )
        msg-loop()
      fun frame-loop()   // real-time frame demand, as ui/app's anim-driver
        frame-ch.receive
        wait(frame-interval-ms().milli-seconds)
        take-frame-request()
        anim-tick(frame-interval-ms().float64)
        frame-loop()
      fork( fn() pump(!mounted-ref) )      // the REAL platform input pump
      fork( fn() drain-state(rerender) )
      fork( fn() async-pump(fork) )        // future-boundary runs (async images, task #53)
      fork( fn() msg-loop() )
      fork( fn() frame-loop() )
      // the script strand: give the app one settle to mount/present first
      wait(50.milli-seconds)
      fun on-err( err : exception )
        fails := fails + 1
        println("  FAIL (exception): " ++ err.show)
      fun reset-app()   // between scenarios: model + ephemeral state + re-render
        // fixes #46: a scenario's tail input burst can still be IN FLIGHT --
        // injected into a host ring but not yet drained by the pump, or
        // drained into a state-ch transition but not yet applied -- when the
        // script moves on. Left alone, that residue surfaces LATE, against
        // the next scenario's freshly-reset (same-keyed, since widget
        // identity is deterministic across a reset render) field, as a stray
        // leading character. Discard/flush BOTH stages before wiping the
        // store: nothing stale can land after this point.
        test-drain-rings()
        flush-pending-transitions()
        reset-state()
        set-model(model-ref, init)
        invalidate-frame()
        set-mounted(mounted-ref, render(!mounted-ref, composed(init)))
        frame-done()
      scenarios.foreach fn(sc)
        val (sname, sscript) = sc
        if sname != "" then
          println("  -- " ++ sname)
          reset-app()
        handle/try(on-err) fn()
          sscript(t)
      if fails > 0
        then
          println("ui/test-live: " ++ name ++ ": " ++ fails.show ++ " of " ++ count.show ++ " checks FAILED")
          test-report("uitest:fail:" ++ fails.show ++ "/" ++ count.show)   // browser probe (document.title)
          live-exit(1)
        else
          println("ui/test-live: " ++ name ++ ": " ++ count.show ++ " checks passed")
          test-report("uitest:pass:" ++ count.show)
          live-exit(0)

fun set-model( r : ref<global,a>, v : a ) : ioc ()   // avoid field-setter sugar collision
  val rr = r
  rr := v

fun set-mounted( r : ref<global,a>, v : a ) : ioc ()
  val rr = r
  rr := v

// hard process exit: the platform loop parks the main thread; a clean unwind
// is not available once the window is up (same reason the backends _Exit)
extern live-exit( code : int ) : ioc ()
  c  inline "(exit((int)(kk_integer_clamp32(#1,kk_context()))), kk_Unit)"
  js inline "((typeof process !== 'undefined' && process.exit) ? process.exit(#1) : undefined)"
