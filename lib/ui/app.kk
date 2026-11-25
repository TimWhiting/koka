/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// The app runtime: one Elm-style loop for every backend.
//
//   app( init, view, update )
//
// - one message channel; every input event is a message value routed into it
// - `update` is continuation-free: the `dispatch` effect's `fun spawn` is the
//   only doorway to async work, and the task runs OUTSIDE the UI path
// - no Cmd: spawn's task IS the async action, its result is a message
// - no Sub machinery: a subscription is any strand emitting into the channel
// - the whole app is ONE interleaving (`forking`): the loop, the platform
//   input pump, subscriptions, and spawned tasks are strands of it
module ui/app

import std/async
import std/async/interleave
import std/async/thread    // xchannel / spawn-thread / native-threads (threaded mode)
import std/num/float64
import std/time/duration
import std/time/timer     // ticks(): the monotonic clock behind real-dt anim frames
import ui/widget
import ui/state
import ui/async     // the future-boundary want-channel + async-pump strand
import ui/view      // scene composition: overlays / scrollbars / portals
import ui/backend
pub import ui/dispatch   // the `spawn` doorway for update (backend-free module)

fun set-ref<a>( r : ref<global,a>, v : a ) : ioc ()   // avoid field-setter sugar collision
  val rr = r
  rr := v

// Run an application: mount `view(init)` (a window natively, under the
// configured root element on web), then loop forever: receive a message,
// update, re-view, render. `view` may read ephemeral `ui/state` (it carries
// `st<global>`, which `ioc` admits, so a pure view still fits). The current
// model + mounted tree live in refs so BOTH the message loop and the
// `ui/state` transition strand re-render against the latest.
// `view` may emit VIEWS (overlays, portals) from anywhere via the `scene` effect
// -- the runtime installs the handler and composes them over the main content
// (see `with-scene`). A plain `ioc` view that emits nothing subsumes into this
// type unchanged, so existing apps need no edits; only portal-using views pick up
// `scene` (by inference, on the functions that actually emit).
//
// `scrollbar` builds the bar widget for an overflowing region that has no manual
// `scrollbar(...)`. It runs at composition time (outside any view's `theme`
// scope), so a themed builder must discharge its OWN theme (self-contained) --
// e.g. `scrollbar = fn(i,a){ with val theme = dark; themed-scrollbar(i,a) }`. It
// defaults to a neutral built-in bar. (Threading an ambient theme through the
// async render strands hits a Koka effect-row limitation, so the builder carries
// its theme instead.)
// Thread topology. `Single` (default) runs everything on one loop. `Threaded`
// runs `update` (+ subs + spawned tasks) on a dedicated worker thread and keeps
// layout / paint / the ltree / ui-state on the main thread -- so FBIP reconcile
// stays single-thread-owned. Threaded falls back to Single where there are no OS
// threads (web/wasi, `native-threads()` is False).
pub type app-threads
  Single
  Threaded

pub fun app<model,msg>( init : model,
                        view : (model, key : key) -> <keytree,uistate,scene<msg>,ioc> widget<msg>,
                        update : (model, msg) -> dispatch<msg> model,
                        config : app-config = App-config(),
                        scrollbar : (scroll-info, scroll-axis) -> ioc widget<msg> = neutral-scrollbar,
                        subs : list<(channel<msg>) -> <async,ioc> ()> = [],
                        threads : app-threads = Single ) : <async,ioc> ()
  with handle/try fn(err)
    println("koka/ui: uncaught exception: " ++ err.show)
  // the backend may split platform (GLFW main thread) from the app (render
  // thread) -- `body` is everything below; web runs it inline
  with-platform(config) fn()
    match threads
      Threaded | native-threads() -> run-threaded(init, view, update, config, scrollbar, subs)
      _                           -> run-single(init, view, update, config, scrollbar, subs)

// SINGLE-THREADED: one loop drives input, update, view, render, and ui/state.
fun run-single<model,msg>( init : model,
                           view : (model, key : key) -> <keytree,uistate,scene<msg>,ioc> widget<msg>,
                           update : (model, msg) -> dispatch<msg> model,
                           config : app-config, scrollbar : (scroll-info, scroll-axis) -> ioc widget<msg>,
                           subs : list<(channel<msg>) -> <async,ioc> ()> ) : <async,ioc,exn> ()
  with with-uistate      // the ephemeral-state store: handler-local, PER APP (no globals)
  with with-keytree      // the identity trie: ?key ids resolve through this handler
  val ch = channel()
  val emit = fn(m) ch.emit-io(m)
  // compose the scene (main content + emitted overlay/scrollbar views) HERE, so
  // the app's `view` builds the scene ambiently and the backend still receives a
  // single composited `ioc widget`.
  fun composed( m )   // : model -> <ioc|e> scene-out<msg> (annotation omitted: local fns can't name the outer type vars)
    with-scene( fn() view(m, root-key), scrollbar ).finish
  // channels BEFORE mount: transitions / frame requests emitted during the
  // mount build land in the channels and re-render normally
  val state-ch : channel<() -> <uistate,ioc> ()> = channel()
  install-state-channel(state-ch)
  val async-ch : channel<async-want> = channel()   // future-boundary wants -> async-pump
  install-async-channel(async-ch)
  val frame-ch : channel<()> = channel()
  install-frame-channel(frame-ch)
  val model-ref   = ref(init)
  val mounted-ref = ref(mount(composed(init), emit, config))
  fun rerender() : <keytree,uistate,ioc,exn> ()
    flush-dirty()      // pending dirty readers -> keytrie subtree bits (memo misses)
    set-ref(mounted-ref, render(!mounted-ref, composed(!model-ref)))
    frame-done()
  forking fn(fork)
    subs.foreach fn(s)
      fork( fn() s(ch) )
    fork( fn() pump(!mounted-ref) )     // platform input as a strand
    fork( fn() drain-state(rerender) )  // ui/state writes as a strand
    fork( fn() async-pump(fork) )       // future-boundary runs as a strand (idle until a boundary kicks)
    fork( fn() caret-blink() )          // caret animation (idle-cheap)
    fork( fn() anim-driver(frame-ch, 0.0, frame-interval-ms()) )  // demand-driven frame clock
    loop(ch, model-ref, mounted-ref, composed, update, fork)
  ()

// THREADED: the WORKER thread owns the model and runs update + subs + spawned
// tasks (its own async loop); the MAIN thread owns the window, ui-state, view and
// render. Only two immutable values cross, via thread-safe channels: a `msg`
// main->worker, and the new `model` worker->main. ui-state never crosses (view +
// on-act writes are all on main), so no state is shared between the threads.
fun run-threaded<model,msg>( init : model,
                             view : (model, key : key) -> <keytree,uistate,scene<msg>,ioc> widget<msg>,
                             update : (model, msg) -> dispatch<msg> model,
                             config : app-config, scrollbar : (scroll-info, scroll-axis) -> ioc widget<msg>,
                             subs : list<(channel<msg>) -> <async,ioc> ()> ) : <async,ioc,exn> ()
  with with-uistate      // main-thread ephemeral-state store (handler-local)
  with with-keytree      // main-thread identity trie (view/render run on main)
  fun composed( m )
    with-scene( fn() view(m, root-key), scrollbar ).finish
  // MAIN owns these; capture only the SENDERS for the worker (never the whole
  // xchannel -- that would hold main's Koka channel).
  val model-ch = xchannel()   // xchannel<model>        (worker -> main)
  val hand-ch  = xchannel()   // xchannel<xsender<msg>> (handshake: worker's msg-sender -> main)
  val model-send = model-ch.sender
  val hand-send  = hand-ch.sender
  // Mount the window NOW, on the clean action stack -- BEFORE the cross-thread
  // handshake receive. The handshake `xreceive` resumes its continuation INSIDE a
  // libuv async-delivery callback; the blocking GLFW/Metal window init cannot run
  // nested in that callback (it deadlocks), so `mount` must happen first. Input is
  // emitted through `send-ref`, wired to the worker's msg-sender once the handshake
  // lands; until then (a few ms, before any window is even visible) emit is inert.
  val send-ref = ref(Nothing)   // : ref<global,maybe<xsender<msg>>> (annotation can't name `msg`)
  val emit = fn(m)
    match !send-ref
      Just(s) -> xsender/xemit(s, m)
      Nothing -> ()
  // spawn the worker BEFORE mount: its libuv loop must be created before GLFW/Metal
  // init (mount), which on macOS sets up Cocoa/NSApplication -- loops created after
  // that do not fire their timers. Its OWN async loop runs update + subs and it
  // immediately hands its msg-sender back over the handshake channel.
  spawn-thread fn()
    with handle/try fn(err)
      println("koka/ui worker: uncaught exception: " ++ err.show)
    val msg-ch = xchannel()                   // worker-owned (from main + local subs/spawns)
    hand-send.xemit(msg-ch.sender)            // hand main the msg-sender
    val model-ref = ref(init)
    forking fn(fork)
      subs.foreach fn(s)
        fork( fn() s(msg-ch.chan) )            // subs emit msgs locally into the worker channel
      worker-loop(msg-ch, model-ref, update, model-send, fork)
  val state-ch : channel<() -> <uistate,ioc> ()> = channel()
  install-state-channel(state-ch)
  val async-ch : channel<async-want> = channel()   // future-boundary wants -> async-pump
  install-async-channel(async-ch)
  val frame-ch : channel<()> = channel()
  install-frame-channel(frame-ch)
  val mounted-ref      = ref(mount(composed(init), emit, config))
  val render-model-ref = ref(init)
  fun rerender() : <keytree,uistate,ioc,exn> ()   // ui-state change -> re-view the CURRENT render model
    flush-dirty()
    set-ref(mounted-ref, render(!mounted-ref, composed(!render-model-ref)))
    frame-done()
  // MAIN: await the worker's msg-sender, wire input, then run the main strands.
  val msg-send = hand-ch.xreceive
  set-ref(send-ref, Just(msg-send))
  forking fn(fork)
    fork( fn() pump(!mounted-ref) )            // input -> emit -> xemit to the worker
    fork( fn() drain-state(rerender) )         // ui-state re-renders (main only)
    fork( fn() async-pump(fork) )              // future-boundary runs (main only; idle until a boundary kicks)
    fork( fn() caret-blink() )                 // caret animation (main thread)
    fork( fn() anim-driver(frame-ch, 0.0, frame-interval-ms()) )    // demand-driven frame clock
    render-loop(model-ch, render-model-ref, mounted-ref, composed)
  ()

// WORKER loop: receive a msg, update the model, ship the new model to main, and
// fork any spawned tasks (their results re-enter as local msgs).
fun worker-loop<model,msg>( msg-ch : xchannel<msg>, model-ref : ref<global,model>,
                            update : (model, msg) -> dispatch<msg> model,
                            model-send : xsender<model>,
                            fork : (() -> <async,ioc,exn> ()) -> ioc () ) : <async,ioc,exn> ()
  val msg = msg-ch.xreceive
  val tasks = ref([])
  val model2 =
    with fun spawn(task)
      tasks := Cons(task, !tasks)
    update(!model-ref, msg)
  set-ref(model-ref, model2)
  model-send.xemit(model2)                     // cross-thread to main (marked thread-shared)
  (!tasks).foreach fn(t)
    fork( fn() msg-ch.chan.emit-io(t()) )       // spawned result -> local msg
  worker-loop(msg-ch, model-ref, update, model-send, fork)

// MAIN render loop: receive a new model from the worker and reconcile+paint it.
fun render-loop<model,msg>( model-ch : xchannel<model>, render-model-ref : ref<global,model>,
                            mounted-ref : ref<global,mounted<msg>>,
                            composed : (model) -> <keytree,uistate,ioc,exn> scene-out<msg> ) : <async,keytree,uistate,ioc,exn> ()
  val model = model-ch.xreceive
  set-ref(render-model-ref, model)
  invalidate-frame()   // model changed: full rebuild
  set-ref(mounted-ref, render(!mounted-ref, composed(model)))
  frame-done()
  render-loop(model-ch, render-model-ref, mounted-ref, composed)

fun loop<model,msg>( ch : channel<msg>,
                     model-ref : ref<global,model>, mounted-ref : ref<global,mounted<msg>>,
                     view : (model) -> <keytree,uistate,ioc,exn> scene-out<msg>,
                     update : (model, msg) -> dispatch<msg> model,
                     fork : (() -> <async,keytree,uistate,ioc,exn> ()) -> ioc () ) : <async,keytree,uistate,ioc,exn> ()
  val msg = ch.receive
  // collect spawned tasks; update itself stays continuation-free
  val tasks = ref([])
  val model2 =
    with fun spawn(task)
      tasks := Cons(task, !tasks)
    update(!model-ref, msg)
  set-ref(model-ref, model2)
  invalidate-frame()   // model changed: memo deps are untracked closures -> full rebuild
  set-ref(mounted-ref, render(!mounted-ref, view(model2)))
  frame-done()
  // each task becomes a strand of the app's one interleaving; its result
  // re-enters as a message
  (!tasks).foreach fn(t)
    fork( fn() ch.emit-io(t()) )
  loop(ch, model-ref, mounted-ref, view, update, fork)

fun ticks-ms() : ndet float64
  ticks().milli-seconds.float64

// The animation driver: BLOCK until some builder requests a frame (see ui/state
// request-frame), wait one frame (`ival` ms -- the backend reports the display's
// refresh interval, so a 120Hz panel animates at 120fps), tick. The tick's
// re-render either re-requests (another receive lands) or settles (the receive
// blocks; the driver is completely idle -- no polling, no writes). The tick
// advances the clock by the REAL time since the previous tick -- layout/paint
// time counts, so animations track wall time even when a frame costs more than
// the wait; capped so a stall skips ahead instead of replaying.
fun anim-driver( fch : channel<()>, last : float64, ival : int ) : <async,uistate,ioc> ()
  fch.receive
  val t0 = ticks-ms()
  wait(ival.milli-seconds)
  val now = ticks-ms()
  val since-last = now - last                    // full frame-to-frame gap (render + wait)
  val dt = (if last > 0.0 && since-last <= 100.0 then since-last else now - t0).min(100.0).max(1.0)
  take-frame-request()              // clear the flag so the re-render can re-arm it
  // slow-motion divides the DELTA, not the frame rate: frames still arrive
  // every `ival`, they just carry less time each (ui/state's `set-time-dilation`)
  anim-tick(dt / time-dilation())
  anim-driver(fch, now, ival)

// The caret-blink strand: while something is focused, toggle the caret phase
// every 530ms (each toggle is a ui/state transition, so drain-state re-renders);
// idle otherwise -- the poll writes nothing, so no re-renders happen unfocused.
fun caret-blink() : <async,uistate,ioc> ()
  if get-focused().is-just then
    wait(530.milli-seconds)
    if get-focused().is-just then toggle-caret()
  else
    wait(200.milli-seconds)
  caret-blink()

// A subscription is just a strand: emit `msg` every `secs` forever.
pub fun every<msg>( ch : channel<msg>, secs : duration, msg : msg ) : <async,ioc> ()
  wait(secs)
  ch.emit-io(msg)
  every(ch, secs, msg)
