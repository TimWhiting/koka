/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Async boundaries: Suspense / FutureBuilder for Koka (task #53). A
// `future-boundary` runs an async `run` ONCE per identity+generation and shows
// a `placeholder` while it is pending, `ready(value)` on success, and
// `failed(err, retry)` on a thrown error -- a `retry` handle re-runs it.
//
// Mechanism (see docs/superpowers/specs/2026-07-27-async-boundary-images-design.md):
//   - The load PHASE lives in ui/state per identity (an `async-entry` = a
//     generation + a `raw-phase` of RPending/RDone/RFailed), read at build
//     time. The Done value is stored ERASED (ui/state's `erase`/`unerase`).
//   - On a KICK the build sets RPending at the kicking generation and emits a
//     `want` to the `async-pump` strand (forked by the app, mirroring
//     `drain-state`). The pump forks each run under `try`, honours `min-load`,
//     and writes RDone/RFailed back through the ui/state transition channel --
//     but only if the boundary's generation is STILL the one it ran under
//     (stale-discard: a retry / new deps bumped it meanwhile -> drop the
//     result). That single generation mechanism IS retry + deps + the
//     cancellation floor.
//
// The `async-snapshot` type below is the SHARED contract with the (deferred)
// low-level `async-boundary` and `stream-boundary`; `future-boundary` produces
// exactly Pending -> Done|Failed (no streaming `Active`).
module ui/async

import std/core/unsafe
import std/async
import std/async/thread   // compute: decode an image off the render thread
import std/num/float64
import std/num/int32      // id.int32 for the Image leaf owner
import std/time/duration
import std/time/timer   // ticks(): the monotonic clock for min-load
import ui/widget
import ui/image          // image-source / image-load / async-image-src marker (re-exported by ui/widget too)
import ui/state          // the async-phase store + erase/unerase (re-exports ui/reactive)

// The shared async-load contract. `Active(latest)` is reserved for the
// (deferred) streaming boundary and deliberately NOT added here: a future
// produces exactly Pending -> Done|Failed.
pub type async-snapshot<a>
  Pending
  Done( value : a )
  Failed( err : exception )

// A "want" the build emits to the async-pump on a kick: the boundary identity,
// the generation it was kicked under, the (erased-result) run to execute, and
// the minimum time the placeholder should stay up. `run` MAY throw -- the pump
// wraps it and turns a throw into RFailed.
pub struct async-want
  id       : int
  gen      : int
  run      : () -> <async,ioc,exn> any
  min-load : duration

// ----------------------------------------------------------------
// the async-pump channel: a ref holding the channel the runtime installs, the
// twin of ui/state's state-channel. The build's kick emits wants here; the
// forked `async-pump` strand receives and runs them.

val async-ch : ref<global, maybe<channel<async-want>>> = unsafe-total{ ref(Nothing) }

// the runtime installs its want-channel here on startup (ui/app run-single /
// run-threaded, and the ui/test harness)
pub fun install-async-channel( ch : channel<async-want> ) : ioc ()
  val r = async-ch
  r := Just(ch)

// emit a want to the pump; if no runtime is installed (a standalone build with
// no pump) it is dropped -- the boundary simply stays on its placeholder
fun emit-want( w : async-want ) : ioc ()
  match !async-ch
    Just(ch) -> ch.emit-io(w)
    Nothing  -> ()

fun ticks-ms() : ndet float64
  ticks().milli-seconds.float64

// ----------------------------------------------------------------
// the future boundary widget

// Run `run` asynchronously and render its lifecycle. `run` executes ONCE per
// identity+generation (not per rebuild): a KICK sets RPending + emits a want,
// and every subsequent rebuild that reads RPending just shows the placeholder
// WITHOUT re-emitting -- "emit exactly once per generation". `min-load` holds
// the placeholder for at least that long (anti-flicker). The default `failed`
// ships a message + a Retry button.
//
// KICK / RETRY ORDERING (the subtle part; see the report):
//   Store writes normally go through ui/state's DEFERRED transition channel
//   (applied later by drain-state). If the kick's RPending were deferred, a
//   rebuild that happens BEFORE it lands (a message/frame render that does not
//   drain the state channel first) would read Nothing again and kick a SECOND
//   time at the same generation -> a duplicate run. So the kick writes RPending
//   SYNCHRONOUSLY to the store (`set-async`, exactly like `use-state`'s
//   first-use seed) -- the store reflects RPending the instant the kick
//   returns, so no rebuild can re-kick the generation. The want is emitted once
//   alongside it. `retry` likewise bumps the generation SYNCHRONOUSLY (so a
//   very fast run's stale-check reads the NEW generation and is not wrongly
//   discarded) and then requests a render -- we are off the render path (a
//   click), so we must ask for the rebuild that swaps Failed -> placeholder.
pub fun future-boundary<a,msg>( run : () -> <async,ioc,exn> a,
                                ready : (a) -> <keytree,uistate,ioc> widget<msg>,
                                placeholder : widget<msg> = default-placeholder(),
                                failed : (exception, () -> <uistate,ioc> ()) -> <keytree,uistate,ioc> widget<msg> = default-error,
                                min-load : duration = zero,
                                ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
  val bkey = kt-child(?key, Slot("ab", ?kk-file-line))
  val id = bkey.key-id
  // the pump stores/handles `any`; the build unerases on read (ui/state)
  fun run-erased() : <async,ioc,exn> any
    erase(run())
  // KICK: reflect RPending SYNCHRONOUSLY in the store + emit ONE want (see note)
  fun kick( g : int ) : <uistate,ioc> ()
    set-async(id, Async-entry(g, RPending))
    emit-want(Async-want(id, g, run-erased, min-load))
  // RETRY: bump the generation SYNCHRONOUSLY, emit the fresh want, and request
  // a render (we are off the render path). NOT just `retry-async`: the store
  // must reflect the new generation before the run's stale-check, AND a new
  // want must actually be emitted (a bump alone re-renders but starts nothing).
  fun retry-fn() : <uistate,ioc> ()
    val ng = current-async-gen(id) + 1
    set-async(id, Async-entry(ng, RPending))
    emit-want(Async-want(id, ng, run-erased, min-load))
    request-render()
  match async-phase(id)
    Nothing ->
      kick(1)               // first mount: kick generation 1
      placeholder
    Just(Async-entry(_, RPending))    -> placeholder    // already kicked this generation
    Just(Async-entry(_, RDone(v)))    -> ready(unerase(v))
    Just(Async-entry(_, RFailed(e)))  -> failed(e, retry-fn)

// a neutral padded fill shown while a boundary is pending, when the caller
// supplies no placeholder of its own (root-key: unaddressable, a plain filler)
pub fun default-placeholder<msg>() : widget<msg>
  box(column([], ?key = root-key), padding = 8.0, ?key = root-key)

// the default failure UI: a message plus a Retry button (retry is failure's
// common partner). `act` runs the ioc `retry` thunk with no message. root-key:
// good for a single boundary; a real app supplies its own scoped `failed` when
// it needs several addressable retries.
pub fun default-error<msg>( err : exception, retry : () -> <uistate,ioc> () ) : <keytree,uistate,ioc> widget<msg>
  column([ text("failed: " ++ err.show, ?key = root-key),
           act(box(text("Retry", ?key = root-key), padding = 6.0, ?key = root-key), retry, ?key = root-key) ],
         ?key = root-key)

// ----------------------------------------------------------------
// the async-pump strand: forked by the app alongside drain-state. Receive a
// want, fork a strand to run it, recurse. Each run strand: try-wrap (a throw ->
// RFailed), time the run, hold min-load, then write RDone -- both writes gated
// on the generation still being current (stale-discard).

// `fork`'s strand effect carries an OPEN tail `|e` so it unifies with
// `forking`'s polymorphic `fork` at any call site (the app runtime, whose body
// row is <keytree,uistate,ioc,exn>; the ui/test harness, whose body ALSO
// carries `uicheck`) -- a closed row would pin the enclosing `forking` body's
// effect and reject one of them.
pub fun async-pump( fork : (() -> <async,uistate,ioc,exn|e> ()) -> ioc () ) : <async,uistate,ioc,exn> ()
  match !async-ch
    Just(ch) ->
      val w = ch.receive
      fork fn()
        with handle/try fn(e) settle-if-current(w.id, w.gen, RFailed(e))
        val t0 = ticks-ms()
        val r  = (w.run)()
        val elapsed = ticks-ms() - t0
        val floor   = w.min-load.milli-seconds.float64
        if elapsed < floor then wait((floor - elapsed).int.milli-seconds)   // hold the placeholder
        settle-if-current(w.id, w.gen, RDone(r))
      async-pump(fork)
    Nothing -> ()

// write the completion through ui/state's transition channel (deferred -> it
// re-renders) ONLY if `gen` is still this boundary's current generation; a
// stale result (retry / new deps bumped the generation meanwhile) is dropped.
//
// IMPORTANT 2 (final-review): a DROPPED write still may have done real work
// off to the side before landing here -- an image's `run` already called
// `put-image-texture`, which PINS a fresh texture, unconditionally, before
// this stale-check ever runs (see backend.kk's PIN note). If the boundary
// has unmounted (or a retry/new deps bumped the generation), that pin is
// never seen live and only `prune-images`' one-sweep grace can reclaim it --
// but `prune-images` runs INSIDE a render, and a dropped write triggers NONE
// (the old code just fell through to `()`). In an otherwise-idle app that
// pin then never ages: it sits pinned until some UNRELATED render happens to
// come along. Requesting a render here, unconditionally, on every drop makes
// the "a completed decode always eventually gets swept" invariant hold with
// no dependency on outside traffic; a render triggered when nothing changed
// is a no-op paint (coalesced with any render already pending), so this is
// free on the normal (not-dropped) path and only costs one idle render on
// the drop path.
fun settle-if-current( id : int, gen : int, phase : raw-phase ) : <uistate,ioc> ()
  match async-phase(id)
    Just(Async-entry(cur, _)) | cur == gen -> set-async-phase(id, gen, phase)
    _ -> request-render()

// ----------------------------------------------------------------
// images: the async boundary's first customer (task #53). `image` is
// backend-agnostic and lives HERE (not in a backend module) so headless tests
// and both hosts share ONE front door without dragging a GPU C shim into the
// headless build. The native GPU decode/upload/put primitives are installed at
// mount via `install-image-ops` (a monomorphic bundle, the twin of the
// async-want channel install); the web onload-probe primitive installs via
// `install-web-image-ops` the same way (task 4, web parity). When NEITHER is
// installed -- headless (no paint, no DOM) -- `image` falls back to a plain
// `Image` leaf.

// the native decode/upload primitives, installed by the impeller backend. All
// `ioc` (they call C externs); the decode ones run inside `compute` (OFF the
// render thread), the uploads + put run ON it (compute resumes there). Field
// names are deliberately short so the impeller backend's own `decode-path` /
// `upload-pixels` externs don't collide with these generated accessors.
pub struct image-ops
  dpath  : ( string ) -> ioc maybe<(int, int, int)>          // encoded file -> (bufptr,w,h)
  dbytes : ( vector<int8> ) -> ioc maybe<(int, int, int)>    // encoded bytes -> (bufptr,w,h)
  upix   : ( int, int, int ) -> ioc int                      // (bufptr,w,h) -> texture handle
  urgba  : ( vector<int8>, int, int ) -> ioc int             // raw RGBA -> texture handle
  puttex : ( int, int, int, int ) -> ioc ()                  // (id,tex,w,h): cache under owner id

val image-ops-ref : ref<global, maybe<image-ops>> = unsafe-total{ ref(Nothing) }

// the backend installs its GPU primitives here at mount (native only)
pub fun install-image-ops( ops : image-ops ) : ioc ()
  val r = image-ops-ref
  r := Just(ops)

// the web onload primitive (task 4, web parity; simplified in task #58).
// `probe` resolves an `image-source` to its final `<img src>` (base64 /
// canvas dataURL for Bytes/Pixels) and AWAITS the browser's own decode of it,
// returning that src or throwing on error -- an ordinary `run` for
// `future-boundary`, so web and native share ONE async path.
//
// It did not always look like this. The awaiting shape was tried first, and
// was believed to deadlock on `--target=jsweb`: a DOM listener resumes a
// suspended channel-receive from outside any strand's driver loop, which was
// blamed for one-shot continuations several `fork` levels deep never getting
// their turn again -- "observed as later-forked sibling wants simply never
// starting". That last part was the giveaway. The wants were not failing to
// resume, they were failing to START, because `async-pump`'s forked closure
// held a by-reference capture of a tail-call loop's `var` (task #55, a JS
// backend bug). With that fixed the awaiting design works, verified with
// three boundaries kicked in one build; so the hand-rolled phase machinery
// this file used to carry for web -- its own kick/pending/done/retry, an
// `EvImageLoaded` event threaded through the backend's input pump, and a
// `web-image-settle` that had to hold the anti-flicker floor as a deadline
// to avoid serializing that pump (task #56) -- is all gone. The floor is
// `future-boundary`'s again, and `async-pump` forks a strand per want, so
// concurrent settles come for free instead of needing to be arranged.
pub struct web-image-ops
  probe : ( source : image-source ) -> <async,ioc,exn> string

val web-image-ops-ref : ref<global, maybe<web-image-ops>> = unsafe-total{ ref(Nothing) }

// the web backend installs its onload-probe primitive here at mount
pub fun install-web-image-ops( ops : web-image-ops ) : ioc ()
  val r = web-image-ops-ref
  r := Just(ops)

// the image front door. `Sync FromPath` (and headless, which has neither
// image-ops installed) lowers to a plain `Image` leaf -- native decodes+
// uploads inline on first paint, headless just lays out the box. `Async`
// loads through a `future-boundary`: native ops decode off the render thread,
// upload on it, cache the texture under the image's owner id, then draw it;
// web ops (no native ops installed) probe the browser's own decode via an
// offscreen `<img>`'s `onload` and then draw a real `<img src>`. The OWNER id
// is `?key.key-id` directly (not a Slot child) so a tail-anchored selector
// (`find("pic")`) still addresses the leaf by its `?key` scope, exactly like
// the pre-task `image`.
pub fun image<msg>( source : image-source, fit : image-fit = Contain, load : image-load = Async,
                    placeholder : widget<msg> = default-placeholder(), min-load : duration = zero,
                    width : float64 = 0.0, height : float64 = 0.0,
                    ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
  val id = ?key.key-id
  val sync = match load { Sync -> True; Async -> False }
  match source
    FromPath(p) | sync -> Image(id.int32, p, fit, width, height)
    _ -> match !image-ops-ref
      Just(ops) -> async-image(id, ops, source, fit, placeholder, min-load, width, height, ?key = ?key)
      Nothing   -> match !web-image-ops-ref
        Just(wops) -> web-async-image(id, wops, source, fit, placeholder, min-load, width, height, ?key = ?key)
        Nothing    -> image-leaf(id, source, fit, width, height)   // headless: no DOM, no GPU

// convenience for the common asset-path case -- keeps today's `image(src, ...)`
// ergonomics: `image-path("logo.png", fit = Cover, ...)`.
pub fun image-path<msg>( src : string, fit : image-fit = Contain, load : image-load = Async,
                         placeholder : widget<msg> = default-placeholder(), min-load : duration = zero,
                         width : float64 = 0.0, height : float64 = 0.0,
                         ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
  image(FromPath(src), fit, load, placeholder, min-load, width, height, ?key = ?key)

// the no-ops fallback leaf (headless only, no DOM/GPU installed): `FromPath`
// uses its path/URL as-is; `FromBytes`/`FromPixels` have nothing to lower to
// without a host, so they render an empty (unaddressed-by-src) `<img>`-shaped
// box -- headless tests never paint it, only lay it out.
fun image-leaf<msg>( id : int, source : image-source, fit : image-fit, w : float64, h : float64 ) : widget<msg>
  val src = match source
    FromPath(p)       -> p
    FromBytes(_)      -> ""
    FromPixels(_,_,_) -> ""
  Image(id.int32, src, fit, w, h)

// the web async image (task 4, web parity; task #58): the SAME
// `future-boundary` native uses, with a `run` that awaits the browser's own
// decode instead of decoding+uploading itself. `ready` draws a real `<img>`
// at the resolved src -- the browser already loaded this EXACT src via the
// (never-mounted) probe element, so it paints from cache immediately (no
// second fetch, no double-decode). Everything else -- placeholder, the
// min-load floor, failure with Retry, retry-by-generation-bump,
// stale-discard -- is `future-boundary`'s, not re-implemented here.
fun web-async-image<msg>( id : int, wops : web-image-ops, source : image-source, fit : image-fit,
                          placeholder : widget<msg>, min-load : duration, w : float64, h : float64,
                          ?key : key ) : <keytree,uistate,ioc> widget<msg>
  future-boundary( fn() (wops.probe)(source),
                   fn(src) Image(id.int32, src, fit, w, h),
                   placeholder = placeholder, min-load = min-load, ?key = ?key )

// a cheap, comparable summary of an `image-source`'s CONTENT (IMPORTANT 1,
// final-review): compared build-over-build to detect a source change at a
// stable `?key` so the async boundary below knows to restart. `FromPath`'s
// own path IS its identity (a different asset -> a different path, always).
// `FromBytes`/`FromPixels` have no natural short identity, so this is a
// coarse fingerprint (length, or dimensions+length) -- cheap enough to
// compute on every build, and good enough to catch the common "swap to a
// different buffer/pixel source" case; it will NOT catch two different
// buffers that happen to share a length (a real content hash is deferred,
// same as `restart-on`/deps generally -- see the design doc).
fun source-key( source : image-source ) : string
  match source
    FromPath(p)           -> "p:" ++ p
    FromBytes(b)          -> "b:" ++ b.length.show
    FromPixels(rgba,w,h)  -> "x:" ++ w.show ++ "," ++ h.show ++ "," ++ rgba.length.show

// bump the generation and emit a fresh want for an already-mounted image
// boundary -- exactly `future-boundary`'s own `retry-fn` shape (synchronous
// store write + one want emit), just triggered by a source-key mismatch
// detected AT BUILD TIME (see `async-image` below) instead of a click, so
// (unlike `retry-fn`) it needs no `request-render()`: we are already mid-
// build, and `future-boundary`'s own subsequent phase-match sees the fresh
// RPending and renders the placeholder in THIS same build.
fun restart-image-boundary( bid : int, g : int, run : () -> <async,ioc,exn> (), min-load : duration ) : <uistate,ioc> ()
  val ng = g + 1
  set-async(bid, Async-entry(ng, RPending))
  emit-want(Async-want(bid, ng, fn() erase(run()), min-load))

// the native async image: a `future-boundary` whose `run` decodes off-thread
// then uploads on the render thread and caches under `id`; `ready` emits the
// leaf drawing that cached texture (marked with `async-image-src` so the
// backend's paint HITS the cache without re-decoding). `run`'s result is unit.
fun async-image<msg>( id : int, ops : image-ops, source : image-source, fit : image-fit,
                      placeholder : widget<msg>, min-load : duration, w : float64, h : float64,
                      ?key : key ) : <keytree,uistate,ioc> widget<msg>
  // min-load is held INSIDE the run, AFTER decode but BEFORE upload -- not
  // passed to `future-boundary` (which would hold AFTER the run returns, i.e.
  // after the texture is already created, leaving it un-mounted-but-alive for
  // the whole min-load window). Holding before the upload means NO texture
  // exists during the placeholder phase (live-textures stays flat until ready),
  // and the upload -> put -> `future-boundary` RDone settle then happens with no
  // await between them -- the texture is created and its ready leaf scheduled in
  // one synchronous step (the PIN in the backend covers the residual gap).
  fun run() : <async,ioc,exn> ()
    val t0 = ticks-ms()
    match source
      FromPixels(rgba, pw, ph) ->
        hold-since(t0, min-load)
        val tex = (ops.urgba)(rgba, pw, ph)      // no decode; already RGBA
        if tex == 0 then throw("ui/image: upload failed (FromPixels)")
        (ops.puttex)(id, tex, pw, ph)
      _ ->
        val (buf, dw, dh) = decode-off-thread(ops, source)   // FromPath / FromBytes, off-thread
        hold-since(t0, min-load)
        val tex = (ops.upix)(buf, dw, dh)
        if tex == 0 then throw("ui/image: upload failed")
        (ops.puttex)(id, tex, dw, dh)
  // IMPORTANT 1 (final-review): a stable `?key` with a CHANGED `source` must
  // re-decode -- `future-boundary` alone has no source-dependency (its
  // phase is keyed on identity+generation only, so the `ready` leaf below
  // always draws the constant `async-image-src` marker and `image-for`
  // always cache-hits on it). Plumb a minimal, targeted `restart-on =
  // source` ourselves: remember the source-KEY this boundary last kicked
  // with in a `use-state-quiet` cell -- QUIET because this comparison runs
  // on EVERY build, and a normal transition-based setter would schedule a
  // redundant re-render each time the key does NOT change (the common
  // case). `ab-fl` pins the id we compute here to be IDENTICAL to the one
  // `future-boundary` computes internally for its own `Slot("ab", ...)`
  // phase entry (the same `?kk-file-line`-threading trick `lazy-column`
  // uses to keep two call sites' ids in lockstep) -- so reading/writing
  // `async-phase(bid)`/`set-async(bid, ...)` here talks to the SAME slot
  // `future-boundary` reads right below.
  val ab-fl = "ui/async:image-boundary"
  val bid = kt-child(?key, Slot("ab", ab-fl)).key-id
  val (last-src-key, set-last-src-key) = use-state-quiet(source.source-key, "async-src-key", ?key = ?key)
  val cur-src-key = source.source-key
  if cur-src-key != last-src-key then
    match async-phase(bid)
      // only restart once the PRIOR run has settled (Done or Failed) --
      // never interrupt an in-flight decode (Pending): the next build after
      // it settles re-compares (last-src-key is left stale below) and
      // restarts then, exactly once. `Nothing` (never kicked yet) needs no
      // restart -- the kick just below picks up the current source already.
      Just(Async-entry(g, RDone(_))) ->
        restart-image-boundary(bid, g, run, min-load)
        set-last-src-key(fn(_) cur-src-key)
      Just(Async-entry(g, RFailed(_))) ->
        restart-image-boundary(bid, g, run, min-load)
        set-last-src-key(fn(_) cur-src-key)
      _ -> ()
  future-boundary(run, fn(_) Image(id.int32, async-image-src, fit, w, h),
                  placeholder = placeholder, ?key = ?key, ?kk-file-line = ab-fl)

// hold the placeholder until at least `d` has elapsed since `t0` (anti-flicker,
// applied before an image upload so no texture exists during the wait)
fun hold-since( t0 : float64, d : duration ) : <async,ioc> ()
  val elapsed = ticks-ms() - t0
  val floor   = d.milli-seconds.float64
  if elapsed < floor then wait((floor - elapsed).int.milli-seconds)

// decode a source to `(bufptr,w,h)` OFF the render thread via `compute` (native
// threadpool -- the whole point: the frame clock keeps ticking during a decode),
// THROWING on a decode failure so the boundary shows its `failed` UI. `compute`'s
// `work` is `pure`; the ops closures are `ioc` (plain C stbi calls, no koka
// handlers), so `unsafe-total` discharges that leftover effect on the worker --
// the `throw` stays outside it.
fun decode-off-thread( ops : image-ops, source : image-source ) : <async,exn> (int, int, int)
  val r = compute fn()
    unsafe-total
      match source
        FromPath(p)         -> (ops.dpath)(p)
        FromBytes(b)        -> (ops.dbytes)(b)
        FromPixels(_,pw,ph) -> Just((0, pw, ph))   // unreachable: FromPixels never decodes
  match r
    Just(t) -> t
    Nothing -> throw("ui/image: decode failed")
