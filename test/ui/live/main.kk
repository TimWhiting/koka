// The LIVE tier of test/ui/basic.kk and test/ui/windows.kk: the SAME
// scenarios, but the app runs the real pipeline (impeller via ./build.sh, or
// the web page via `koka -e build.kk -- jsweb`) and events are injected at
// the host fringe.
//
// Two apps, two runs of ONE binary: `basic` (model/msg) and `windows`
// (model/msg) are DIFFERENT message types, so they can't share one
// `live-scenarios` call (the tester is generic in `msg`, one call = one
// app) -- run `./test-live` for the basic suite (the default) and
// `./test-live windows` for the windows suite. Both are wired into this one
// `main` so `build.sh` only builds a single binary.
module main

import std/os/env
import std/async
import std/num/float64   // anim-time()'s `>` (Minor #1: frame-clock assert)
import ui/state
import basic
import windows
import ui/test
import ui/backend
import ui/test-live

// toggle the inspector open, exercise a widget INSIDE the real secondary
// window, close and reopen it, and assert retention -- all via injected
// host events routed to whichever window (main or secondary) each target
// name resolves to (see ui/test-live's module doc for the routing scheme).
// Window creation is a real, asynchronous OS call on this tier (unlike
// headless, where `window()` mounts synchronously), so an extra `settle()`
// after each toggle gives the backend's create -> reconcile -> present
// sequence a second round to land before the next assertion reads the tree.
pub fun windows-live-scenario( t : tester<windows/msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.click("toggle")
  t.settle()
  t.settle()   // window creation is async: allow a second round to land
  check-eq("window content reachable after toggle", t.texts("insp-body"), ["inspector body"])
  check-eq("keep starts fresh", t.texts("insp val"), ["K=0"])
  t.click("insp bump")
  t.settle()
  check-eq("keep bumped (clicked INSIDE the real window)", t.texts("insp val"), ["K=1"])
  // exercise the last-clicked-window keyboard routing path (ui/test-live's
  // last-vkey-ref): the app ignores Escape, so this only proves the key is
  // routed to the secondary window's ring without crashing or misrouting --
  // real text-into-window coverage needs a field in windows.kk (follow-up).
  t.press-key("Escape")
  t.settle()
  check-eq("keep unaffected by routed key", t.texts("insp val"), ["K=1"])
  t.click("close-insp")
  t.settle()
  check-eq("window content unreachable while closed", t.texts("insp val"), [])
  t.click("toggle")
  t.settle()
  t.settle()
  check-eq("keep retained across close/reopen (KeepAlive)", t.texts("insp val"), ["K=1"])
  check-eq("scratch reset across close/reopen (Transient)", t.texts("scratch val"), ["S=0"])

// NATIVE-ONLY retention: an image caches a GPU texture on first paint and frees
// it when unmounted. The basic app mounts `image("pic")` and a `toggle-pic`
// button that flips `show-pic`. Settle (pic mounted -> one cache entry), toggle
// off (unmounted -> pruned -> released -> zero), toggle on (re-mounted ->
// reloaded -> one). Works whether or not the PNG actually decodes: a FAILED
// decode is still a cache ENTRY (so we do not retry every frame), pruned the
// same way -- so this asserts the cache/retention lifecycle without shipping an
// asset (Task 6 commits the real sample image for the visual check).
pub fun image-retention-scenario( t : tester<basic/msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  check("image cached on first paint", image-cache-size() >= 1)
  val live-before = image-live-textures()
  check("texture uploaded on first paint", live-before >= 1)
  t.click("toggle-pic")
  t.settle()
  check-eq("texture released when image unmounts", image-cache-size(), 0)
  // pins that the GPU texture is actually RELEASED, not just the cache map
  // entry dropped -- a bug that skips `texture-release` in `prune-images`
  // would leak GPU memory and still pass the check above
  check-eq("GPU texture actually released (not just cache entry dropped)",
           image-live-textures(), live-before - 1)
  t.click("toggle-pic")
  t.settle()
  check("image reloaded on re-mount", image-cache-size() >= 1)
  check-eq("texture re-uploaded on re-mount", image-live-textures(), live-before)
  // src-change AT A STABLE KEY (review Important #1): emit `SwapPicSrc`
  // directly (no widget -- basic.kk deliberately doesn't wire a button for
  // this, see its comment) to flip `pic-src` between two valid PNGs without
  // touching `show-pic`/the `?key` -- the owner never unmounts, so this is
  // NOT the prune-sweep path above; it exercises `image-for`'s cache-HIT
  // src-mismatch branch instead. Before the fix, an owner-only cache HIT
  // returned the stored `ImgReady` unchecked -- the cached src (and its
  // stale texture) never changed -- so this assertion is the failing-first
  // pin for the fix (fails against the old owner-only lookup, passes once
  // `ImgReady` carries and compares `src`).
  check-eq("pic-src starts at x.png", image-cache-first-src(), Just("assets/x.png"))
  (t.emit)(basic/SwapPicSrc)
  t.settle()
  check-eq("cache re-decoded the NEW src (not stuck on the first texture)",
           image-cache-first-src(), Just("assets/y.png"))
  // the stable-key swap must NET ZERO on live textures: one release (old
  // src) balanced by one create (new src) -- a leak here would mean the old
  // texture was dropped from the cache map without `texture-release`, or the
  // reverse (double-created without releasing the old one)
  check-eq("src swap at a stable key does not leak a GPU texture",
           image-live-textures(), live-before)
  check-eq("cache stays at one entry across the swap (same owner, not a new one)",
           image-cache-size(), 1)
  // swap back so the scenario leaves the model as it found it
  (t.emit)(basic/SwapPicSrc)
  t.settle()
  check-eq("swap back restores x.png", image-cache-first-src(), Just("assets/x.png"))
  check-eq("swap-back nets zero too", image-live-textures(), live-before)

// NATIVE-ONLY async image loading (task #53): the basic app's `async-imgs` row
// (mounted on `ShowAsync`) exercises every source variant through the async
// `future-boundary` -- decode OFF the render thread, upload ON it. The valid
// FromPath carries a `min-load` so we can observe the PLACEHOLDER phase (leaf
// not yet addressable, no texture yet) before it flips to ready. FromBytes /
// FromPixels decode/upload a KNOWN small input. A bad path stays FAILED (no
// texture, no crash). Hiding the row again releases every async texture (the
// pin/prune lifecycle nets to zero -- no leak).
pub fun async-image-scenario( t : tester<basic/msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  val base = image-live-textures()   // the Sync "pic" texture (show-pic defaults on)
  val clock-at-kick = anim-time()    // Minor #1: baseline before the async row mounts and requests frames
  (t.emit)(basic/ShowAsync)
  t.settle()   // ~35ms: images kicked; the FromPath image holds min-load(150ms) before upload
  // PLACEHOLDER phase: the min-load FromPath image is NOT ready yet (no leaf,
  // no texture) -- it is still showing the boundary's placeholder
  check("async FromPath still on placeholder before min-load elapses", t.find("aimg-path").is-nothing)
  // TIGHTENED (Minor #2): after exactly one settle (~35ms) the min-load(150ms)
  // FromPath image is still on its placeholder (0 textures contributed) while
  // FromBytes and FromPixels -- carrying no `min-load` -- have already decoded
  // (a trivial 2x2 PNG / no decode at all) and uploaded: base+2, deterministically
  // (verified over repeated runs), not base+3. `< base+3` used to also pass if
  // the FromPath image had ALREADY uploaded early (2 of 3 done); pin the exact
  // count instead so a regression that uploads FromPath too early is caught.
  check-eq("no FromPath texture during the placeholder phase (exactly the two no-min-load images)",
           image-live-textures(), base + 2)
  // settle past the min-load so every valid image reaches ready
  t.settle(); t.settle(); t.settle(); t.settle(); t.settle(); t.settle(); t.settle()
  check("async FromPath ready after settles", t.find("aimg-path").is-just)
  check("async FromBytes ready (decoded a known PNG)", t.find("aimg-bytes").is-just)
  check("async FromPixels ready (uploaded raw RGBA)", t.find("aimg-pixels").is-just)
  check("bad async path stays failed (no ready leaf)", t.find("aimg-bad").is-nothing)
  // three valid async images each uploaded exactly one texture; the bad one none
  check-eq("three async textures uploaded (bad path uploaded none)",
           image-live-textures(), base + 3)
  // MINOR #1 FIX: the old assert here only counted cache entries (>= 4), which
  // says nothing about the render thread having stayed unblocked -- it would
  // pass even if the clock had stalled. `async-imgs` (basic.kk) calls
  // `request-frame()` every render while mounted, so `anim-time()` (the
  // demand-driven animation clock, ui/state) actually ADVANCES across the
  // decode/min-load window IF AND ONLY IF the render thread kept servicing
  // frame requests during the off-thread decode -- real proof of non-blocking.
  check("no hang: the animation clock advanced while the async image was loading",
        anim-time() > clock-at-kick)
  // SRC-CHANGE AT A STABLE KEY (review Important #1): the "aimg-path" async
  // image is currently READY at x.png -- flip its source to y.png WITHOUT
  // touching `?key`/`show-async` (SwapAsyncPicSrc, no widget -- mirrors
  // image-retention-scenario's SwapPicSrc for the Sync "pic"). Before the
  // fix the async `ready` leaf always drew the constant `async-image-src`
  // marker with no source-dependency in `future-boundary`'s phase, so this
  // was a silent no-op: the image stayed on x.png forever, `t.find` never
  // dropped to placeholder, and `image-live-textures()` never moved. After
  // the fix, the source-key mismatch restarts the boundary: the leaf goes
  // back to placeholder for one round (proving a REAL re-kick happened, not
  // just a same-texture repaint), then reaches ready again at the new
  // source -- one texture released (old) + one created (new), netting the
  // SAME count as before the swap (base + 3, no leak).
  check("async FromPath ready at x.png before the swap", t.find("aimg-path").is-just)
  val live-before-swap = image-live-textures()
  (t.emit)(basic/SwapAsyncPicSrc)
  t.settle()
  check("async FromPath back on placeholder right after a source swap (a real re-kick, not a no-op)",
        t.find("aimg-path").is-nothing)
  t.settle(); t.settle(); t.settle(); t.settle(); t.settle(); t.settle(); t.settle()
  check("async FromPath ready again after the swap (new source decoded)", t.find("aimg-path").is-just)
  check-eq("src swap at a stable async key does not leak a GPU texture (old released, new created)",
           image-live-textures(), live-before-swap)
  // swap back so the scenario leaves the model as it found it
  (t.emit)(basic/SwapAsyncPicSrc)
  t.settle(); t.settle(); t.settle(); t.settle(); t.settle(); t.settle(); t.settle(); t.settle()
  check("async FromPath ready again after swapping back to x.png", t.find("aimg-path").is-just)
  check-eq("swap-back nets zero too", image-live-textures(), live-before-swap)
  // hide the row: every async image unmounts -> its texture is released (pin
  // cleared once seen live, then pruned on unmount). Nets back to the baseline.
  (t.emit)(basic/ShowAsync)
  t.settle(); t.settle()
  check-eq("async textures all released on unmount (no leak)", image-live-textures(), base)

// FAILING-FIRST LEAK REGRESSION (Critical #1 -- pinned-but-never-mounted async
// texture leaks forever): mirrors the canonical case -- an async image
// scrolled past a lazy list while its decode/min-load window is still open.
// The row is unmounted (`ShowAsync` off) BEFORE the min-load(150ms) FromPath
// image's `run` ever reaches `put-image-texture`, so its `ready` leaf never
// mounts -- `put` still fires (on the main thread, after the boundary is
// already gone) and PINS a texture whose owner is never seen live again.
// Before the one-sweep-grace fix: the pin is permanent (`prune-images` skips
// any pinned owner forever) -> `image-live-textures()` stays elevated by
// exactly one texture past `base`, forever (verified: this assertion FAILS
// against the pre-fix `prune-images`, see the task report). After the fix:
// the pin ages to `PinAged` on the first sweep it is not seen live, then
// released on the NEXT sweep still not live -- reclaimed within two extra
// renders, well inside the settles below.
pub fun async-leak-scenario( t : tester<basic/msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  val base = image-live-textures()
  (t.emit)(basic/ShowAsync)
  t.settle()   // ~35ms: all four kicked; FromPath (min-load 150ms) still in flight
  check("scrolled-past image never mounted (still on placeholder)", t.find("aimg-path").is-nothing)
  // UNMOUNT the whole row NOW -- well before the 150ms min-load elapses, so
  // the FromPath image's `run` has not yet uploaded+pinned. This is the
  // "scrolled past during decode" boundary-unmounts-before-leaf-mounts case.
  (t.emit)(basic/ShowAsync)
  // `prune-images` only runs INSIDE a render, and once the row is unmounted
  // nothing left in the tree keeps asking for one (the stale RDone write that
  // eventually lands is silently dropped, no re-render) -- so, deterministically
  // (not relying on some OTHER animation, e.g. a still-blinking caret from an
  // earlier scenario, happening to land in this window), explicitly request a
  // frame before each settle. That forces one render -- and one `prune-images`
  // sweep -- per settle: enough to (a) let `run` finish its off-thread decode +
  // min-load wait + upload/pin (up to ~150ms after the ORIGINAL kick, so
  // ~115ms of settling from here) and (b) give the pin its two grace sweeps
  // (PinFresh -> PinAged -> released) once it lands.
  request-frame(); t.settle()
  request-frame(); t.settle()
  request-frame(); t.settle()
  request-frame(); t.settle()
  request-frame(); t.settle()
  request-frame(); t.settle()
  request-frame(); t.settle()
  request-frame(); t.settle()
  request-frame(); t.settle()
  request-frame(); t.settle()
  check-eq("never-mounted scrolled-past texture reclaimed back to baseline (no permanent GPU leak)",
           image-live-textures(), base)

// FAILING-FIRST REGRESSION (review Important #2 -- a late async run pins a
// texture but triggers no render, so pin-grace never advances in an IDLE
// app): the SAME "scrolled past during decode" shape as `async-leak-
// scenario` above, but deliberately WITHOUT that scenario's `request-frame()`
// crutch before every settle -- an idle app has nothing left asking for
// frames once the row unmounts (see the comment on that scenario), so this
// exercises exactly the path the review flagged: the late `run` finishes,
// calls `put-image-texture` (pins fresh), then its `settle-if-current` write
// is DROPPED (the boundary's phase entry is gone) with -- before the fix --
// NO render requested, so `prune-images` (the only thing that ages/releases
// a pin) never runs. Before the fix: this assertion FAILS (the pinned
// texture stays live past `base` forever, since nothing here ever asks for
// a render). After the fix: `settle-if-current`'s drop branch itself calls
// `request-render()`, so the completed-but-dropped decode ALWAYS schedules
// the render that ages/reclaims its pin -- no external frame needed.
pub fun async-idle-leak-scenario( t : tester<basic/msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  val base = image-live-textures()
  (t.emit)(basic/ShowAsync)
  t.settle()   // ~35ms: all four kicked; FromPath (min-load 150ms) still in flight
  check("scrolled-past image never mounted (still on placeholder)", t.find("aimg-path").is-nothing)
  // UNMOUNT the whole row NOW, well before the 150ms min-load elapses -- the
  // boundary-unmounts-before-leaf-mounts case -- and go IDLE: no
  // `request-frame()` anywhere from here on, only plain `settle()`s (each
  // is a real ~35ms wall-clock wait, see `t.sync`, so real time still passes
  // for the off-thread decode/min-load to finish and the late `run` to call
  // `put-image-texture` -- the only question is whether ANYTHING renders
  // afterward to sweep the pin it leaves behind).
  (t.emit)(basic/ShowAsync)
  t.settle()
  t.settle()
  t.settle()
  t.settle()
  t.settle()
  t.settle()
  t.settle()
  t.settle()
  t.settle()
  t.settle()
  check-eq("never-mounted texture reclaimed even in an otherwise-idle app (no external frame needed)",
           image-live-textures(), base)

// WEB-ONLY (task 4, web parity): the SAME `future-boundary`/phase model as
// native's `async-image-scenario`, but resolved by a real `<img>` onload
// probe instead of a GPU decode/upload -- images are browser-managed here, so
// there are no texture counts to assert, only the placeholder->ready phase
// transition. `FromBytes`/`FromPixels` are entirely self-contained (embedded
// bytes / raw pixels, no network fetch, no test asset server needed): right
// after the kick the boundary is synchronously `RPending` (`future-boundary`'s
// `kick` writes it before returning), and a DOM "load" event can only fire on
// a LATER turn of the browser's event loop -- so the FIRST check below
// reliably observes the placeholder before `t.settle()` ever gives the probe
// a turn to resolve. `aimg-bad`'s 404 exercises the failure path the same
// way. This also stands in for "the general `future-boundary` works on web":
// `web-async-image` (ui/async.kk) is future-boundary with no image-specific
// mechanism beyond the `waitload` probe -- a plain async `run` resolving is
// exactly this same kick -> Pending -> (real async work) -> Done path.
pub fun async-image-web-scenario( t : tester<basic/msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  t.settle()
  (t.emit)(basic/ShowAsync)
  check("async FromBytes still on placeholder right after the kick (onload is a later turn)",
        t.find("aimg-bytes").is-nothing)
  check("async FromPixels still on placeholder right after the kick (onload is a later turn)",
        t.find("aimg-pixels").is-nothing)
  // settle past the onload probe's real (if fast: a data-url / canvas source
  // needs no network) DOM round-trip
  t.settle(); t.settle(); t.settle(); t.settle(); t.settle()
  check("async FromBytes ready (data-url onload observed)", t.find("aimg-bytes").is-just)
  check("async FromPixels ready (canvas-dataURL onload observed)", t.find("aimg-pixels").is-just)
  check("bad async path stays failed on web too (no ready leaf)", t.find("aimg-bad").is-nothing)
  // hide the row again (mirrors native's unmount half of async-image-scenario)
  (t.emit)(basic/ShowAsync)
  t.settle()

pub fun main()
  // secondary OS windows only exist on the native backend (browsers have
  // none) -- `./test-live windows` on jsweb is a deliberate no-op rather than
  // a build failure, so the gate must still TYPE-CHECK for jsweb (it does:
  // `windows` imports nothing impeller-specific).
  if get-args().any(fn(a) a == "windows") then
    if test-backend == "impeller" then
      live-scenarios("windows (live)", windows/Model(), windows/view, windows/update,
                     [("windows", windows-live-scenario)])
    else
      println("ui/test-live: windows scenario skipped (native-only; backend=" ++ test-backend ++ ")")
  else
    // the retention assert is native-only (web images are browser-managed);
    // append it on the impeller tier, run the shared suite everywhere
    val scenarios = if test-backend == "impeller"
      then shared-scenarios ++ [("image-retention", image-retention-scenario),
                                ("async-image", async-image-scenario),
                                ("async-leak", async-leak-scenario),
                                ("async-idle-leak", async-idle-leak-scenario)]
      else shared-scenarios ++ [("async-image-web", async-image-web-scenario)]
    live-scenarios("basic interactions (live)", basic/Model(), basic/view, basic/update, scenarios)
