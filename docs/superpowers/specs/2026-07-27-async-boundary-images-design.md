# Async boundaries + async/sync image loading (task #53)

Status: approved design (Tim, 2026-07-27). Generalizes "async image loading"
into a first-class **async boundary** primitive (Suspense / FutureBuilder for
Koka); **images are its first customer**. 100% vision documented; ~80% built
now against a fixed contract so the deferred parts drop in without reshaping.

## Motivation

Native image decode+upload currently runs SYNCHRONOUSLY inside `paint-at`
(render thread), hitching one frame on first display (task #53). The fix is
async loading with a placeholder — which is the same shape as any widget
awaiting async work (a backend fetch, a computation). So rather than a
one-off image loader, build the general boundary and make `image` an instance.

## The unified model (the 100% core — DEFINED now, partially built)

**One snapshot type** (Flutter's `AsyncSnapshot`, deduplicated):
```koka
pub type async-snapshot<a>
  Pending                        // no value yet
  Active( latest : a )           // streaming: a value arrived, more may come
  Done( value : a )              // completed (one-shot final, or a stream's last)
  Failed( err : exception )
```
**One driver shape** unifying future and stream — a `run` that YIELDS:
```koka
run : (yield : a -> ioc ()) -> <async,ioc|e> ()
```
- Future = yields once then returns → `Done(v)`.
- Stream = yields many then returns → `Active(c1)`, `Active(c2)`, … `Done(last)`.
- Heterogeneous progress (a download bar THEN the image) = the user yields a
  union THEY define (`Progress(pct) | Data(x)`); the framework stays
  type-uniform. This is the escape valve keeping the core simple.
- Throw → `Failed(err)`.

### Design rationale: shared CONTRACT, specialized MECHANISM

"A future is a one-shot stream" conceptually does NOT mean future must be
IMPLEMENTED via the stream code path. The mechanisms genuinely differ:

| | one-shot future | stream |
|---|---|---|
| lifetime | fork → await 1 value → store → EXIT | fork → drain N yields → live until complete |
| delivery | none (the return value IS the result) | a channel per boundary (yields cross to render thread) |
| re-renders | one (on Done) | one per yield → needs COALESCING/backpressure |
| states | Pending → Done \| Failed | Pending → Active* → Done \| Failed |

Forcing future through the stream path makes it carry a delivery channel +
coalescing it never uses, and flash a spurious `Active(v)` before `Done(v)`.
So: **share the CONTRACT** (the `async-snapshot` type, the builder shape, the
phase-in-`ui/state` pattern, the async-pump host strand, the generation /
cancellation semantics) — that keeps future and stream "not drastically
different" and interchangeable to a reader — but give each its OWN optimal
mechanism (future: fork-await-store-exit; stream: drain-coalesce). We build
the future mechanism now against the fixed contract; `stream-boundary` slots
in later as a parallel mechanism, not a retrofit.

## API layers

```koka
// LOW-LEVEL (100%, stream-capable): one builder over the snapshot + a retry handle.
pub fun async-boundary<a,msg>( run : (yield : a -> ioc ()) -> <async,ioc|e> (),
                               view : (async-snapshot<a>, retry : () -> ioc ()) -> <keytree,uistate,ioc> widget<msg>,
                               ?key : key ) : <keytree,uistate,ioc> widget<msg>

// ERGONOMIC FUTURE (the 80% path; its own lean mechanism, no yield/Active/channel):
pub fun future-boundary<a,msg>( run : () -> <async,ioc|e> a,
                                ready : (a) -> <keytree,uistate,ioc> widget<msg>,
                                placeholder : widget<msg> = default-placeholder,
                                failed : (exception, retry : () -> ioc ()) -> <keytree,uistate,ioc> widget<msg> = default-error,
                                min-load : duration = zero,
                                ?key : key ) : <keytree,uistate,ioc> widget<msg>

// ERGONOMIC STREAM (designed, DEFERRED): adds an `active(partial)` builder.
// stream-boundary( run, active, ready, placeholder, failed, ?key )
```
`future-boundary`'s `run` stays clean (no `yield`); internally it needs no
delivery channel and produces exactly Pending → Done|Failed. The default
`failed` builder ships a message + a **Retry button** (retry is the common
partner to failure). `ready` MAY take a `refresh` handle (same as retry) for
pull-to-refresh — offered, low-level always provides it.

## Phase in ui/state; result stored erased

- Per-key phase lives in `ui/state` (build-readable, exactly like
  `use-state`/`scroll-state`): the snapshot + a **generation** (below). The
  Done/Active `value : a` is stored ERASED (the same phantom-key existential
  coercion `use-state`'s cell store already uses — a guarded `cell/as`).
- **build** reads phase(key): kick when the phase's generation ≠ the key's
  current generation (covers first run); Pending → `placeholder`; Done(r) →
  `ready(r)`; Failed(e) → `failed(e, retry)`. A boundary runs ONCE per
  identity+generation (not per rebuild).

## Retry / deps / cancellation-floor — one mechanism: GENERATION

- Each boundary key carries a **generation** (epoch). A completing `run`
  writes its result TAGGED with the generation it ran under; if a retry (or a
  future dep change) bumped the key's generation meanwhile, the stale result
  is DISCARDED. This is simultaneously: retry, `restart-on`/deps, and the
  cancellation FLOOR (stale results dropped). True `forking`-cancellation
  (actually stop the stale strand) is an optimization ON this, deferred.
- **`retry()` = bump the key's generation** → the build's "generation changed
  → re-kick with the current `run`" path re-runs (placeholder shows again).
- **Unmount mid-flight**: retention drops the phase; the late write to a dead
  key is a no-op (result discarded), same as the generation-stale case.

## Threading / mechanism (native)

- An **async-pump strand**, forked by `app` alongside `pump`/`drain-state`
  (backend-agnostic; it lives in the app runtime, not a backend). It receives
  "wants" `(key, run, generation, min-load)` over a channel (emitted by the
  build on a kick), and for each: `forking` runs the `run` under try; on
  success waits `max(0, min-load - elapsed)`; writes `Done`/`Failed(gen)` via
  the state channel → `request-render`. `compute` offloads CPU/IO work inside
  a `run` (native threadpool; degrades to a cooperative strand on web/wasi).
- future path: fork-await-store-exit (no per-boundary channel). stream path
  (later): a delivery channel + coalescing on the same async-pump host.

## Images as the first customer

`image` becomes a `future-boundary` specialized for GPU textures — it SHARES
placeholder/min-load/failed(+retry)/phase, and adds:
```koka
pub type image-source
  FromPath( path : string )                            // asset path (native decode) / URL (web)
  FromBytes( bytes : vector<int8> )                    // in-memory encoded PNG/JPEG (e.g. a fetch)
  FromPixels( rgba : vector<int8>, w : int, h : int )  // already-decoded RGBA
pub type image-load
  Async   // default: placeholder → decode off-thread → upload on render thread
  Sync    // decode+upload inline on first paint (one-frame hitch, no placeholder/min-load)
pub fun image<msg>( source : image-source, fit : image-fit = Contain, load : image-load = Async,
                    placeholder : widget<msg> = default-placeholder, min-load : duration = zero,
                    width = 0.0, height = 0.0,
                    failed : (exception, retry : () -> ioc ()) -> widget<msg> = default-error,
                    ?key : key ) : <keytree,uistate,ioc> widget<msg>
// convenience: image-path(src, ...) = image(FromPath(src), ...) keeps today's ergonomics
```
Image's specialized resolution (the GPU-upload constraint the generic
boundary lacks):
- **run** (`load=Async`): decode/acquire pixels off-thread via `compute`
  (`FromPath`→read+decode; `FromBytes`→`stbi_load_from_memory`;
  `FromPixels`→identity, no decode). The pixels are the async result.
- **finalize** (render thread): the async-pump's image variant uploads the
  pixels to an `ImpellerTexture` on the render thread (upload is render-thread
  ONLY), stores the texture in the backend cache keyed by owner, and sets the
  ui/state phase Ready → re-render. The `ready` build then emits the image
  leaf drawing the cached texture.
- **`load=Sync`**: decode+upload inline in `paint-at` (today's path, kept) —
  appears frame 1, ignores placeholder/min-load.
- `FromBytes` decodes async like a path (the native-has-no-URL-fetch
  workaround: fetch the PNG yourself, hand bytes in). `FromPixels` uploads
  only (no decode); cached per owner — **80/20 limitation, documented**:
  changing pixels at a stable `?key` requires a key change (buffers aren't
  cheaply diffable beyond a length check), OR use `retry()` to force a
  reload. **UPDATE (final-review, Important 1 fixed):** this caveat
  originally read as applying to every async source; it now applies to
  `FromPixels` ONLY. `async-image` compares a per-source `source-key`
  build-over-build (`FromPath`'s path string; `FromBytes`'s byte length;
  `FromPixels`'s `(w,h,length)`) and restarts the boundary itself when it
  changes at a settled (`RDone`/`RFailed`) phase — so `FromPath`/
  `FromBytes` re-decode automatically on a source change at a stable
  `?key`, no key change or explicit `retry()` needed. A narrower
  same-length blind spot survives for BOTH `FromPixels` AND `FromBytes`,
  which fingerprint by buffer length rather than a content hash: two
  different buffers of the same length are indistinguishable, so a swap
  between them at a stable `?key` still needs a key change or `retry()`.
  `FromPath` (fingerprinted by its path string) has no such gap.
- Texture cache + `prune-images` retention release + `g_live_tex` leak guard:
  unchanged. Also folds in the review residual — `ImgFailed` carries `src` and
  re-decodes on a src swap.

## Cross-backend (web)

- General boundary: a `run` is JS-async on the browser loop (`compute`
  degrades to a cooperative strand); the async-pump + phase model is identical.
- **image**: lowers to `<img>` (`FromPath`), `<img src="data:…;base64,…">`
  (`FromBytes`), or `<canvas>` + `putImageData` (`FromPixels`). To honor the
  placeholder + min-load on web, the element gets an **`onload` listener** that
  posts an event → sets phase Ready (+ a `min-load` timer strand); until then
  the placeholder widget shows. One phase model, both backends. `load` is
  ignored on web (the browser is always async).

## 80/20 scope

**Ships now:** the `async-snapshot` type + `run`-yields shape (full API
surface), `async-boundary` (low-level) + `future-boundary` (lean future
mechanism), the generation model (retry + stale-discard), `retry` handle +
default retry-error UI, placeholder + min-load, `image` on `future-boundary`
(source union, Async default + Sync, the `ImgFailed`-src fix), web
onload→phase + min-load timer. **Designed, deferred:** `stream-boundary` /
`Active` builder + coalescing, `restart-on`/deps sugar, true
forking-cancellation, progress sugar, blurhash/progressive image.

## Testing

- Headless `future-boundary` (`test/ui/async-boundary.kk`): a `run` resolving
  after N settles goes placeholder→ready; a throwing `run`→failed; the
  default-error retry re-runs (a run that fails once then succeeds → retry →
  ready); `min-load` holds the placeholder past a fast resolve (advance the
  test clock). The result-value round-trips through the erased store correctly.
- Image on top (native live tier): async load goes placeholder→ready across
  settles (via `image-cache-size`/`live-textures`); `Sync` is ready frame 1;
  `FromBytes` decodes; `FromPixels` uploads; the frame clock keeps ticking
  during a decode (no render-thread block — the whole point); retention/leak
  guard hold; a failed image's retry re-kicks the decode.
- Suite counts updated; gallery sample gains a placeholder + a retry demo.

## Plan sequencing

1. `async-boundary`/`future-boundary` primitive + generation + retry
   (headless-testable with a plain async `run`, no image/GPU).
2. Rebuild `image` on `future-boundary` (source union, decode-off-thread /
   upload-on-render, Sync, cache/leak/retention, the `ImgFailed`-src fix).
3. Web parity (onload→phase, min-load timer, Bytes/Pixels lowering).
4. Gallery sample (placeholder + retry) + ledger + suite.
