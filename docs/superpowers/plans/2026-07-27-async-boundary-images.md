# Async boundaries + async/sync image loading Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A first-class `future-boundary` async widget (placeholder → ready/failed, retry, min-load) per `docs/superpowers/specs/2026-07-27-async-boundary-images-design.md`, with `image` rebuilt as its first customer (async decode-off-thread/upload-on-render, Sync opt-in, source union).

**Architecture:** Load phase lives in `ui/state` (build-readable, identity-keyed, erased like `use-state`) with a per-key **generation**; a build kicks a "want" when the generation changed; an **async-pump strand** (app-forked like `pump`) forks each `run` under try + min-load and writes the phase back. `retry` = bump the generation. `image`'s `run` does `compute(decode)` off-thread then uploads on the render thread inside itself (the async-pump is a render thread strand), so image is a plain `future-boundary` customer.

**Tech Stack:** Koka (lib/ui), `std/async` (channels/strands/`compute`/`wait`), Impeller shim (C), web DOM.

## Global Constraints

- Load phase in `ui/state` keyed by identity id (int32), erased (the `erase`/`unerase`/`cell`-store pattern in lib/ui/state.kk); result value stored erased, un-erased at the read site.
- **Generation** (per-key epoch) is the ONE mechanism for retry + stale-discard (cancellation floor): a `run` writes its result tagged with the generation it ran under; a stale generation's result is DISCARDED. `retry()` = bump the generation.
- **Shared contract, specialized mechanism**: ship `future-boundary` (lean: fork→await→store→exit, states Pending→Done|Failed, no channel/Active/coalescing) + the `async-snapshot<a>` TYPE. The low-level stream-capable `async-boundary`(yield-run) + `stream-boundary`/`Active`/coalescing are DEFERRED (they are the stream mechanism). [Scoping refinement of the spec's "async-boundary ships now" line — the TYPE ships; the yield-delivery impl defers with stream.]
- `future-boundary` runs a `run` ONCE per identity+generation, not per rebuild.
- The async-pump strand is a MAIN/render-thread strand (forked in run-single AND run-threaded next to `pump`/`drain-state`), so `compute` inside a `run` resumes on the render thread (required for image's GPU upload).
- Native image `load = Async` (default): placeholder → `compute`-decode off-thread → upload on render → ready. `load = Sync`: decode+upload inline in paint (today's path). `FromPixels` uploads only. Native = local/asset PATHS (`stbi_load`, no URL fetch); URLs are web-only.
- GPU upload is render-thread ONLY; upload ONCE per (owner, decoded pixels), cache by owner, free via `prune-images` retention; `g_live_tex` leak-guard stays balanced. `ImgFailed` carries `src`, re-decodes on a src swap (the prior review residual).
- Web honors placeholder + min-load via an `onload`→phase listener + a min-load timer; `load` ignored on web.
- Koka gotchas: `0.0 - expr` (no unary minus); named local funs; `?key : key` implicit on widget ctors; erased store's one guarded coercion; exhaustive-match = the walk checklist; koka doesn't rebuild on .c change (clear LOCAL .koka / `-r`); live tier -O1; wasi-web node≥24; the `.m` field-shadow (avoid `val m`).

## File Map

| File | Change |
|---|---|
| `lib/ui/reactive.kk` | async-phase store: `int32-map<async-entry>` + ops (get/set/bump-gen) |
| `lib/ui/state.kk` | pub `async-phase`/`set-async-phase`/`bump-async-gen` wrappers; `async-snapshot` re-export |
| `lib/ui/async.kk` | NEW: `async-snapshot` type, `future-boundary`, the want channel + `async-pump` strand, `default-error`/`default-placeholder` |
| `lib/ui/app.kk` | fork `async-pump` in run-single + run-threaded; install the want channel |
| `lib/ui/widget.kk` | `image-source` union; `image` rebuilt on `future-boundary` (Async) + Sync path; `image-path` sugar |
| `lib/ui/api/impeller/{shim.c,impeller.kk,backend.kk}` | `stbi_load_from_memory` + pixels-upload bindings; Async run's decode+upload; Sync inline; cache/leak/retention; `ImgFailed(src)` |
| `lib/ui/api/web/backend.kk` + `lib/web-ui/api/*/dom.*` | image `<img>`/`<canvas>`/data-url lowering + onload→phase + min-load timer |
| `test/ui/async-boundary.kk`, `test/ui/image.kk` (or basic) | NEW/extended headless + native tests |
| `samples/ui/gallery/main.kk`, `util/test-wasi.sh`, `docs/ui/design-notes.md` | placeholder+retry demo, suite, ledger §16 |

Tasks 1–2 are the primitive (headless, no image/GPU). Task 3 rebuilds image native. Task 4 web parity. Task 5 sample+docs.

---

### Task 1: async-phase store + generation (ui/state)

**Files:** Modify `lib/ui/reactive.kk` (uistate handler), `lib/ui/state.kk` (pub wrappers). Test: `test/ui/async-store.kk` (standalone, direct ops).

**Interfaces (produces):**
```koka
// stored per identity id; the snapshot value is erased (any). generation is the epoch.
pub type raw-phase
  RPending
  RDone( value : any )
  RFailed( err : exception )
pub struct async-entry( gen : int, phase : raw-phase )
// uistate ops (in the with-uistate handler + effect):
fun get-async( id : int ) : maybe<async-entry>
fun set-async( id : int, e : async-entry ) : ()
fun bump-async-gen( id : int ) : int    // increment this id's generation, return the NEW gen; entry becomes RPending at the new gen
```

- [ ] **Step 1:** add the effect ops + handler state to `lib/ui/reactive.kk`: `var asyncs : int32-map<async-entry> := int32-map/empty()`. `get-async(id) = asyncs.lookup(id.int32)`. `set-async(id, e) = asyncs := asyncs.set(id.int32, e)`. `bump-async-gen(id)`: read current gen (0 if absent), `g = cur+1`, `asyncs := asyncs.set(id.int32, Async-entry(g, RPending))`, return `g`. Add all three to the `uistate` effect decl AND handler AND `reset-uistate` (clear `asyncs`). `RActive` is NOT added now (deferred stream) — leave a comment that a stream RActive(any) variant slots in here.
  - `Active`-store note: `raw-phase` deliberately has no RActive yet; adding it later is additive.
- [ ] **Step 2:** `lib/ui/state.kk` pub wrappers (build/strand-callable): `pub fun async-phase(id : int) : uistate maybe<async-entry> = get-async(id)`, `pub fun set-async-phase(id, gen, phase) : <uistate,ioc> () = emit-transition(fn() set-async(id, Async-entry(gen, phase)))`, `pub fun bump-async-gen-io(id : int) : <uistate,ioc> int` — a transition that bumps + returns... note: a transition is deferred (drain-state), so returning the new gen synchronously needs the bump to happen on read. SIMPLER: `pub fun current-async-gen(id) : uistate int` (reads gen, 0 if absent) and `pub fun retry-async(id) : <uistate,ioc> () = emit-transition(fn() { bump-async-gen(id); () })`. The build computes "should I kick?" from `current-async-gen` vs the running-gen stored in the entry.
- [ ] **Step 3: test** `test/ui/async-store.kk` (standalone self-checking, like test/ui/selector.kk — `with-uistate` wraps direct ops; a fail counter + "ASYNC-STORE: n/m"): assert get on empty → Nothing; set then get round-trips the entry (erase a known int as the value, unerase on read → equal); bump-gen on absent → 1 (RPending); bump again → 2; set a Done then bump → gen advances + phase resets to RPending (stale-discard basis). Run `stack exec koka -- -v0 --console=raw -ilib -itest/ui -e test/ui/async-store.kk`.
- [ ] **Step 4:** green; basic 15/15 unaffected.
- [ ] **Step 5:** commit `git commit -am "ui/state: async-phase store + generation (foundation for async boundaries)"`.

### Task 2: `future-boundary` + async-pump strand

**Files:** Create `lib/ui/async.kk`; modify `lib/ui/app.kk` (fork the pump + install the channel). Test: `test/ui/async-boundary.kk`.

**Interfaces (produces):**
```koka
pub type async-snapshot<a>       // the SHARED contract (Active reserved for stream, deferred)
  Pending
  Done( value : a )
  Failed( err : exception )
pub fun future-boundary<a,msg>( run : () -> <async,ioc> a,
                                ready : (a) -> <keytree,uistate,ioc> widget<msg>,
                                placeholder : widget<msg> = default-placeholder(),
                                failed : (exception, () -> <uistate,ioc> ()) -> <keytree,uistate,ioc> widget<msg> = default-error,
                                min-load : duration = zero,
                                ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
// the want the build emits to the async-pump; the pump forks each run.
pub struct async-want( id : int, gen : int, run : () -> <async,ioc> any, min-load : duration )
pub fun install-async-channel( ch : channel<async-want> ) : ioc ()
pub fun async-pump( fork : (() -> <async,uistate,ioc,exn> ()) -> ioc () ) : <async,uistate,ioc,exn> ()
```

- [ ] **Step 1:** `lib/ui/async.kk`. `future-boundary`:
  - `val bkey = kt-child(?key, Slot("ab", ?kk-file-line))` ; `val id = bkey.key-id`.
  - Read `async-phase(id)`. Determine the CURRENT generation `g` = the entry's gen (or 0 if absent). Decide a KICK when: absent (no entry) OR the entry's phase is RPending AND its gen has not yet been dispatched. To track "dispatched", the ENTRY's gen IS the running gen; the build dispatches once per new gen. Use this rule: keep a build-local memo is not possible (build is stateless); instead, dispatch when the entry is absent (first) — set RPending(gen=1) + emit want(id, 1, ...). On a Done/Failed entry, no kick. On RPending, no re-kick (already dispatched — the entry existing at gen G means want G was emitted). retry (below) bumps to RPending(G+1) via a transition AND must emit a fresh want — so `retry` both bumps the store AND emits the want (not just bumps). So: KICK (emit want + set RPending) happens (a) on absent, (b) inside `retry`. That keeps "emit exactly once per generation".
  - So: `match async-phase(id) { Nothing -> { kick(id, 1, run-erased, min-load); placeholder } ; Just(Async-entry(g, RPending)) -> placeholder ; Just(Async-entry(g, RDone(v))) -> ready(unerase(v)) ; Just(Async-entry(g, RFailed(e))) -> failed(e, retry-fn) }` where `kick(id, gen, run, ml) = { set-async-phase(id, gen, RPending); emit-want(Async-want(id, gen, run, ml)) }` and `retry-fn = fn() { val ng = current-async-gen(id) + 1; kick(id, ng, run-erased, min-load) }`.
  - `run-erased = fn() erase(run())` (the pump stores/handles `any`; the build unerase's on read).
  - `default-placeholder()` = a neutral box (`box(column([spacer()]), ...)` sized small — grep the old image placeholder fill). `default-error(e, retry)` = `column([ text("failed: " ++ e.show), primary-button-or-act("Retry", retry) ])` — use `act(box(text("Retry")), retry)` (an ioc thunk, no msg; grep `act`).
- [ ] **Step 2:** `async-pump` strand + channel. `install-async-channel` stores the channel in a ref (like install-state-channel). `emit-want(w)` emits to it. `async-pump(fork)`:
  ```
  val w = (channel).receive
  fork fn()
    with handle/try fn(e) set-async-phase(w.id, w.gen, RFailed(e))
    val t0 = ticks-ms()
    val r = w.run()                       // awaits async; compute inside offloads
    val elapsed = ticks-ms() - t0
    if elapsed < w.min-load.milli-seconds.float64 then wait((w.min-load.milli-seconds.float64 - elapsed).milli-seconds)
    // STALE-DISCARD: only write if this gen is still current
    match async-phase(w.id) { Just(Async-entry(cur, _)) | cur == w.gen -> set-async-phase(w.id, w.gen, RDone(r)) ; _ -> () }
  async-pump(fork)
  ```
  (grep ticks-ms / the anim-driver for the clock; `wait` from std/async.)
- [ ] **Step 3:** `lib/ui/app.kk`: in run-single AND run-threaded, `val async-ch = channel(); install-async-channel(async-ch)` (near install-state-channel) and `fork( fn() async-pump(fork) )` (next to `fork( fn() drain-state(rerender) )`). Note: `async-pump` needs the `fork` closure — pass it (like `loop` receives fork).
- [ ] **Step 4: test** `test/ui/async-boundary.kk` (a `test-scenarios` app). Model holds nothing; the view has a `future-boundary`:
  - a `run` that resolves after a delay: `fn() { wait(30.milli-seconds); "hello" }`. Scenario: initially `t.texts` shows the placeholder marker; after `t.settle()` (a couple rounds, enough for the 30ms wait + min-load), `t.texts` shows the ready content ("hello"). (settle advances via the state channel + waits; ensure the wait resolves — the async-pump runs on the harness strands.)
  - a throwing run `fn() { wait(10.ms); throw("boom") }` → after settle, the failed content ("failed: boom") + a "Retry" control is present.
  - RETRY: a run that fails the FIRST time and succeeds after (use a use-state/model counter the run reads — or a module-global attempt counter): after fail, `t.click("Retry")`, settle, assert ready content. This pins generation+retry.
  - MIN-LOAD: a run resolving in ~1ms with `min-load = 60.ms` — assert the placeholder still shows right after a short settle, then ready after a longer settle. (If the deterministic test clock makes timing flaky, assert the ORDER via the phase store directly, or gate this assertion — pick a robust form.)
  Run: `stack exec koka -- -v0 --console=raw -ilib -itest/ui -e test/ui/async-boundary.kk`.
- [ ] **Step 5:** green; basic/retain/windows/lazy all green (app.kk change is additive — the async-pump strand idles when no boundary kicks).
- [ ] **Step 6:** commit `git commit -am "ui/async: future-boundary + async-pump strand (placeholder/ready/failed, retry, min-load)"`.

### Task 3: image on future-boundary (native)

**Files:** Modify `lib/ui/widget.kk` (image-source union, `image` rebuilt), `lib/ui/api/impeller/{shim.c,impeller.kk,backend.kk}`. Test: extend `test/ui/image.kk` / the live tier.

**Interfaces (produces):**
```koka
pub type image-source
  FromPath( path : string )
  FromBytes( bytes : vector<int8> )
  FromPixels( rgba : vector<int8>, w : int, h : int )
pub type image-load { Async; Sync }
pub fun image<msg>( source : image-source, fit : image-fit = Contain, load : image-load = Async,
                    placeholder : widget<msg> = default-placeholder(), min-load : duration = zero,
                    width = 0.0, height = 0.0, ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
pub fun image-path<msg>( src : string, fit : image-fit = Contain, ... ) : ... = image(FromPath(src), ...)
// impeller externs:
extern decode-path( path : string ) : ioc maybe<(int,int,int)>       // (bufptr, w, h) or Nothing
extern decode-bytes( bytes : vector<int8> ) : ioc maybe<(int,int,int)>
extern upload-pixels( bufptr : int, w : int, h : int ) : ioc int      // -> texture handle (0 on fail); consumes buf
extern upload-rgba( rgba : vector<int8>, w : int, h : int ) : ioc int // FromPixels: no decode
```

- [ ] **Step 1:** `image-source` union + rebuilt `image`. Keep the existing `LImage(owner, src, fit, w, h)` LEAF as the "draws a ready texture" node — but the owner's TEXTURE now lives in the backend cache keyed by owner (already true). `image()`:
  - `load = Sync` → today's behavior: emit the `LImage` leaf directly (paint decodes+uploads inline on first paint, per the current impeller path). (Keep the current sync path intact for Sync.)
  - `load = Async` → build a `future-boundary`:
    - `run = fn() { val px = compute-decode(source); render-upload(owner-id, px) }` where `compute-decode` runs the decode OFF-thread via `compute(fn() decode-source(source))` returning `(bufptr,w,h)` or throwing on failure, and `render-upload` (on return = render thread) calls `upload-pixels`/`upload-rgba` → stores the texture in the backend cache keyed by the boundary's owner id (a new `backend/put-image-texture(id, tex, w, h)` extern-ish fn) → returns unit. `decode-source`: FromPath→decode-path; FromBytes→decode-bytes; FromPixels→(no decode, pass the rgba through to upload-rgba on the render thread).
    - `ready = fn(_) LImage-drawing-cached-texture` — emit an `LImage(owner, <src-or-marker>, fit, w, h)` whose paint arm draws the owner's cached texture (the texture is already uploaded by run). NOTE: reconcile the owner id: the future-boundary mints `Slot("ab")` under ?key; the image leaf must draw the texture cached under the SAME id the run uploaded to. Thread ONE id (the boundary's) to both the run's upload and the leaf. Document it.
    - `placeholder`/`min-load` passed through.
- [ ] **Step 2:** shim: `stbi_load_from_memory` for `decode-bytes` (read the vector<int8> into a buffer — grep how a vector is read in C, e.g. the kk_imp_transform vector read, but bytes: `kk_vector` of int8/bytes → `kk_bytes`? check the koka `vector<int8>` C repr; may be simpler to accept `kk_bytes`/string). SPLIT the existing `decode-image`+`texture-create` into `decode-path`/`decode-bytes` (return bufptr+dims, do NOT free) and `upload-pixels`(bufptr,w,h→tex, frees/uploads buf) — so the decode can run in `compute` and the upload separately on the render thread. `upload-rgba(rgba,w,h)` copies the koka bytes → a buffer → texture (FromPixels). Keep `g_live_tex` balanced (++ on upload success, -- on release). impeller.kk externs.
- [ ] **Step 3:** backend: a per-owner texture cache is ALREADY there (imgcache). Add `put-image-texture(id, tex, iw, ih)` (called by the Async run's upload step) storing `ImgReady(tex, iw, ih, marker)`; the `LImage` paint arm draws `image-for-cached(owner)` (draw if ImgReady, else the placeholder fill — but under Async the boundary shows the widget-level placeholder, so the leaf only appears when ready; still keep a fill fallback). Keep the Sync path (`image-for(owner, src)` decode+upload inline). `prune-images` + `ImgFailed(src)` re-decode + leak-guard unchanged. Ensure the Async upload path also participates in `prune-images` (unmount releases).
- [ ] **Step 4: test** (native live tier — GPU/threads are native): async image goes placeholder→ready across settles (assert `image-live-textures` goes 0→1 after the load settles; the boundary's placeholder shows before); `Sync` image is ready frame 1 (texture present after one settle, no placeholder phase); a `FromBytes` (embed a tiny PNG's bytes) decodes → texture; `FromPixels` (a small rgba vector) uploads → texture; the frame clock keeps ticking during a decode (reuse the threads-sample idea: an animation runs while a slow image loads — or at minimum assert no deadlock/hang and exit 0); a failed image (bad path) → retry re-kicks (live-textures 0 → click Retry with a now-valid path... or assert the failed phase + that retry re-runs decode). Keep counts consistent.
- [ ] **Step 5:** gates: headless basic/retain/windows/lazy green; native live tier green incl. the new image asserts; gallery/counter native smoke exit 0; jsweb compiles (web image arm unchanged this task — web parity is Task 4, so Async on web must at least NOT break: web can keep the current `<img>` for now, the onload phase lands Task 4).
- [ ] **Step 6:** commit `git commit -am "ui/impeller: async image via future-boundary (decode off-thread, upload on render); Sync + source union"`.

### Task 4: web parity (onload→phase, min-load, Bytes/Pixels)

**Files:** Modify `lib/ui/api/web/backend.kk`, `lib/web-ui/api/jsweb/dom.{kk,js}`, `lib/web-ui/api/wasiweb/dom.{kk,c}` + `support/wasi-web/web-ui-host.js`.

- [ ] **Step 1:** web `image` under `load = Async` builds the SAME `future-boundary`, but its `run` is web-shaped: resolve when the browser reports the image loaded. Simplest robust form: the `<img>` (or `<canvas>`) is emitted by the `ready` builder; the PLACEHOLDER shows until an `onload` DOM event flips the phase. Wire: the LImage web lowering attaches an `onload` listener that posts an `EvImageLoaded(id)` (new web-ev) → the pump sets `set-async-phase(id, gen, RDone(()))`. Until then the boundary shows the placeholder. `min-load` on web: a timer strand (the async-pump's min-load wait already applies if the run is "wait for onload event"; model the web run as `fn() { await-onload(id); () }` where await-onload parks on a per-id signal the onload listener fires — OR the simpler event→phase path with a min-load timer). Pick the cleaner of: (a) run = await-onload (reuses future-boundary's min-load), or (b) direct event→phase + a separate min-load gate. Prefer (a): a web `await-onload(id)` extern that resolves when onload fires, so the SAME future-boundary min-load applies. Document the choice.
  - `FromBytes` → `<img src="data:image/png;base64," ++ base64(bytes)>` (a base64 encoder — grep std for one, or a small shim). `FromPixels` → a `<canvas>` sized w×h with `putImageData` (a `kk_dom_put_image_data(canvas, rgba, w, h)` extern). `FromPath` → `<img src=path>` (today).
- [ ] **Step 2:** dom externs (both hosts): `subscribe-image-onload(el, id)` / the base64 helper / `put-image-data`. Mirror jsweb dom.js ↔ wasiweb dom.c + web-ui-host.js table (the established lockstep). Touch owning .kk for bundled .js.
- [ ] **Step 3:** gates: web live tier — an image scenario (placeholder present pre-load, image present post-load) on jsweb; the general `future-boundary` also works on web (a plain async run resolves). basic headless still green; native live still green (native lowering untouched). wasi-web basic green (node≥24).
- [ ] **Step 4:** commit `git commit -am "ui/web: image onload->phase + min-load; FromBytes data-url + FromPixels canvas"`.

### Task 5: gallery (placeholder+retry) + ledger + suite

**Files:** Modify `samples/ui/gallery/main.kk`, `util/test-wasi.sh`, `docs/ui/design-notes.md`, `docs/ui/paper-outline.md`.

- [ ] **Step 1:** gallery: make the image row use `image(FromPath(...), placeholder = a-spinner-or-skeleton, min-load = 250.ms)` so the placeholder is visible; add one `future-boundary` demo (a `run` that `wait`s ~400ms then returns a value → a card) with a `default-error` retry path (a deliberately-failing run + Retry button); keep the flip-card. A tiny always-there icon uses `load = Sync` to show frame 1. Note web-only URL image stays.
- [ ] **Step 2:** smoke: native `KOKA_IMP_FRAMES=120 ./app-native` exit 0 (placeholder→image visible, flip works); jsweb loads in headless Chrome (`<img>` + onload; no console errors). EYEBALL note: placeholder visible then image; retry re-loads.
- [ ] **Step 3:** ledger §16 (terse, match §15 style): the async-boundary primitive (snapshot type + future-boundary + generation=retry+stale-discard + async-pump strand + min-load; shared-contract/specialized-mechanism, stream deferred); image as its first customer (source union, async decode-off/upload-on-render, Sync, web onload→phase); Tier + task pointers (stream/cancellation/deps deferred). Outline claims row.
- [ ] **Step 4:** full suite `./util/test-wasi.sh` green (known kklib first-run flakes rerun; update any pinned counts). No build artifacts committed.
- [ ] **Step 5:** commit `git commit -am "samples/ui/gallery async demo + ledger 16: async boundaries + async image land"`.

## Self-review notes
- Spec coverage: snapshot type + generation + retry + min-load + phase store (T1/T2), future-boundary primitive (T2), image on it native (T3), source union Path/Bytes/Pixels (T3 native + T4 web), Sync (T3), web onload→phase parity (T4), sample+ledger (T5). Deferred (stream/Active/coalescing, low-level async-boundary yield-impl, restart-on/deps, true forking-cancellation) explicitly scoped OUT and noted.
- Green-between-tasks: T1 store is additive; T2 async-pump idles unless a boundary kicks (existing apps unaffected); T3 keeps Sync = today's path so image never regresses; T4 web image keeps working (T3 note) until parity lands.
- Two empirical pins for implementers: (a) the min-load test timing under the deterministic clock (assert order/phase-store directly if wall-time is flaky); (b) the web run shape (await-onload vs event+timer — pick the one that reuses future-boundary's min-load).
- Type consistency: `async-snapshot`/`raw-phase`/`async-entry`/`future-boundary`/`async-want`/`image-source`/`image-load`/`image` names identical across tasks; the boundary's owner id threads to both the image run's upload and the leaf's draw (T3, flagged).
- Scoping refinement vs spec: spec lists low-level `async-boundary` as shipping; plan ships the TYPE + `future-boundary`, defers the yield-delivery impl with stream (noted in Global Constraints) — a reviewer/Tim call if the low-level should ship now.
