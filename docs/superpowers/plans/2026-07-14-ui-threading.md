# Threading via extended libuv — implementation plan

> Worktree agent brief. Branch off `clang-wasm`. Extend **libuv** (per-thread
> async loops + thread-safe channels), NOT the old `std/os/task` pthread pool.
> Async must work on every thread. **Layout + render + the ltree stay on ONE
> thread (main) so FBIP in-place reconcile is preserved.** Configurable.

**Goal:** let data-processing (and later `update`) run on their own OS threads,
each with a full libuv/async loop, connected by channels — without moving the
widget/layout/render path off the single UI thread.

## Hard constraints (verified in the codebase)

- Today ONE libuv loop, ONE thread; `app` forks `pump`/`drain-state`/`loop`/subs
  as cooperative strands (`lib/ui/app.kk:70-76`).
- `std/async` has **no `uv_async`/thread bridge** (`lib/std/async/api/uv/evloop.c`
  is a single `uv_run`). `std/os/task` (pthread pool) exists but is pure-only,
  experimental — **do not use it**; extend libuv instead.
- Heap is **thread-local**; Perceus refcounts non-atomic. Anything crossing a
  thread must be `mark_shared` (atomic refcounts; runtime has
  `kk_block_mark_shared`, `kklib/src/refcount.c`, `kklib/src/thread.c:365`) or
  copied. Non-atomic channel/global mutation across threads is UB.
- **GLFW/Cocoa event poll + Metal present MUST stay on the main thread.** So the
  render/layout/event thread IS the main thread; only update + data move off.
- Web/wasi have no OS threads — every new primitive must **degrade to a
  cooperative strand** on those hosts (same API, so apps stay portable).

## Architecture

1. **Per-thread async loop** — start an OS thread that runs its OWN `uv_loop` +
   the full `async` effect handler, so `spawn`/`wait`/timers/channels work there
   exactly as on main.
2. **Thread-safe channel** — a channel owned by loop A can be `emit`'d from thread
   B: enqueue under a mutex, then `uv_async_send` to wake A's loop, which delivers
   to the waiting `receive`. Payload is `mark_shared` before crossing. Keep the
   existing single-thread fast path unchanged.
3. **Topology, configurable on `app(..., threads = ...)`:**
   - `Single` (default) — one thread, cooperative strands. **Zero behavior
     change**; the whole existing suite + bench must stay green (hard gate).
   - `Threaded` — UI/render thread = main (event poll, layout, reconcile, paint,
     the ltree, ui/state — single-threaded, FBIP intact). Data threads run heavy
     work; `update`-on-its-own-thread is a later increment.
4. **Invariant:** layout/reconcile/paint/ltree/ui-state never leave the UI thread;
   only immutable `widget<msg>`/`msg`/data values cross (mark_shared).

## Files

- **`lib/std/async/api/uv/evloop.c` + `evloop.kk`** — add `uv_async` handle
  binding (`uv_async_init`/`uv_async_send`/close) and a thread-spawn primitive
  (`uv_thread_create` wrapper) that inits + runs a fresh `uv_loop` on the new
  thread; a `mark_shared` extern (`kk_block_mark_shared`).
- **`lib/std/async/*.kk`** — a `spawn-thread(body : () -> <async,ioc> ()) : ioc
  thread` (native/libc; cooperative-strand fallback for `[host=jsweb|wasi-web|
  wasmweb]` via the existing host split) and a cross-thread-capable channel path
  (or a `shared-channel` variant) built on the async loop ownership + uv_async.
  Follow the existing `[host=...]` conditional-import pattern used by
  `async.kk:61-63`.
- **`lib/ui/app.kk`** — a `threads` config arg (default `Single`); `Threaded`
  routes the data/worker strand(s) onto OS threads via `spawn-thread`, keeping
  `pump`/render/`drain-state`/`loop` on main. The `forking` block at
  `app.kk:70-76` is the seam.
- **`samples/ui/thread-demo/`** (or extend counter) — a native app that offloads a
  heavy compute to a worker; UI animation keeps ticking during it.

## Increment 1 — data-offload (do this first; lowest risk)

Route a heavy computation onto a worker thread; deliver the result back as a
message. **No widget tree crosses threads** in this increment.

- Primitive: `compute<a>( work : () -> pure a ) : async a` (or `spawn`-shaped) —
  runs `work` on a worker thread's loop (or libuv threadpool), `mark_shared` the
  result, delivers it to the caller's loop via a thread-safe channel + uv_async.
  `work` must be pure/total over shared-immutable input (document this).
- Wire into `app`: under `Threaded`, a `spawn`/`compute` in `update` runs on a
  worker; its result re-enters as a message on the main loop (mirrors the existing
  `spawn`-result-as-message path at `app.kk:94-95`, but cross-thread).
- **Verify:** a native app computes something heavy (e.g. the JSON/DFA parse from
  the json-bench work) off-thread while a `clock`/`every`-driven animation on the
  UI thread keeps advancing smoothly (proves the UI thread isn't blocked); the
  result lands as a message and updates the model. Compare against `Single` mode
  (UI stalls during the compute) to show the difference.

## Increment 2 — update on its own thread (gated on #1)

Run `update` on a dedicated thread; marshal the produced immutable `widget<msg>`
to the UI thread (mark_shared) where reconcile + paint run. The ltree never
crosses. Only start this once #1 is solid and merged.

## Steps

1. libuv C bindings: `uv_async` init/send/close + `uv_thread_create` wrapper +
   `mark_shared` extern in `api/uv/evloop.{c,kk}`. Unit-spike: spawn a thread that
   runs a trivial async body (a timer), joins/exits cleanly.
2. Thread-safe channel path: cross-thread `emit` (mutex + `uv_async_send`),
   `mark_shared` payload; single-thread path unchanged. Spike: producer thread →
   consumer main loop receives N messages in order, refcounts sane (no leak under
   `--target` leak checks if available).
3. `spawn-thread` + `compute`; host fallbacks (web/wasi = cooperative strand).
4. `app` `threads` config; wire data-offload under `Threaded`.
5. Native demo + verification (animation-during-compute). `Single` mode: full
   `util/test-wasi.sh` green + bench byte-identical (**hard gate**).

## Verification

- **Single (regression gate):** entire `util/test-wasi.sh` green; `lib/ui/bench`
  byte-identical; every existing sample unchanged.
- **Threaded (native):** the animation-during-heavy-compute demo stays smooth;
  result arrives as a message. No crashes/leaks; clean thread shutdown on window
  close.

## Follow-ups (notes only)

- Worker POOL (N threads) + bounded/back-pressured channels; work-stealing.
- Cross-thread cancellation (async-cancel across loops).
- Minimize `mark_shared` cost (mark only what crosses; small-payload copies).
- Cocoa nested-resize stall: a render thread that keeps drawing during a
  main-thread AppKit modal loop — hard (Metal drawable/AppKit rules); separate
  investigation.
- Real Web Workers (jsweb/wasi, structured-clone) — different mechanism, later.

## Coordination

Touches `lib/std/async/*` (disjoint from overlays), `lib/ui/app.kk`, and possibly
`lib/ui/api/impeller/backend.kk` (the shared hotspots). The overlays MVP does NOT
touch these, so parallel work is safe; flag any `app.kk`/`backend.kk` change to
the supervisor before it lands so it can be sequenced against the overlays
native-window follow-up.
