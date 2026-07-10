# Native-clang WASI targets (`wasi` / `wasi-web`) — Design

Date: 2026-07-07 (rev 2: wasip3-first)
Branch: `clang-wasm` (off `dev`)
Status: approved design, pre-implementation

## Motivation

Koka's current wasm targets (`wasm`, `wasmjs`, `wasmweb`) all compile through
emscripten (`emcc`), even the "wasi" flavor (which is emscripten with
`-D__wasi__` defined — see `ccFromPath` in `src/Compile/Options.hs`). Emscripten
brings a ~1GB SDK, a bespoke ABI and JS prelude, and non-standard semantics.
Clang has mature native WebAssembly support via the wasi-sdk toolchain, which
produces standard **WebAssembly components** (the clang driver links through
`wasm-component-ld` automatically for wasip2/wasip3 targets).

This design adds two new **parallel** targets using native clang, leaving the
existing emcc targets untouched:

- **`wasi`** — standalone **WASI 0.3** component (`--target=wasm32-wasip3`);
  runs under `wasmtime run` (wasmtime 43+).
- **`wasi-web`** — the same component running in browsers and node via
  [jco](https://github.com/bytecodealliance/jco) transpilation. This is the
  primary focus.

### Why WASI 0.3 (wasip3) rather than 0.2

WASI 0.3.0 shipped June 11, 2026. It rebases WASI onto the component model's
**native async** primitives: `async func`, `stream<T>`, `future<T>`, and a task
system (tasks, waitable-sets, `task.return`). This eliminates the need for any
custom event-loop interop: a timer is just an async call to
`wasi:clocks/monotonic-clock.wait-for`.

Koka is architecturally an ideal fit for P3's **stackless callback ABI**: an
async export returns "not done — invoke my callback when a waitable fires",
with continuation state kept on the heap. Koka's `std/async` is built on effect
handlers, which already keep all pending state in the Koka heap rather than on
the C stack. No stack switching is needed *inside* the component.

Koka is experimental and will not be widely deployed on the web before the P3
ecosystem matures, so we target the standards-track endpoint directly instead
of building interim wasip2 machinery.

### Browser story and JSPI

Browsers do not run components natively; **jco transpilation is the browser
story**. jco's async component support uses **JSPI** (`--async-mode jspi`).
JSPI status (July 2026): standardized (phase 4, W3C CG April 2025); shipped in
Chrome 137+ and Node 24+; **Safari 27 beta (June 2026) includes it**; Firefox
behind a flag since 131; JSPI is an Interop 2026 focus area, so consistent
support across all engines is expected within the year. Requiring JSPI is
acceptable for an experimental language; older browsers are out of scope.

(WebKit's earlier formal objection to JSPI was withdrawn in late 2025 — the
"Safari problem" is historical.)

### Tradeoffs vs emscripten

Gains: no emsdk dependency; smaller, standards-conformant output; identical
WASI semantics between wasmtime and the browser; component-model/WIT as the
interop story instead of `EM_JS`/`ccall`; native async instead of emscripten's
unwind-the-main-loop trick; regular wasm + DWARF debugging.

Costs: jco (npm) becomes a build-time dependency for `wasi-web`; the P3 C
toolchain (wasip3 sysroot, wit-bindgen C async, jco async) is young — WASI
0.3.0 is weeks old. Risk is managed via an early spike (see Phasing) and a
documented fallback (see Appendix).

## Targets & naming

- CLI target names: `wasi`, `wasi-web`. New `CTarget` constructors `Wasi` and
  `WasiWeb` in `src/Common/Syntax.hs` alongside `Wasm | WasmJs | WasmWeb`.
- Both are wasm32 (`platform32`); wasm64 is out of scope.
- Buildcfg host tags: `wasi` and `wasi-web` (fall back to `wasiweb` if the
  `[host=...]` lexer rejects hyphens — check during implementation).
- Two targets, deliberately kept split: the run/glue pipelines differ (wasmtime
  vs jco), and `wasi-web` additionally supports **custom JS-host interfaces**
  (e.g. DOM access) that wasmtime cannot satisfy. The evloop itself is shared
  (native P3 async on both).

## Toolchain

**Prerequisite:** official wasi-sdk **binary release** with a first-class
`wasm32-wasip3` target: minimum **34** (currently 34-rc; expected stable
imminently — wasip3 has been building since 31, and 34 removes the legacy
`wasm32-wasi` target, confirming the direction). Hard error below the minimum.
Develop against 34-rc; bump the recommended version as releases land.

Discovery order for the SDK root:
1. `--wasisdk=<dir>` flag (new field in `Flags`)
2. `WASI_SDK_PATH` environment variable
3. Probe well-known locations: `/opt/wasi-sdk`, `~/wasi-sdk-*` — validated by
   presence of `bin/clang` and `share/wasi-sysroot`.

Version check reads `<sdk>/VERSION` from the release tarball layout.
If not found: clear error with the GitHub releases download URL. Auto-download
is explicitly deferred to the vscode extension / install script (not the
compiler).

**CC configuration** (`src/Compile/Options.hs`): a new `wasiClang` CC derived
from `ccGcc`:
- Invoke `<sdk>/bin/clang --target=wasm32-wasip3` (driver finds its own
  sysroot/compiler-rt and links via `wasm-component-ld`, emitting a component).
  We always pass the target explicitly (wasi-sdk 31 changed the default target;
  relying on defaults is fragile).
- `ccFlagStack`: `-Wl,-z,stack-size=<n>` (wasm-ld syntax); heap flags are a
  no-op (memory grows on demand).
- Executable extension `.wasm` for both targets; object/lib naming as gcc.
- The "should use emcc" warning and `detectCC`'s emcc preference apply only to
  the legacy emcc targets, not `wasi`/`wasi-web`.

**Runtimes:**
- `C Wasi`: `wasmtime run <out>.wasm` — requires wasmtime **43+** (WASI 0.3);
  respects the existing `--wasmrun` flag.
- `C WasiWeb`: `node <outdir>/run.mjs` (node 24+, JSPI) for terminal runs;
  `index.html` for the browser.

**De-risk note:** all *synchronous* code compiles identically under
`--target=wasm32-wasip2`; if the wasip3 sysroot proves broken during phase 1,
sync phases can proceed on wasip2 with only the target-triple string changed,
without altering this design.

## kklib / runtime

- **Allocator:** mimalloc supports wasi (sbrk/`memory.grow`, no mmap). Verify
  under wasip3; if problematic, these targets initially force
  `KK_USE_STD_ALLOC` (wasi-libc dlmalloc) — correctness first.
- **Existing `__wasi__` conditionals** (`os.c`, `process.c`, `random.c`,
  `atomic.h`) carry over; real wasi-libc implements more POSIX than
  emscripten's `-D__wasi__` shim did, so expect fewer stubs. Single-threaded.
- **Async main:** the component's `wasi:cli/run` export is lifted **async
  (stackless callback ABI)**. `kk_main` runs the Koka program; if the event
  loop holds live references (pending timers/promises) when the program's
  direct execution returns, the run task does **not** `task.return` yet — the
  task stays live and the runtime re-enters via task callbacks until the loop
  refcount reaches zero, then delivers the exit code and tears down
  (`kk_free_context`). This is the standardized equivalent of emscripten's
  `EXIT_RUNTIME=0` unwind trick, possible because effect handlers keep pending
  state on the Koka heap, not the C stack.

## Event loop on native P3 async

No custom WIT is authored. The evloop primitives map to standard WASI 0.3:

- `timer-setup(evloop, ms, cb)` — start a subtask calling async
  `wasi:clocks/monotonic-clock.wait-for(ms)`; register `cb` in a heap table
  keyed by the subtask; when the task-callback reports completion, invoke `cb`.
  Cancellation (the returned dispose function) uses subtask cancellation.
- `immediate-setup` — degenerate `wait-for(0)` (or `task.yield` if exposed).
- `event-loop-init/run` — maintain the loop refcount consulted by async main
  (above); `run` returns immediately (the task system is the loop).

Guest-side bindings come from **wit-bindgen C in async mode** against the
`wasi:cli` 0.3 world; generated bindings for the runtime support code are
**committed** to the repo so wit-bindgen is not a user-facing dependency.

New files (mirroring the existing `lib/std/async/api/web/` structure):
- `lib/std/async/api/wasi/evloop.{kk,c}` — the P3 evloop above, shared by both
  targets if the bindings are host-agnostic (expected; see Targets & naming).
- `lib/std/async/async.kk` conditional imports gain:

```
[host=wasi|wasi-web]  async/api/wasi/evloop   // native WASI 0.3 async
```

## `wasi-web` host package

Build output for `--target=wasi-web`:

```
<out>/
  main.wasm        # the component
  host/            # jco transpile output (core wasm + JS bindings, JSPI mode)
  index.html       # minimal page (like wasmweb today)
  run.mjs          # node entry point
```

Build step: `jco transpile main.wasm --async-mode jspi -o host/` via npx/node;
missing jco is a clear error naming the install command. jco is a dependency of
the `wasi-web` target only; pin a known-good jco version and warn on older.
The hand-written glue is minimal (instantiate + wire stdout/stderr to the page
or console) since jco supplies the WASI shim and async machinery.

## Phasing

0. **Spike (timeboxed, first)** — validate the load-bearing experimental
   pieces end-to-end *before* building on them: hand-written C hello-timer
   using wit-bindgen C async + `wasm32-wasip3`, run under wasmtime 43 and
   jco-JSPI in node + Chrome + Safari 27 beta. Exit criteria: async
   `wait-for` round-trips via the callback ABI in all three. If the spike
   fails, fall back to the Appendix design for async while keeping all other
   phases unchanged.
1. **`wasi`, sync** — toolchain discovery, targets/CC config, hello-world and a
   test-suite subset under wasmtime. Validates codegen + kklib on wasip3.
2. **`wasi-web`, sync** — jco transpile step, host package emission, browser +
   node hello-world. (Playground integration is follow-up work.)
3. **Async (primary deliverable)** — async main, P3 evloop, timer/async tests
   passing on wasmtime and in the browser.
4. **DOM interop demo** — a `wasi-web` sample (e.g. `samples/wasi-web/dom`)
   where Koka manipulates the DOM: a small hand-written `koka:dom` WIT
   interface (element lookup, set-text, add-event-listener with a callback
   export), C bindings via `wit-bindgen c` (committed, like the evloop
   bindings), Koka externs over them, and the JS-host implementation in the
   glue. Event listeners reuse the async-main keep-alive (the run task stays
   live while listeners are registered). This demo is the template for the
   later WIT-from-externs work and proves `wasi-web` interop beyond WASI.
5. **Out of scope / later** — wasi-sdk auto-download (vscode ext / install
   script), WIT generation from Koka externs, `stream`/`future` exposure in
   Koka APIs, `std/async/os/file` on these targets, wasm64, non-JSPI browsers.

## Testing

- Phase 1: run a subset of `test/` under `wasmtime` (gate on wasmtime 43+ and
  wasi-sdk presence); compare against the same `.kk.out` expectations as the C
  target.
- Phase 2: node-based smoke test of the transpiled output (stdout capture).
- Phase 3: timer/async tests from `test/` under node 24+ via `run.mjs`.
- CI: install wasi-sdk 34 + wasmtime 43+ + jco (pinned) in a dedicated job.

## Appendix: fallback — inverted event loop on wasip2 (no JSPI)

Retained as the fallback if the phase-0 spike shows the P3 toolchain is not
ready, and as a possible future "works on old browsers" build mode. This is
the emscripten technique, standardized by hand: control inversion instead of
blocking, so **no JSPI or asyncify is needed** and it runs in every current
browser.

- Target `wasm32-wasip2`; a small internal WIT world:

```wit
package koka:async@0.1.0;

interface timers {
  set-timeout: func(timer-id: u64, millisecs: u64) -> u32; // host handle
  clear-timeout: func(handle: u32);
}

world koka-web {
  include wasi:cli/imports@0.2.x;
  import timers;
  export wasi:cli/run@0.2.x;
  export dispatch: func(timer-id: u64);  // host -> wasm timer callback
  export loop-done: func() -> bool;      // host checks: tear down yet?
}
```

- `timer-setup` calls the `set-timeout` import with a fresh u64 id and stores
  the Koka callback in a heap table; the JS host implements timers over
  `setTimeout`/`clearTimeout` and re-enters wasm via the exported `dispatch`.
  `event-loop-run` returns immediately; main returns without teardown and the
  host drops the instance once `loop-done()` reports true.
- All boundary types are scalars, so the canonical ABI lowering is trivial;
  bindings generated once with `wit-bindgen c` and committed.
- The guest-side shape (heap-keyed callbacks + re-entry export) is identical
  to the P3 stackless callback ABI, so code structure is shared with the
  primary design.

## Rev 3 (2026-07-08): `wasi-web` moves to core modules + externref

Decision: `wasi-web` switches from wasip2 components/jco to **plain core modules**
(`--target=wasm32-wasip1`), while `wasi` stays components/wasip3 for wasmtime.

Rationale: (a) the canonical ABI is shared-nothing by design — no externref can
cross a component boundary, only lifted copies or u32 resource handles — which
blocks the key interop win below; (b) jco proved the weakest dependency (cannot
run wasip3; two open bugs); (c) we hand-write the JS glue either way.

Key design unlocked — **Perceus-owned JS references (`kk_js_obj`)**: a normal
kklib boxed value whose payload is an i32 slot into a module-local `externref`
table (clang `__externref_t` + `__builtin_wasm_table_get/set/grow`), with a
free-list for slot reuse. Perceus drop → `table.set(slot, null)` + free-list
push: deterministic, refcount-driven release of JS objects; no JS-side Map; no
finalizers. DOM values (elements, strings we don't inspect) stay JS-side,
copy-free. Strings that must cross go as (ptr,len) + TextDecoder.

WASI in the host: node via built-in `node:wasi` (preview1); browser via
`@bjorn3/browser_wasi_shim`. The inverted event loop, keepalive (weak symbol),
channel-based listener API, and `dom.kk` surface carry over unchanged — only
the fringe changes (attribute imports/exports instead of wit-bindgen; import
object instead of jco `--map`). WIT `resource`s remain the migration path back
to components if/when jco matures (same handle+drop shape, Perceus-compatible).
