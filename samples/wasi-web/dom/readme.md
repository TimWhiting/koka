# DOM interop demo (`--target=wasi-web`)

A minimal counter app: Koka fetches `#counter` and `#btn` from the real
browser DOM, sets the counter's initial text, subscribes to the button's
`click` event as an async `channel<()>` (`dom.kk`'s `events`, built on
`std/async/channel.kk`), and loops `receive`-ing from it, updating the
counter text each time -- driven entirely by real DOM events dispatched back
into the wasm instance. There is no raw callback anywhere in the public Koka
API, and (Core Task 2, this rewrite) **no JS-side handle table either**: DOM
elements cross the wasm/JS boundary as `externref` values held in a
Perceus-owned table (`jsobj.c`), and dropping the last Koka reference to an
`element` is what releases the underlying JS object back to the browser's
own GC.

## Rev 3 / Core Task 2: what changed from the wit-bindgen/jco version

The previous version of this sample (`--target=wasi-web` when that target
was still a wasm32-wasip2 *component*) used `wit-bindgen c` to generate a
`koka:dom` component-model world (`koka-dom.wit`, `gen/koka_dom.{c,h}`), a
second `jco transpile --map` pass in `build.sh`, and a hand-written `dom.js`
host module holding a `Map<number, Element>` (browser handles were plain
`u32`s, looked up in that map on every DOM call). Core Task 1 retargeted
`--target=wasi-web` to a plain wasm32-wasip1 *core module* (no component
model at all, see `lib/std/async/api/wasiweb/evloop.c`); this task (Core Task
2) is the payoff of that retarget for this sample: real JS object references
now cross the boundary as `externref` values (a genuine host reference type,
not an integer key into a JS-side table), and Koka's own Perceus refcounting
drives when the browser gets to reclaim them. `koka-dom.wit`, `gen/`, and
`dom.js` are deleted; there is no jco anywhere in this path any more.

## Files

- `jsobj.c` / `jsobj.kk` -- the externref table primitive (sample-scoped for
  now; promotion to `lib/std` is a later decision). A module-local
  `static __externref_t kk_js_table[0]` (a wasm *table*, not a data array --
  see "Step 1: scratch compile" below) plus a free-list, exposing
  `kk_js_obj_alloc`/`kk_js_obj_get`/`kk_js_obj_box`/`kk_js_obj_slot_borrow`
  to `dom.c`, and a `koka:dom/live-slots` debug export used by the
  slot-recycling proof (see below). `jsobj.kk` only exposes `box` to Koka
  (wrapping a slot into a Perceus-refcounted `any`) -- everything else is
  C-only plumbing between `dom.c` and `jsobj.c`, forward-declared the same
  way `dom.c` forward-declares `evloop.c`'s `kk_wasiweb_loop_ref`.
- `dom.c` -- kept to the C-at-the-fringe minimum: the three `koka:dom`
  import attributes (`get-element-by-id`, `set-inner-text`,
  `add-event-listener`, plain `import_module`/`import_name` attributes, no
  wit-bindgen), canonical-ABI string marshaling, the externref <-> slot
  conversion via `jsobj.c`, storage of exactly one `kk_function_t` (the
  dispatcher `dom.kk` registers once at module init), and the
  `koka:dom/dispatch-event` export trampoline (`export_name` attribute) that
  dups+calls it and flushes stdio, mirroring
  `lib/std/async/api/wasiweb/evloop.c`'s `koka:async/dispatch`. No
  per-listener table or callback table lives in C.
- `dom.kk` -- Koka module `dom`: the public API is `element` (a value struct
  wrapping an `any` -- the Perceus-owned js-obj box, never a raw handle),
  `get-element-by-id` (returns `maybe<element>`, `Nothing` for a null
  externref), `set-inner-text`, and `events` (registers a listener and
  returns a fresh `channel<()>` instead of taking a callback). The id ->
  listener `ref`, the id counter (`std/core`'s `unique`), and the single
  dispatcher registered with `dom.c` all live here, not in C.
- `demo.kk` -- the app (module `demo`), plus `touch-tmp`, the slot-recycling
  proof's throwaway element lookup (see below).
- `index.html` -- the host page. Implements `koka:dom` as **plain functions
  that receive/return real DOM objects** (no `Map`, no handle table
  anywhere): `get-element-by-id` is just `document.getElementById` (already
  returns `null` for "not found", which the wasm boundary turns into a null
  externref on its own); `set-inner-text`/`add-event-listener` take the
  element back as a real JS reference. A small `decode(ptr,len)` helper reads
  UTF-8 strings out of `instance.exports.memory`. Also runs the auto-verify
  hook (two synthetic clicks + reading `koka:dom/live-slots`, see below).
- `build.sh` -- simplified for Core Task 2: the compiler's own
  `--target=wasi-web` post-link step (`wasiWebPostLink`) already emits
  everything a generic wasi-web program needs (`demo.wasm`, `run.mjs`, a
  generic `index.html`, `timers.js`, `vendor/browser_wasi_shim/`); this
  script just runs `koka --target=wasi-web` and then copies this sample's
  own `index.html` (the one implementing `koka:dom` + auto-verify) over the
  generic one. No second transpile pass, no `--cclinkopts` -- `dom.c` and
  `jsobj.c` are ordinary sample-local Koka modules (`dom.kk`/`jsobj.kk`) the
  compiler's module-dependency-driven linker (`codeGenLinkC`) already links
  in because `demo.kk` transitively imports them.

## Step 1: scratch compile (externref table intrinsics)

Before writing `jsobj.c`, its table declaration/grow/get/set syntax was
validated in a standalone file, compiled with the exact `WASI_SDK_PATH`
clang this repo uses (`clang version 23.0.0-wasi-sdk`,
`wasi-sdk-34.0-rc.1-arm64-macos`), targeting `wasm32-wasip1` (the same
target `--target=wasi-web` uses, see `src/Compile/Options.hs`):

```c
static __externref_t kk_js_table[0];               // a wasm *table*, not a data array

int32_t test_grow(int32_t n) {
  return __builtin_wasm_table_grow(kk_js_table, __builtin_wasm_ref_null_extern(), n);
}
void test_set(int32_t i, __externref_t r) { __builtin_wasm_table_set(kk_js_table, i, r); }
__externref_t test_get(int32_t i)          { return __builtin_wasm_table_get(kk_js_table, i); }
int32_t test_is_null(__externref_t r)      { return __builtin_wasm_ref_is_null_extern(r); }
```

Findings:

- **No extra clang flag needed.** `clang --target=wasm32-wasip1 -c ...`
  compiles all of the above (`__externref_t`, `__builtin_wasm_table_grow/
  set/get`, `__builtin_wasm_ref_null_extern`,
  `__builtin_wasm_ref_is_null_extern`) with **no** `-mreference-types` or
  similar flag -- reference types are unconditionally available on this
  target in this clang. This meant no change to `src/Compile/Options.hs`'s
  `wasicc` flags was needed.
- **node >= 24 needs no extra `WebAssembly` feature flag either** --
  `WebAssembly.instantiate` on a module using an externref table just works.
  Verified directly: grew the table, `table.set` a real JS object into slot
  1, read it back with `table.get` (`===` the original object), round-tripped
  it through a plain `(externref) -> externref` host import, and confirmed
  `__builtin_wasm_ref_is_null_extern` distinguishes a never-set slot (null)
  from a populated one.
- **A single-TU link (`clang a.c -o a.wasm`) and a default-entry, two-TU
  link (`clang a.o b.o -o out.wasm`, `main` in `b.c` calling into `a.c`'s
  table functions) both worked fine** with plain `-O1` and no special
  linker flags -- so cross-translation-unit calls into/out of the table
  primitive need no special handling either.
- **The one real gotcha: `-g` (debug info) breaks the link** -- see the next
  section. This is *not* a scratch-compile-time surprise (the scratch file
  above was compiled without `-g` first); it only showed up once the real
  `koka --target=wasi-web` build (which always passes `-g`, see
  `ccFlagsBuildFromFlags`) tried to link `jsobj.c`'s actual generated `.c`.

### The `-g` / debug-info gotcha (and its fix)

`koka`'s wasi-sdk C build always passes `-g -O1` (`src/Compile/Options.hs`).
Compiling `jsobj.c` with `-g` and linking produced:

```
wasm-ld: error: .../samples_wasi_dash_web_dom_jsobj.o: invalid data relocation: kk_js_table
```

Root cause: clang's DWARF emission for a global variable normally generates
a location-expression relocation that assumes a *data* symbol, but
`kk_js_table` is a wasm **table** symbol (a distinct symbol kind from
`.bss`/`.data` symbols) -- wasm-ld rejects the resulting relocation as
invalid. Reproduced minimally: a two-function scratch file compiling the
identical table pattern links fine at `-O1` without `-g`, and fails with the
exact same error once `-g` is added; removing `-g` (or building the real
generated `jsobj.c` without `-g`) links cleanly either way.

Fix: `__attribute__((nodebug))` on just the `kk_js_table` declaration
suppresses debug-info generation for that one variable (nothing else in the
file needs it -- ordinary globals/functions aren't affected), which
sidesteps the relocation mismatch entirely. Confirmed sufficient: the real
`koka --target=wasi-web` build links cleanly with `-g` restored everywhere
else. This is a one-line, sample-local fix (`jsobj.c`); it does not touch
`src/Compile/Options.hs` or any other compiler-level `-g` handling.

## Design decisions worth calling out

- **`element`, not raw handles**: the public API never exposes a bare
  integer or externref; `get-element-by-id` returns `maybe<element>`
  (`Nothing` for a null externref) and `element` wraps a Perceus-owned `any`
  (a `kk_cptr_raw_box` around a table slot, see `jsobj.c`/`jsobj.kk`).
  Dropping the last reference to that box is what releases the underlying JS
  object -- ordinary Perceus refcounting, no new kklib API, no GC/WeakRef
  machinery on the JS side.
- **Perceus ownership, concretely**: `kk_js_obj_box(slot, ctx)` wraps `slot`
  in a `kk_cptr_raw_box` whose free function (`kk_js_obj_free_fun`) is called
  by kklib exactly when the box's refcount hits zero. That free function
  does `table.set(slot, null)` (dropping wasm's own strong reference to the
  externref -- the browser's JS GC can now reclaim the object once nothing
  *else* references it) and pushes `slot` back onto the free-list for reuse.
  Every C function that receives an `element`'s boxed slot as a parameter
  (`set-inner-text-raw`, `add-event-listener-raw`) *owns* that reference
  (same convention as the `kk_string_t` it also receives) and calls
  `kk_box_drop` on it after use -- Koka's own Perceus-inserted `dup`s (for
  bindings still needed afterward, e.g. `counter` reused every loop
  iteration) are what keep a slot alive past a single call.
- **Slot 0 reserved invalid**: `kk_js_obj_alloc` never allocates slot 0, so a
  "not found" result (a null externref from `get-element-by-id`) can be
  represented as the integer `0` without ever touching the table --
  `dom.c` checks `__builtin_wasm_ref_is_null_extern` and returns `0`
  directly in that case, `dom.kk` turns that into `Nothing`.
- **`is-null` via a clang builtin, not an extra import**: the brief allowed
  either an extra `is-null(externref) -> i32` host import or a clang
  builtin; `__builtin_wasm_ref_is_null_extern` worked cleanly in the Step 1
  scratch compile, so no extra import namespace entry was needed.
- **Channels, not callbacks**: `events(elem,event) : <async,ndet>
  channel<()>` is the only public listener API -- unchanged from the
  previous rework, see the "Channels, not callbacks" reasoning that was
  already true before this task and still is.
- **Evloop refcount exposure**: unchanged from the previous rework --
  `dom.c`'s `add-listener` forwarding calls `kk_wasiweb_loop_ref`/`_unref`
  (non-static exports from `lib/std/async/api/wasiweb/evloop.c`) to keep
  `std/async`'s wasi-web evloop singleton alive for as long as any DOM
  listener is registered.

## Slot-recycling proof: the reasoning and the actual number

`jsobj.c` exports `koka:dom/live-slots` (`allocated - freed`, i.e. the number
of currently-live table slots). `demo.kk`'s `main` does three things that
touch the table:

1. `get-element-by-id("counter")` -- bound to `counter`, and *reused on every
   iteration* of the infinite `while` loop (`set-inner-text(counter,
   count.show)`). Because it is used again on the next iteration, Koka's
   Perceus keeps a live reference to `counter`'s box across the whole
   (suspended-on-`receive`, resumed-by-dispatch) loop -- **this slot never
   frees for the lifetime of the page.**
2. `get-element-by-id("btn")` -- bound to `btn`, and used **exactly once**:
   `btn.events("click")`. That is `btn`'s last use in `main`, so Perceus does
   *not* dup it -- ownership of the box moves straight through
   `events`/`add-listener`/`add-event-listener-raw` into `dom.c`'s
   `kk_wasiweb_dom_add_event_listener`, which drops it (`kk_box_drop`) right
   after forwarding the (now-unwrapped) externref to the `add-event-listener`
   host import. **`btn`'s slot is freed synchronously, before `main` even
   reaches its first `receive`.** (The actual `<button>` DOM node is of
   course *not* garbage collected -- it stays reachable through the live
   document tree and the JS-side event listener the host attached to it
   directly; this accounting is purely about the wasm-side table, which no
   longer needs to hold a reference once the listener is registered.)
3. `touch-tmp()` -- looks up `#tmp`, calls `set-inner-text` once, and
   returns. `tmp` is never referenced again, so Perceus drops it before
   `touch-tmp` returns -- freeing its slot **before `main` even calls
   `events`** (in program order `touch-tmp` runs after `events` registers the
   listener, but well before any suspension point, and certainly before
   index.html's verify hook ever runs).

So the baseline (after `main` runs to its first suspend, and after
`touch-tmp` has come and gone) is **exactly 1 live slot** -- `counter` alone.
This was confirmed empirically, not just reasoned about in the abstract: the
headless-Chrome transcript below reads `slots=1`, matching this analysis
(and *not* the naive "2, for counter+btn" guess one might make before
tracing through what `events` actually consumes). The point of the assertion
is `touch-tmp`'s slot going away: if Perceus's drop did *not* actually fire
`kk_js_obj_free_fun` (e.g. if the box merely went out of Koka-level scope
without kklib ever being told to release it), `live-slots` would read `2`
here instead of `1`, since `tmp`'s slot would still be marked allocated.

## Building

```
./build.sh
```
Requires: `WASI_SDK_PATH` (defaults to `~/wasi-sdk-34.0-rc.1-arm64-macos`),
and a `koka` built from this repo (`stack build`; the script falls back to
`stack exec koka --` if `koka` isn't on `PATH`). No `jco`, no `node` needed
for the build itself any more (only for optionally smoke-testing `run.mjs`,
which will throw once it reaches a `koka:dom` call since node has no
`document` -- this demo's primary leg is the browser).

This produces `./out/`, containing:
- `demo.wasm` -- the linked wasm32-wasip1 core module.
- `run.mjs`, `timers.js`, `vendor/browser_wasi_shim/` -- the compiler's own
  generic wasi-web runner package (see `src/Compile/CodeGen.hs`'s
  `wasiWebPostLink` and `support/wasi-web/`).
- `index.html` -- **this sample's own** (copied over the generic one by
  `build.sh`'s step 2), implementing `koka:dom` and the auto-verify hook.

## Verifying

Serve `./out` over http (ES modules + wasm need a real origin, not
`file://`):

```
npx serve ./out
# or: python3 -m http.server -d ./out 8080
```

Then open `http://localhost:<port>/index.html` in a browser -- you should
see a "click me" button and a counter that increments on click, and (thanks
to the auto-verify hook) the counter should already read `2` and the tab
title should read `counter=2;slots=1` on page load (two synthetic clicks
fired automatically, and the throwaway `#tmp` element's slot already
recycled by the time the title is set).

### Headless Chrome (used for this task's verification)

```
"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" \
  --headless=new --disable-gpu --virtual-time-budget=5000 \
  --dump-dom http://localhost:<port>/index.html | grep -o '<title>[^<]*</title>'
```
Expected and confirmed (two independent runs, no flake): `<title>counter=2;slots=1</title>`.
If headless Chrome is unavailable, `chromium`/`chrome-headless-shell` work
the same way.

### Browser support note

This demo requires wasm **reference types** (the `externref` type and
`table.get`/`table.set`/`table.grow` instructions) -- these have been
supported unconditionally (no flag, no opt-in) in every evergreen browser
engine (V8/Chrome, SpiderMonkey/Firefox, JavaScriptCore/Safari) and in
node >= 24 for years at this point; reference types are effectively
universal on any wasm host capable of running `--target=wasi-web` output at
all (which already requires a fairly current WASI/wasm toolchain). No
feature-detection or fallback path is needed.
