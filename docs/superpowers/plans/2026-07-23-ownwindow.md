# OwnWindow (native multi-window) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Realize `Window`-band views as real native windows (titled + borderless panels) on macOS, per the approved spec `docs/superpowers/specs/2026-07-23-ownwindow-design.md`, without changing the widget API.

**Architecture:** The scene split (`scene-out` = main composite + native-chrome views) happens in `ui/view`; the impeller backend diffs emitted window views against a uniform host window table (main = id 0) and renders one ltree per window; window create/destroy marshals to the main thread over a command ring. Web backends flatten windows back to layers.

**Tech Stack:** Koka (lib/ui), Objective-C (host.m: GLFW + CAMetalLayer + Cocoa), C shim (shim.c), Impeller SDK.

## Global Constraints (from the spec — every task inherits these)

- One shared `ImpellerContext`; per-window `CAMetalLayer` + surface. Never a second context.
- Main window is table id 0, created by `imp_host_init` exactly as today.
- Window create/destroy/retitle/reposition happen ONLY on the main thread, ONLY via the command ring, NEVER during init.
- Lifecycle is declarative: emitted view = open window; not emitted = destroyed. Close button fires the view's `on-dismiss` (or is ignored when `Nothing`). Window 0 close = app shutdown, as today.
- No window-system state retention (a window is `scope(keep = Transient)` in essence). No position persistence across close.
- Anchoring rules: `InLayer` ⇒ `anchor` defaults `Just(Anchoring())`; `Titled` ⇒ `anchor` must be `Nothing` (throw `"titled-window anchoring is not supported yet (pass no anchoring)"` on `Just`); `Panel` ⇒ `anchor` must be `Just` (throw `"a Panel view needs an anchoring"` on `Nothing`).
- Web/wasi behavior unchanged: chrome degrades to `InLayer`.
- Every task ends with the repo's suite green for the parts it touches; native samples smoke via `KOKA_IMP_FRAMES=30`.
- Koka gotchas that WILL bite: multi-line lambdas in parens don't parse (use named local funs); inner annotations can't name outer fn type vars; `ctx` and `use` and `raw` are reserved words; local per-directory `.koka` caches go stale (clear the LOCAL one); koka does not rebuild when only `.c`/`.m`/`.h` change — pass `-r` or delete the cached object.

## File Map

| File | Responsibility in this plan |
|---|---|
| `lib/ui/view.kk` | `chrome` type, `view.anchor : maybe<anchoring>`, `window()` sugar, validation, `scene-out`, `with-scene` split |
| `lib/ui/widget.kk` | Positioned oversize hardening (clamp edge case) |
| `lib/ui/anchor.kk` | `clamp1` lo>hi guard |
| `lib/ui/app.kk` | `composed` produces `scene-out`; passes it to mount/render |
| `lib/ui/api/web/backend.kk` | accept `scene-out`, flatten windows to layers |
| `lib/ui/api/impeller/backend.kk` | per-window mounts, window diff, per-window pump routing, present |
| `lib/ui/api/impeller/impeller.kk` | window-id externs + open/close/set-pos/set-title + event win getters |
| `lib/ui/api/impeller/shim.c` | C wrappers for the above |
| `lib/ui/api/impeller/host.m` | window table, command ring, Panel chrome, tagged rings |
| `lib/ui/test.kk` | tester walks main + window trees |
| `lib/ui/test-live.kk` | per-window injection routing + documented cuts |
| `test/ui/windows.kk` | headless scene-split + retention-on-close tests |
| `samples/ui/windows/` | native demo (inspector + panel tooltip) |
| `util/test-wasi.sh` | picks up test + sample automatically (glob / sample list edit) |

Tasks 1–3 are pure Koka and independently green. Tasks 4–6 are host-side and each keeps single-window behavior working. Tasks 7–9 tie backend, tests, demo together.

---

### Task 1: `chrome` + `maybe<anchoring>` + `window()` + `scene-out` (portable model)

**Files:**
- Modify: `lib/ui/view.kk` (view struct ~line 52, `overlay` ~line 71, `with-scene` ~line 171)
- Modify: `lib/ui/app.kk:95-96,131-132` (`composed`)
- Modify: `lib/ui/api/web/backend.kk` (mount/render signatures)
- Modify: `lib/ui/api/impeller/backend.kk:103,112` (mount/render signatures — flatten for now, real multi-window in Task 7)
- Modify: `lib/ui/test.kk` (its internal mount/render path + `composed`)
- Test: `test/ui/windows.kk` (new)

**Interfaces (produces):**
```koka
pub type chrome
  InLayer
  Titled( title : string, width : float64 = 480.0, height : float64 = 360.0 )
  Panel

pub struct view<a>            // changed/added fields
  anchor : maybe<anchoring> = Nothing   // Nothing = InLayer default / Titled OS placement
  chrome : chrome = InLayer

pub fun window<a>( key : string, content : widget<a>, title : string,
                   width : float64 = 480.0, height : float64 = 360.0,
                   on-dismiss : maybe<a> = Nothing ) : scene<a> ()

pub struct scene-out<a>
  main    : widget<a>
  windows : list<view<a>>     // chrome != InLayer, band order preserved

// with-scene now RETURNS scene-out; `flatten` realizes windows as layers
pub fun with-scene<a,e>( action, scrollbar = neutral-scrollbar ) : <uistate,ioc|e> scene-out<a>
pub fun scene-out/flatten<a>( s : scene-out<a>,
                              rect-of : (string) -> maybe<(float64,float64,float64,float64)> ) : widget<a>
```

- [ ] **Step 1: Write the failing headless test** — `test/ui/windows.kk`:

```koka
// Scene split: window()/Panel views leave the main composite; InLayer stays in.
module windows

import std/async
import std/num/float64
import ui/widget
import ui/state
import ui/view
import ui/style/default
import ui/test

pub struct model( show-inspector : bool = False )
pub type msg
  ToggleInspector
  CloseInspector

pub fun themed-view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc,theme> widget<msg>
  if m.show-inspector then
    window("inspector", column([ keyed("insp-body", text("inspector body", 13.0, theme.fg)) ]),
           title = "Inspector", on-dismiss = Just(CloseInspector))
  overlay("hint", text("layer hint", 13.0, theme.fg))   // InLayer: stays composited
  column([
    keyed("toggle", primary-button("Inspect", ToggleInspector)),
    keyed("main-body", text("main body", 13.0, theme.fg)),
  ], gap = 8.0)

pub fun view( m : model, key : key ) : <keytree,uistate,scene<msg>,ioc> widget<msg>
  with val theme = dark
  box( themed-view(m, key), padding = 12.0 )

pub fun update( m : model, msg : msg ) : dispatch<msg> model
  match msg
    ToggleInspector -> m(show-inspector = True)
    CloseInspector  -> m(show-inspector = False)

pub fun split-scenario( t : tester<msg> ) : <async,uistate,uicheck,ioc,exn> ()
  check-eq("no window content before toggle", t.texts("insp-body"), [])
  check-eq("layer content composites", t.texts("hint").length, 1)
  t.click("toggle")
  t.settle()
  check-eq("window content reachable after toggle", t.texts("insp-body"), ["inspector body"])
  check-eq("main still reachable", t.texts("main-body"), ["main body"])

pub fun main()
  test-scenarios("native windows (headless)", Model(), view, update,
                 [("split", split-scenario)])
```

- [ ] **Step 2: Run it, verify it fails** — `stack exec koka -- -v0 --console=raw -ilib -itest/ui -e test/ui/windows.kk`. Expected: type error (`window` not defined).

- [ ] **Step 3: Implement `lib/ui/view.kk`.** Add after the `anchoring` struct:

```koka
// how the backend realizes a view: an in-window layer (today), a real titled
// resizable window, or a borderless non-activating panel that escapes the
// parent window's bounds. Web backends realize everything InLayer.
pub type chrome
  InLayer
  Titled( title : string, width : float64 = 480.0, height : float64 = 360.0 )
  Panel
```

Change the `view` struct fields `anchor : anchoring = Anchoring()` to `anchor : maybe<anchoring> = Nothing` and add `chrome : chrome = InLayer`. `overlay` keeps its parameters and wraps: `View(key, content, Just(Anchoring(target, target-align, self-align, offset-x, offset-y)), band, dim, on-dismiss, max-width, max-height, chrome)` — add a `chrome : chrome = InLayer` parameter at the end of `overlay`'s parameter list. Add the sugar + validation:

```koka
// a titled native window as a Window-band view: OS placement (no anchoring),
// declarative lifecycle (emit = open; stop = close; close button -> on-dismiss)
pub fun window<a>( key : string, content : widget<a>, title : string,
                   width : float64 = 480.0, height : float64 = 360.0,
                   on-dismiss : maybe<a> = Nothing ) : scene<a> ()
  emit-view( View(key, content, Nothing, Window, False, on-dismiss,
                  unbounded-w, unbounded-w, Titled(title, width, height)) )

// anchoring rules per chrome (validated when the scene is composed)
fun check-chrome<a>( v : view<a> ) : exn view<a>
  match v.chrome
    Titled -> match v.anchor
      Just(_) -> throw("view '" ++ v.key ++ "': titled-window anchoring is not supported yet (pass no anchoring)")
      Nothing -> v
    Panel -> match v.anchor
      Nothing -> throw("view '" ++ v.key ++ "': a Panel view needs an anchoring")
      Just(_) -> v
    InLayer -> v
```

In `view/layers`, read the anchoring with `v.anchor.default(Anchoring())` (InLayer default restores today's behavior). Change `with-scene` to return `scene-out`:

```koka
pub struct scene-out<a>
  main    : widget<a>
  windows : list<view<a>>

pub fun with-scene<a,e>( action : () -> <scene<a>,uistate,ioc|e> widget<a>,
                         scrollbar : (scroll-info, scroll-axis) -> <uistate,ioc|e> widget<a> = neutral-scrollbar ) : <uistate,ioc,exn|e> scene-out<a>
  // ... identical body through `autobars` ...
  val checked = views.map(check-chrome)
  val (native, layers) = checked.partition(fn(v) !v.chrome.is-in-layer)
  Scene-out( compose(main, layers ++ autobars, rect-of), native )

// realize native-chrome views as in-window layers (web / degrade path)
pub fun scene-out/flatten<a>( s : scene-out<a>,
                              rect-of : (string) -> maybe<(float64,float64,float64,float64)> ) : widget<a>
  match s.windows
    Nil -> s.main
    ws  -> compose(s.main, ws.map(fn(v) v(chrome = InLayer, anchor = Just(v.anchor.default(Anchoring())))), rect-of)
```

Note `with-scene` gains `exn` (the validation throws); `ioc` admits `exn` at every existing call site (`composed` in app.kk / test.kk), so only signatures that SPELL the row need edits. Add `fun chrome/is-in-layer( c : chrome ) : bool` by matching (auto `is-` names are unreliable across ctor casing).

- [ ] **Step 4: Update the consumers mechanically.** `ui/app.kk` `composed` (both run-single and run-threaded) and `ui/test.kk`'s equivalent now produce `scene-out`; backends' `mount`/`render` accept it. For this task, ALL THREE backends flatten immediately — impeller `mount`/`render` first line: `val w = s.flatten(rect-of-snapshot())` where `rect-of-snapshot()` is a small helper reading `all-anchor-rects()` like `with-scene` does; web backend identical. `ui/test.kk`'s harness keeps its own tree walk: walk `s.main` AND every `s.windows` content for `find`/`texts`/`dispatch-click` (windows are laid out with `with-test-measure` at the harness's fixed window size for hit purposes — a plain `stack` append via `flatten` is acceptable for the headless tier and keeps one walk).

- [ ] **Step 5: Run the new test AND the existing headless suite** — expected: `windows.kk` passes (window content reachable via the flattened walk), `basic.kk` + `retain.kk` unchanged.

Run: `for t in test/ui/*.kk; do stack exec koka -- -v0 --console=raw -itest/ui -e $t; done`

- [ ] **Step 6: Web + native sample smoke** — `cd samples/ui/counter && stack exec koka -- -v0 --console=raw -e build.kk -- native && KOKA_IMP_FRAMES=30 ./app-native`; expected: builds, runs 30 frames, exit 0. Same for `samples/ui/overlay` (exercises InLayer views through the new `maybe<anchoring>` path).

- [ ] **Step 7: Commit** — `git add -A lib/ui test/ui && git commit -m "ui/view: chrome kinds + scene-out split (windows still flattened)"`

### Task 2: InLayer oversize hardening

**Files:**
- Modify: `lib/ui/anchor.kk:59-73` (`clamp1`, `place`)
- Test: extend `test/ui/windows.kk`

The Positioned layout (`lib/ui/widget.kk:538`) already caps child constraints at `vw.min(maxw)`/`vh.min(maxh)`; the remaining hole is a child with an intrinsic size larger than the viewport (e.g. a fixed `rect(2000,...)`): `clamp1(x, 0.0, vw - cw)` gets `hi < lo` and pins to a possibly-cut-off position.

- [ ] **Step 1: Failing test** — add to `test/ui/windows.kk` a scenario `oversize` with an InLayer overlay whose content is `rect(4000.0, 30.0)` and assert its laid-out x position is `0.0` (fully pinned left, not negative, not cut off at the right beyond viewport): use `t.find("big")` (wrap the rect in `keyed("big", ...)`) and `check("oversize pins to origin", rect.x == 0.0 && rect.y >= 0.0)`.
- [ ] **Step 2: Run — fails** (position negative or missing depending on clamp behavior).
- [ ] **Step 3: Fix `clamp1`** in `lib/ui/anchor.kk`:

```koka
pub fun clamp1( v : float64, lo : float64, hi : float64 ) : float64
  if hi < lo then lo else v.max(lo).min(hi)   // oversized content pins to the near edge
```

- [ ] **Step 4: Test passes; full headless suite green.**
- [ ] **Step 5: Commit** — `git commit -am "ui/anchor: pin oversized positioned content to the near edge"`

### Task 3: headless retention-on-close test (windows are Transient in essence)

**Files:** extend `test/ui/windows.kk` only. Windows' content state follows the EXISTING key/retention semantics — this task pins that with a test, no new code.

- [ ] **Step 1:** Add a `retention` scenario: the inspector window content holds `use-state` under `scope("insp", keep = KeepAlive)` for one field and a plain (Transient) `scope("scratch")` for another, both behind `memo` (mirror `test/ui/retain.kk`'s pane/bump structure — click targets `bump-keep` / `bump-scratch`, texts `val-keep` / `val-scratch`). Script: open window, bump both, close (emit `CloseInspector`), reopen; assert `val-keep` retained, `val-scratch` reset.
- [ ] **Step 2:** Run; if the Transient assert fails because nothing unmounts, the window content in the test app must sit under a `memo` boundary INSIDE the view (the boundary is the unit of retention — same as tabs). Fix the test app, not the library.
- [ ] **Step 3:** Suite green; commit — `git commit -am "test/ui: window content state follows key retention (Transient default)"`

### Task 4: host window table (behavior-preserving)

**Files:**
- Modify: `lib/ui/api/impeller/host.m` (whole-file refactor of the statics)
- Modify: `lib/ui/api/impeller/shim.c`, `lib/ui/api/impeller/impeller.kk` (lockstep)

**Interfaces (produces, C):**
```c
#define IMP_MAX_WINDOWS 16
typedef struct {
  GLFWwindow*   window;
  CAMetalLayer* layer;
  double        scale;
  volatile double win_w, win_h;     // cached logical size
  double        cursor_x, cursor_y; int cursor_seen;
  int           chrome;             // 0 titled/main, 1 panel
  volatile int  alive;
} imp_win;
static imp_win g_wins[IMP_MAX_WINDOWS];   // slot 0 = main
```
Every event-ring entry gains a window index: `g_pointer[IMP_MAX_EVENTS][4]` (kind, x, y, win), `g_chars`/`g_keys` become `struct { unsigned int v; int win; }` arrays, plus `int g_last_event_win` conventions below. All `imp_host_*` functions gain a leading `int win` parameter; `imp_host_init` fills slot 0.

- [ ] **Step 1:** Refactor host.m: replace `g_window/g_layer/g_scale/g_win_w/g_win_h/g_cursor_*` with `g_wins[win].*`. GLFW callbacks find their window's index via `glfwGetWindowUserPointer` (set to `(void*)(intptr_t)win` at creation) and stamp it into the ring entries. `imp_host_present(int win, ...)`, `imp_host_width(int win)`, etc. Functions that are genuinely global keep their signatures: rings' `imp_host_next_pointer` (returns kind) plus NEW `imp_host_pointer_win(void)` / `imp_host_char_win(void)` / `imp_host_key_win(void)` returning the win of the LAST drained entry; `imp_host_take_scroll_dx/dy` gain `int win` (per-window accumulators in `imp_win`... keep scroll global with a `g_scroll_win` tag: scroll targets the window under the cursor, one wheel at a time — global accumulator + tag is sufficient and simpler).
- [ ] **Step 2:** shim.c: every `kk_imp_*` wrapper that maps to a windowed host call gains `kk_integer win` first arg (pattern: `int w = kk_integer_clamp32(win, ctx);`). impeller.kk: each corresponding extern gains `win : int`; keep the EXISTING Koka function names as window-0 wrappers so `backend.kk` compiles untouched this task:

```koka
extern window-width-raw( win : int ) : ioc float64
  c "kk_imp_window_width"
pub fun window-width( win : int = 0 ) : ioc float64
  window-width-raw(win)
```

Apply the same pattern to: `window-height`, `content-scale`, `cursor-x`, `cursor-y`, `present`, `should-close`, `inject-*` (5), `take-scroll-dx/dy`. Add `pub extern pointer-win() : ioc int`, `char-win`, `key-win`, `scroll-win`.
- [ ] **Step 3:** Build + run three native samples 30 frames (`counter`, `overlay`, `threads` — remember `-r` or clear the local `.koka` since only C changed): behavior identical, exit 0.
- [ ] **Step 4:** Native live test tier: `./test/ui/live/build.sh && (cd test/ui/live && ./test-live)` — 7/7 (injection wrappers defaulting to window 0 must keep this green).
- [ ] **Step 5:** Commit — `git commit -am "impeller host: uniform window table (main = id 0), win-tagged event rings"`

### Task 5: command ring + titled window create/destroy

**Files:** `host.m`, `shim.c`, `impeller.kk` (same lockstep pattern as Task 4)

**Interfaces (produces, Koka):**
```koka
// allocate a table slot and enqueue creation on the main thread; returns the id
pub extern open-window( chrome : int, title : string, w : float64, h : float64 ) : ioc int
pub extern close-window( win : int ) : ioc ()
pub extern set-window-title( win : int, title : string ) : ioc ()
pub extern set-window-pos( win : int, x : float64, y : float64 ) : ioc ()
pub extern window-alive( win : int ) : ioc bool          // created AND not close-requested
pub extern window-close-requested( win : int ) : ioc bool // user hit the close button (sticky until close-window)
pub extern main-window-origin() : ioc (float64, float64)  // screen coords, for Panel placement (Task 6)
```

- [ ] **Step 1:** host.m command ring:

```c
typedef struct { int op; int win; int chrome; char title[128]; double x, y, w, h; } imp_cmd;
#define IMP_OP_CREATE 1
#define IMP_OP_DESTROY 2
#define IMP_OP_SET_TITLE 3
#define IMP_OP_SET_POS 4
static imp_cmd g_cmds[64]; static int g_cmd_head = 0, g_cmd_count = 0;
static pthread_mutex_t g_cmd_mutex = PTHREAD_MUTEX_INITIALIZER;
```

`imp_host_open_window` (callable from the render thread): find a free slot (alive == 0 && window == NULL), mark it pending, enqueue `IMP_OP_CREATE`, `glfwPostEmptyEvent()`, return the slot. `imp_host_drain_commands(void)` runs ON MAIN: create the GLFW window (`GLFW_VISIBLE` true, decorated for chrome 0), attach a `CAMetalLayer` exactly as `imp_host_init` does for the main window (extract the layer-attach code into `static void imp_attach_layer(imp_win* iw)` shared by both), install ALL the same callbacks with the slot in the user pointer, set `alive = 1`. DESTROY: `glfwDestroyWindow`, clear the slot. Call `imp_host_drain_commands()` from (a) the platform loop right after `glfwWaitEvents` returns, and (b) `imp_host_poll` (embed mode) — one code path, two drain sites.
- [ ] **Step 2:** close semantics: the per-window GLFW close callback sets `close_requested = 1` and CANCELS the close for win != 0 (`glfwSetWindowShouldClose(w, GLFW_FALSE)`) — the app decides by no longer emitting the view; window 0 keeps today's behavior (app shutdown).
- [ ] **Step 3:** smoke WITHOUT backend involvement — temporary probe at the end of `samples/ui/threads/main.kk`? NO (keep samples clean): write `test/ui/live/winprobe.kk` (native-only, built ad hoc, NOT suite-wired):

```koka
// probe: open a titled window from the render side, verify it comes alive, close it
module winprobe
import std/async
import ui/api/impeller/impeller
pub fun main()
  init("winprobe", 320, 200)
  val w = open-window(0, "probe", 240.0, 160.0)
  var tries := 0
  while { !window-alive(w) && tries < 100 }
    poll-events()
    tries := tries + 1
  println(if window-alive(w) then "alive" else "DEAD")
  close-window(w)
  poll-events()
  println(if window-alive(w) then "STILL-ALIVE" else "closed")
```
Run embed-mode (no split in a bare probe): expected output `alive` / `closed`.
- [ ] **Step 4:** all Task-4 smokes still green. Commit — `git commit -am "impeller host: render->main command ring; titled windows open/close"`

### Task 6: Panel chrome

**Files:** `host.m` only (creation branch in `imp_host_drain_commands`).

- [ ] **Step 1:** chrome 1 creation: `glfwWindowHint(GLFW_DECORATED, GLFW_FALSE); glfwWindowHint(GLFW_FOCUS_ON_SHOW, GLFW_FALSE); glfwWindowHint(GLFW_FLOATING, GLFW_TRUE);` then post-create Cocoa tweaks:

```c
#import <GLFW/glfw3native.h>   // GLFW_EXPOSE_NATIVE_COCOA at top of host.m (already exposed for the layer)
NSWindow* ns = glfwGetCocoaWindow(iw->window);
[ns setLevel:NSFloatingWindowLevel];
[ns setStyleMask:[ns styleMask] | NSWindowStyleMaskNonactivatingPanel];  // if the cast is rejected at runtime, fall back to: never call makeKey; GLFW_FOCUS_ON_SHOW already prevents steal
[ns setHidesOnDeactivate:NO];
```
Note: `NSWindowStyleMaskNonactivatingPanel` is formally an `NSPanel` mask; if setting it on an `NSWindow` misbehaves (assert/appearance glitch), drop that line — floating + no-focus-on-show covers the MVP need. Document whichever lands in a comment.
- [ ] **Step 2:** `imp_host_set_window_pos` (via ring, `glfwSetWindowPos` — GLFW screen coords are points on macOS, matching `main-window-origin` from `glfwGetWindowPos(g_wins[0].window)` cached by a window-pos callback into `volatile double g_main_x, g_main_y` so the render thread can read it without a main-thread call).
- [ ] **Step 3:** extend `winprobe.kk`: open a chrome-1 panel at (100,100), assert alive, close. Run: `alive`/`closed`.
- [ ] **Step 4:** Commit — `git commit -am "impeller host: Panel chrome (borderless, floating, no focus steal)"`

### Task 7: impeller backend — real multi-window render, pump routing, dismiss

**Files:**
- Modify: `lib/ui/api/impeller/backend.kk` (the heart: mounted struct, mount/render, present, pump/drains)

**Interfaces (consumes):** Task 1's `scene-out`, Task 5/6's externs. **Produces:** none new (backend-internal).

- [ ] **Step 1:** per-window mount record + registry (module-level, mirroring `dl-entry` style):

```koka
struct win-mount<a>
  vkey    : string                      // the view's key (identity of the window)
  win     : int                         // host table id
  tree    : ref<global, ltree<a>>
  dlcache : ref<global, int32-map<dl-entry>>
  dismiss : maybe<a>
```
`mounted<a>` gains `wins : ref<global, list<win-mount<a>>>`.
- [ ] **Step 2:** `render(m, s : scene-out<msg>)`:
  1. main tree: today's body against `s.main`.
  2. diff: for each `v` in `s.windows` not in `!m.wins` → `open-window(chrome-code(v.chrome), title/size from `Titled` or anchor-derived for `Panel`)`, fresh `win-mount` with an empty tree; for each `wm` in `!m.wins` whose `vkey` is not emitted → `close-window(wm.win)`, drop the record (state pruning is the app's retention concern, not the backend's).
  3. per window alive: reconcile `v.content` at `tight(window-width(wm.win), window-height(wm.win))` (same take-tree/re-laid discipline as main; each window's tree ref is its own unique owner), `bake-scroll`, present via a `present-win(wm)` variant of `present-tree` that ends with `present(dl, win = wm.win)`. Not alive yet → skip this frame (spec: catches the next one).
  4. Panel placement: compute screen rect = `main-window-origin() + anchor rect` (resolve `v.anchor.default(...)` against `all-anchor-rects()` exactly as `view/layers` does) and `set-window-pos(wm.win, sx, sy)` when it changed (cache last pos in the win-mount as two more fields `px, py : ref` or store `(float64,float64)` in a ref).
- [ ] **Step 3:** pump routing: after each ring drain, read the event's window (`pointer-win()` etc.); resolve the tree: `fun tree-for(m, win)` returns main tree for 0 else the matching `win-mount`'s. Hover uses the CURSOR's window (`cursor-x(w)/cursor-y(w)` of the window that last saw the cursor — add `g_cursor_win` in host.m stamped by the cursor callback, exposed as `cursor-win()`; do this in Task 4 if preferred). `drain-pointers`/`drain-scroll`/`drain-text` take the resolved tree instead of `!m.tree` (mechanical: they already read the tree once per call).
- [ ] **Step 4:** dismiss: in the pump's iteration, for each `wm` where `window-close-requested(wm.win)`: `match wm.dismiss { Just(msg) -> (m.emit)(msg); Nothing -> () }` (the sticky flag + declarative diff make this idempotent — the app stops emitting and step 2 destroys).
- [ ] **Step 5:** headless suite still green (backend untouched by headless); native live tier 7/7; three-sample smoke green.
- [ ] **Step 6:** Commit — `git commit -am "ui/impeller: multi-window render + input routing + declarative dismiss"`

### Task 8: live-tier per-window injection + documentation

**Files:**
- Modify: `lib/ui/api/impeller/backend.kk` (test-inject surface), `lib/ui/api/impeller/impeller.kk` (already win-parameterized from Task 4)
- Modify: `lib/ui/test-live.kk` (routing + header doc)
- Modify: `lib/ui/test.kk` (tester `find` returns which tree/window a key was found in — extend the internal anchor walk result with a window ordinal; the public tester API is UNCHANGED)

- [ ] **Step 1:** `test-inject-*` gain `win : int = 0` parameters passing through to the injectors. `live-tree()` in test-live returns main + window trees (the backend registers the erased scene as `(main, [(vkey, tree)])` — change `set-live-scene` payload to carry the window trees too, erased as a list).
- [ ] **Step 2:** tester routing: `find`/`click`/etc. search main first, then window trees in order; a hit in window k injects with that window's id and window-local coordinates (the walk already yields tree-local coords — window trees ARE window-local, so no translation is needed beyond passing the right win).
- [ ] **Step 3:** Document at the top of `lib/ui/test-live.kk`: what IS covered (event injection into any window by key; dismiss via close-request is NOT injectable — GLFW has no synthetic close, so dismiss paths are tested headless; Panel screen-position is asserted only as "alive", not geometry).
- [ ] **Step 4:** Extend `test/ui/live/main.kk`'s scenario list with a `windows` scenario (native only — gate `if test-backend == "impeller"`) reusing `test/ui/windows.kk`'s app: toggle inspector, assert `insp-body` text via the window tree, click `bump-keep` INSIDE the window, close+reopen via messages, assert retention. Run native live: expected all checks pass.
- [ ] **Step 5:** Commit — `git commit -am "ui/test-live: per-window injection; windows scenario on the native live tier"`

### Task 9: demo sample + suite wiring + ledger

**Files:**
- Create: `samples/ui/windows/main.kk`, `samples/ui/windows/build.kk` (copy `samples/ui/threads/build.kk` verbatim — it is target-generic), `samples/ui/windows/.gitignore` (`app-native`, `out*/`, `.koka/`)
- Modify: `util/test-wasi.sh:386` (add `windows` to the native smoke sample list)
- Modify: `docs/ui/design-notes.md` (ledger entry 11), `docs/ui/paper-outline.md` (move OwnWindow off the designed-only list)

- [ ] **Step 1:** demo app: a main window with (a) an "Open inspector" button → `window("inspector", ...)` showing live model state + its own bump button (proves cross-window messaging), close button wired `on-dismiss`; (b) a hover-armed tooltip as a `Panel` anchored to a `keyed` region (`overlay("tip", ..., chrome = Panel, target = Region("tip-anchor"), target-align = bottom-left)`) — moving the main window drags the panel along (Task 7 placement).
- [ ] **Step 2:** `KOKA_IMP_FRAMES=60 ./app-native` exits 0; manual eyeball note in the sample readme (tear-off + tooltip escaping the bounds).
- [ ] **Step 3:** add to the suite's native sample list; run `./util/test-wasi.sh`; expected all green (known kklib first-run flakes excepted).
- [ ] **Step 4:** ledger entry 11 (what landed, decisions, parked items: titled anchoring throw, no synthetic close in live tier, IMP_MAX_WINDOWS=16) + paper outline claims-ledger row (`OwnWindow: implemented + smoke/live-tested`).
- [ ] **Step 5:** Commit — `git commit -am "samples/ui/windows + suite wiring + ledger: native multi-window lands"`

---

## Self-review notes

- Spec coverage: chrome kinds (T1/T5/T6), anchoring rules incl. throws (T1), InLayer clamp (T2), Transient-in-essence (T3), table+id0 (T4), command ring + drain sites (T5), Panel Cocoa specifics + placement (T6), scene split + per-window trees + dismiss + input routing (T7 with T1), live-tier folding + documented cuts (T8), sample/suite/ledger (T9), web degrade (T1 flatten). Web/wasi unchanged: verified by T1 step 6 + suite.
- The one intentionally-deferred spec line: "windows list, band order preserved" — `partition` preserves emission order; bands only matter for InLayer stacking, which `flatten` re-applies via `compose`.
- Type consistency: `scene-out` fields `main`/`windows` used identically in T1/T7/T8; `win-mount.vkey` naming consistent in T7/T8; extern names of T5 match T7's calls (`open-window`, `close-window`, `set-window-pos`, `window-alive`, `window-close-requested`, `main-window-origin`).
