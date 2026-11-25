# OwnWindow: native out-of-window windows on the view model

Status: approved design (Tim, 2026-07-23). Prior art: the view/scene model
(lib/ui/view.kk, design ledger), the Plan A follow-up notes
(docs/superpowers/plans/2026-07-14-ui-overlays.md), the platform/render
thread split (ledger §6), the retention machinery (ledger §10).

## Goal

Realize `Window`-band views as REAL native windows (macOS first) without
changing the widget API: windows remain "just the top z-band" of the
everything-is-a-view scene model. Two chrome kinds from the start: titled
resizable windows (inspector/palette/second document) and borderless
non-activating panels that escape the main window's bounds (tooltips,
popovers). Web and wasi keep realizing everything in-window, unchanged.

## Decisions (with rationale)

1. **Lifecycle is declarative.** A window view emitted this frame is an
   open window; a key not emitted closes (destroys) its window. The native
   close button fires the view's existing `on-dismiss` message; the app
   updates its model and stops emitting. No handle API, no second
   lifecycle concept.

2. **A window is `scope(keep = Transient)` in essence.** Closing a window
   prunes its content's ephemeral state through the existing retention
   machinery -- nothing window-specific is retained (no cells, no
   position/size memory). An app that wants a reopened window to resume
   opts in with `keep = KeepAlive` on the content's key under a memo
   boundary (ledger §10); the window system adds NO retention of its own.

3. **One shared ImpellerContext, per-window CAMetalLayer + surface.**
   The SDK header is explicit (contexts are thread-safe, expensive,
   "create as few as possible -- typically just one -- and share");
   Flutter's desktop multi-window work has the same shape (one engine +
   rasterizer, per-window views managed by a window manager). Display
   lists are surface-independent.

4. **Uniform window table; main window is id 0.** No aux-window sidecar:
   the host.m singletons (window, layer, scale, cached metrics) become a
   table; `imp_host_init` creates entry 0 exactly as today. Every
   `imp_host_*` getter / present / inject gains a window id (shim.c and
   impeller.kk externs updated in lockstep).

5. **Render→main command ring.** Cocoa requires window create / destroy /
   retitle / reposition on the MAIN thread; the render thread owns the
   declarative decision. A mutex-guarded command ring (create, destroy,
   set-title, set-pos) + `glfwPostEmptyEvent` wakes the platform loop,
   which drains it. In embed (no-split) mode the same ring drains inline
   in `imp_host_poll` -- one code path. Window creation happens only via
   the ring between frames, never during init (keeps the #44 startup
   surface no wider than today). A view whose window is not up yet skips
   that frame's paint and catches the next one.

## API (lib/ui, portable)

```
// ui/view.kk
pub type chrome
  InLayer                          // today's realization: a layer in the parent window
  Titled( title : string, width : float64 = 480.0, height : float64 = 360.0 )
  Panel                            // borderless, non-activating, anchor-following

pub struct view<a>                 // changed fields only
  anchor : maybe<anchoring>        // WAS anchoring; see rules below
  chrome : chrome = InLayer

// sugar: a titled native window as a Window-band view, OS placement
pub fun window<a>( key : string, content : widget<a>, title : string,
                   width : float64 = 480.0, height : float64 = 360.0,
                   on-dismiss : maybe<a> = Nothing ) : scene<a> ()
```

Anchoring rules (validated at compose time, throwing with a clear message):
- `InLayer`: `anchor` defaults to `Just(Anchoring())` -- today's behavior.
- `Titled`: `anchor` must be `Nothing` (OS cascade placement; the window
  remembers its position while open, forgets it on close). `Just` THROWS
  ("titled-window anchoring not supported yet") -- the seam for later.
- `Panel`: `anchor` must be `Just` (throws on `Nothing`); the anchor rect
  resolves in SCREEN coordinates (parent window origin + region rect) and
  the panel is re-placed when either moves.

`overlay(...)` keeps its signature (chrome defaults to InLayer); it gains
`chrome : chrome = InLayer` and its `anchor` handling wraps in `Just`.

**InLayer size + position clamping (new, ships with this design):** an
InLayer view's content layout is capped at the window's size (effective
max-width/height = min(view cap, window w/h)), and the existing
`ui/anchor` place-clamp then shifts the view fully inside the window --
a view can never render larger than its window or be cut off by its edge.
(Today an oversized view makes the clamp range negative; the size cap
fixes that ordering.)

## Scene split (lib/ui/view.kk + backends)

`with-scene` stops flattening everything into one stack. It returns the
main composite (main widget + InLayer views, exactly today's `compose`)
PLUS the list of native-chrome views:

```
pub struct scene-out<a>
  main    : widget<a>
  windows : list<view<a>>          // chrome != InLayer, band order preserved
```

- Web backends: realize `windows` as InLayer (append to the stack) --
  a one-line degrade; no behavioral change on web/wasi.
- Impeller backend: each window view is its own widget tree -> own ltree ->
  own layout (against ITS window's size) -> own reconcile -> own display
  list -> `imp_host_present(win, dl)`. All trees are owned by the render
  thread (FBIP per window, single-threaded). `mounted` keeps a map
  view-key -> (window id, ltree, dl cache).
- Window diff per frame: emitted keys vs open windows -- create via the
  command ring (chrome params), destroy missing, retitle on change.

## Input and focus

- Event ring entries gain a window id (set by each window's GLFW
  callbacks). Pointer events hit-test ONLY the tagged window's ltree.
- One cursor: the single `hovered-key` / `pressed-key` stores are
  unchanged (the cursor is in one window at a time).
- Keyboard: the OS key window already routes char/key callbacks; they are
  tagged and drained against that window's tree. `focused-key` stays a
  single store.
- Native close request on a secondary window: enqueue the view's
  `on-dismiss` message (if `Nothing`, the close request is ignored -- the
  window stays until the app stops emitting it). Window 0's close remains
  app shutdown, as today.

## Host (host.m / shim.c / impeller.kk)

- `imp_win` table entry: GLFWwindow*, CAMetalLayer*, scale, cached w/h,
  chrome kind, alive flag. Id = table index; 0 = main.
- Panel realization: borderless GLFW window + Cocoa tweaks via
  `glfwGetCocoaWindow` (non-activating panel style mask, floating level,
  no focus steal, `GLFW_FOCUS_ON_SHOW=FALSE`).
- Panel placement: render thread computes the screen rect (parent origin
  from a window-pos callback cache + anchor rect) and sends set-pos
  commands when it changes.
- The existing single-window externs keep working during the refactor by
  becoming `(win = 0)` wrappers.

## Testing

- **Headless (ui/test):** the scene split is pure -- assert that emitting
  a `window(...)` yields a `scene-out` with the right windows list;
  tester `find`/`texts`/actions search main + window trees. A retention
  check: window content state dies on close (Transient default), survives
  under `keep = KeepAlive`.
- **Native smoke:** new `samples/ui/windows` (tear-off inspector +
  tooltip Panel escaping the bounds) in the suite's 30-frame smoke.
- **Live tier (folded in):** `test-inject-*` gain the window id; the
  tester resolves which window's tree contains a found key and injects
  window-local coordinates into that window's rings. Anything that does
  not make the MVP (e.g. asserting a Panel's absolute screen position)
  is documented at the top of ui/test-live.kk, not silently skipped.

## Deliberate cuts (MVP)

No per-window theme; no menus / fullscreen; no cross-window drag; no
position persistence across close (see decision 2); no web change; no
titled-window anchoring (throws; seam reserved); no per-window refresh
pacing (one frame clock paces all windows at the fastest display).

## Risks

- Task #44 (-O1 platform-split startup race) lives in this area: mitigated
  by creating windows only through the command ring between frames.
- Cocoa modal loops (window drag/resize of SECONDARY windows) block the
  platform loop, not the render thread -- same live-resize behavior as
  the main window under the split.
- GLFW panel behavior on macOS needs the Cocoa style-mask tweak to avoid
  focus stealing; if a true NSPanel proves necessary, the table entry
  isolates that change to host.m.
