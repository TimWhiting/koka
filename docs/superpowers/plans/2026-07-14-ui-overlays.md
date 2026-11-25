# Overlays & multi-view MVP — implementation plan

> Worktree agent brief. Branch off `clang-wasm`. Portable in-window overlays now;
> per-view tree-split seam so native out-of-window windows drop in later.

**Goal:** a correct, z-ordered, **not-parent-relative** overlay system (context
menus, dropdowns, modal dialogs, tooltips) that works identically on web + native,
with **zero** host.m/shim changes.

## Architecture

- An **overlay is composited at the ROOT of a view**, absolutely positioned and
  z-ordered by list order — never parent-relative (so it never clips to or
  inherits a deep parent's transform/scroll). Flutter parallel: `Overlay` +
  `OverlayEntry` high in the tree.
- `Stack` already lowers to `LFlex` (`lib/ui/widget.kk:340-346`) and both backends
  paint children in source order, later on top (native `impeller/backend.kk`
  `paint-at` LFlex fold; web positions each child absolutely, no z-index). So the
  overlay layer needs **no new node type and no backend change**.
- **Placement seam** for the future: each entry carries a placement (`InView` |
  `OwnWindow`). MVP realizes everything `InView`. `OwnWindow` (a real native
  window with its own view/ltree) is a documented follow-up; the widget API is
  unchanged, only the backend lowering differs.

## Files

- **Create `lib/ui/overlay.kk`** — the portable overlay layer.
- **Modify `lib/ui/style/default/components.kk`** — `context-menu`, `menu-item`,
  `dropdown` styled content.
- **Create `samples/ui/overlay/`** — `main.kk`, `build.kk`, `index.html`,
  `.gitignore` (copy an existing sample's).
- **Modify `util/test-wasi.sh`** — add `overlay` to the native smoke loop.

## API sketch (`lib/ui/overlay.kk`)

```koka
module ui/overlay
import ui/widget

// where an overlay is realized. MVP: InView only.
pub type placement
  InView          // clamp within the current view's bounds (web + native today)
  OwnWindow       // FOLLOW-UP: its own native window/view

// one floating layer over a view
pub struct overlay-entry<msg>
  content    : widget<msg>
  anchor     : (float64, float64)      // top-left target in view coords
  on-dismiss : maybe<msg> = Nothing    // fired by an outside (scrim) click
  dim        : bool = False            // translucent modal scrim beneath content
  placement  : placement = InView

// compose the main view with its overlays at the ROOT. Each entry becomes a
// full-view scrim (captures outside clicks -> on-dismiss; translucent if `dim`)
// plus the content positioned at `anchor`, clamped inside the view bounds.
pub fun with-overlays<msg>( main : widget<msg>, entries : list<overlay-entry<msg>> ) : widget<msg>

// convenience for a single popup at a point
pub fun popup<msg>( anchor : (float64,float64), content : widget<msg>,
                    on-dismiss : maybe<msg> = Nothing, dim : bool = False ) : widget<msg>
```

### Clamping to view bounds

`with-overlays` lowers to a `stack([ (0.0,0.0,main) ] ++ layers)`. The stack is
laid out with the view's full constraints, so the overlay content's size can be
measured and the anchor clamped so the popover stays on-screen. Because layout is
constraints-down, the simplest correct MVP: position content at `anchor`, and in
the backend-agnostic layout let the parent (the stack) place it; clamp `anchor.x`
to `[0, view_w - content_w]` and `.y` similarly. If measuring content width before
placing is awkward in one pass, clamp with a conservative min-margin and note
exact edge-flipping (flip above/left when it would overflow) as a follow-up.

### Scrim / dismiss

Each entry contributes, in order:
1. a full-view `box` (transparent, or `Fill(Color(0,0,0,0.4))` when `dim`) with
   `on-click = on-dismiss` (only if `on-dismiss` is `Just`) — captures outside
   clicks. An inner click on the content wins (content is a later sibling / on top
   and stops at its own handlers).
2. the `content` positioned at the clamped `anchor`.

## Open-state ownership (MVP)

Overlay open-state lives in the **app model** (an open dialog is app state,
Elm/Flutter-style). The app's view does:

```koka
fun view(m) = with-overlays( main-view(m), m.overlays )
```

Deep widgets open/close via **messages**; the anchor comes from `on-click-at`
(already delivers pointer coords as a typed message — ideal for context menus,
right-click, cursor-anchored poppers). No portal/hoist pass in the MVP.

## Styled menu components (`ui/style/default/components.kk`)

```koka
pub fun context-menu<msg>( items : list<(string, msg)> ) : theme widget<msg>
  // a surface box (theme.surface, rounded) holding a column of menu-items
pub fun menu-item<msg>( label : string, on : msg ) : theme widget<msg>
  // interactive() row: hover highlight, click -> on
pub fun dropdown<msg>( label : string, items : list<(string,msg)>, on-open : msg ) : theme widget<msg>
  // a button that emits on-open; the app opens a popup with context-menu(items)
```

Use the existing `interactive`/`box`/`column` + `theme`. Native shadow/rounded
polish (`DrawShadow`/`ClipRoundedRect`) is a follow-up (not blocking).

## Demo (`samples/ui/overlay/main.kk`)

An app whose model holds `overlays : list<overlay-entry<msg>>` (or a small variant
like `menu : maybe<(float64,float64)>` + `dialog-open : bool`). Show:
- Right-click (or a "context menu" button using `on-click-at`) opens a
  `context-menu` at the cursor; clicking an item dispatches and closes; clicking
  outside (scrim) closes.
- A `dropdown` that opens a menu.
- A "Open dialog" button → a modal dialog with `dim=True` scrim; a Close button or
  scrim click dismisses.

## Steps (TDD-ish; commit after each)

1. `lib/ui/overlay.kk`: `placement`, `overlay-entry`, `with-overlays`, `popup`.
   Compile-check against `lib/`. Verify `with-overlays(main, [])` == just `main`
   structurally (no scrim when no entries).
2. Styled `context-menu`/`menu-item`/`dropdown` in `ui/style/default`.
3. `samples/ui/overlay` (model-owned open state). Build jsweb; headless probe:
   open menu at a point → menu renders above content; click item → dispatched +
   closed; click scrim → closed; open dialog → scrim dims → close works.
4. Build native (`-- native`), 30-frame smoke. Add `overlay` to
   `util/test-wasi.sh` native loop.
5. Run full `util/test-wasi.sh` (node 24) — all green.

## Verification

- jsweb headless (CDP, like existing site probes): assert menu z-order (content
  paints over main), item click dispatches + dismisses, scrim click dismisses,
  modal dim renders.
- Native: builds + runs 30 frames.
- Full suite green; existing samples unaffected.

## Follow-ups (leave notes / TODOs, don't build)

- **Portal hoisting**: `Portal(content)` deep in the tree, collected pre-layout
  into a root overlay slot (Flutter `OverlayEntry.insert`). Ergonomic win.
- **Widget-rect anchoring** (Flutter `LayerLink`): anchor to a widget's laid-out
  rect via a keyed rect published during layout (like scroll metrics), read next
  frame; edge-flip placement.
- **Native `OwnWindow`**: host.m per-window refactor (singletons → per-window
  struct, shared `ImpellerContext`, per-window events/tree/pump, window handle
  across shim). Each window = its own view/ltree (FBIP per view). **Touches
  `impeller/backend.kk` + `app.kk` — coordinate with the threading plan.**
- Impeller `SaveLayer`/`ClipRoundedRect`/`ClipOval`/`DrawShadow` shim wiring for
  translucent/rounded/shadowed popovers.

## Coordination

MVP touches `lib/ui/overlay.kk`, `ui/style/default/components.kk`,
`samples/ui/overlay/*`, `util/test-wasi.sh` — **disjoint** from the threading
plan. Do NOT modify `app.kk` or `impeller/backend.kk` in the MVP (those are the
shared-hotspot files; the native-window follow-up would touch them later).
