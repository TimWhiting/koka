# lib/ui API audit — group related parameters/fields

The framework grew by adding individual parameters/fields as features landed.
Several now want grouping so signatures stay small and new options don't
proliferate a field across every tree match. Audit + refactor targets:

## Pointer input on `box` (DONE — landed with right-click)
`box` / `WBox` / `LBox` carry `onclick`, `onclickat`, `drag`, `ondrop` as
separate fields; right-click would add a fifth (`oncontextat`), and every `LBox`
match (~16 sites) grows a slot each time. **Group them into one `pointer<msg>`
struct** carried by `WBox`/`LBox`:

```koka
pub struct pointer<a>
  click      : maybe<a> = Nothing                        // left click
  click-at   : maybe<(float64,float64) -> a> = Nothing   // left click + position
  context-at : maybe<(float64,float64) -> a> = Nothing   // RIGHT click + position
  drag       : maybe<string> = Nothing                   // drag source payload
  drop       : maybe<string -> a> = Nothing              // drop target
```

`box()` KEEPS additive convenience params (`on-click=`, `on-click-at=`,
`on-context-at=`, `drag=`, `on-drop=`) and bundles them into `Pointer(...)`, so
no caller breaks. Then `LBox` has ONE handler field; adding future events
(double-click, middle-click, hover-enter/leave, wheel) is a struct field, not a
tree-wide change. This was the enabler for right-click (contextmenu / GLFW right
button -> `pointer.context-at`).

**Landed:** `pointer<a>` is defined in `widget.kk`; `WBox`/`LBox` carry a single
`on : pointer<a>`; `box()` bundles the flat params. Right-click flows through
`hit-context` (a new tree walk mirroring `hit-drop`): native emits pointer kind 3
on `GLFW_MOUSE_BUTTON_RIGHT` (`host.m` + `drain-pointers`); web subscribes a root
`contextmenu` listener and the dom host `preventDefault`s the browser menu. The
overlay sample's context menu is now right-click-triggered; jsweb self-test green.

## Other grouping candidates (lower priority)
- `App-config` is fine, but window/render options may grow — keep an eye on it.
- Overlay `overlay(...)` has many params (target/aligns/offset/band/dim/
  on-dismiss/max-w/max-h); consider grouping anchoring (target + two aligns +
  offset) into an `anchoring` value the caller builds, and placement (band/dim/
  dismiss/max) separately.
- `font` is already a struct (good). `fill`/`color` fine.
- `positioned(...)` mirrors overlay's params — same grouping applies.

## Principle
When a widget accumulates >3 related optional parameters that also become tree
fields, group them into a value struct with defaulted fields; keep flat
convenience params on the constructor function only (they bundle into the
struct), so callers stay terse and the tree stays narrow.
