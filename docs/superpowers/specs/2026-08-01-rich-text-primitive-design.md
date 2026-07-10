# Rich text primitive (`rich`) — design

## Motivation

`ui/widget`'s `Text`/`Paragraph` render one string in one font and one
color. That's been enough for the docs site until now, but two real needs
have hit the ceiling of what a single-run string can do:

1. **Inline code spans in prose.** Markdown-style `` `code` `` spans inside
   a sentence should render in the mono font, distinct from the sentence
   around them. Today `prose` just strips the backtick characters
   (`samples/ui/site/blocks.kk`) because there's no way to switch fonts
   mid-paragraph — the words survive, but the visual distinction doesn't.
2. **Syntax highlighting in code samples.** Every `code-block` line is one
   flat color today. Real syntax highlighting needs per-token color
   (keywords, strings, identifiers, comments) within what is still visually
   one line of code.

Both need the same underlying capability: one piece of text, several
sub-ranges independently styled, wrapping and flowing as a single unit.
This spec adds that capability — a new core `ui/widget` primitive, `rich`
— and wires it into `prose` for inline code spans. Syntax highlighting is
an explicit follow-up (it additionally needs a Koka tokenizer, a separable
piece of work) once `rich` exists and is proven.

## Goals

- A `rich` widget: one base string, a base font/color, and a list of
  **spans** — `(start, end, font-override, color-override, on-click)` —
  layered over sub-ranges of that string.
- Both backends flow/wrap spans as ONE paragraph, matching how `Paragraph`
  wraps today, not a row of independently-wrapped fragments.
- A span can optionally carry a click message, and this must work even
  when the span's line wraps (a click on the wrapped continuation of a
  multi-line span still resolves to that span's message).
- `prose` parses `` `backtick` `` spans and renders them via `rich` with a
  mono font override, replacing the current backtick-stripping.

## Non-goals (this round)

- **Syntax highlighting itself.** This spec lands the primitive `rich` is
  built on; a Koka tokenizer + color scheme for `code-block` is a separate
  follow-up design.
- **Inline widget spans** (Flutter's `WidgetSpan` — embedding an arbitrary
  widget, not just styled text, inline in the flow). Neither current use
  case needs it. The span data model is a record now, not a closed sum
  type, specifically so a `WidgetSpan`-shaped variant could be added later
  without reshaping this API — but the placeholder-reservation/positioning
  machinery it would need is not built this round.
- **Rich text editing.** `rich` is display-only, like `Text`/`Paragraph`
  today; it is not a `field`/`text-input` variant.

## Known limitations

- **wasi-web spans are not clickable.** The wasi-web host (`lib/web-ui/api/wasiweb/dom.kk`'s
  `measure-rich-box`) has no "koka:dom" host import for per-span DOM
  measurement (jsweb gets one; native/impeller has its own real
  implementation). It composes `rich` measurement out of the
  text-measurement imports that already exist, and reports **zero rects**
  for every span, so on wasi-web specifically `rich` renders and measures
  base text correctly but a span's `on-click` is silently inert — clicks
  never resolve to a span there. Fixing this for real needs a new host
  import (both a Koka extern and the corresponding `support/wasi-web/*.js`
  implementation), which is real scope beyond this round; the docs site
  does ship a `build-wasi-web` target (`lib/web-ui/project.kk`), so this is
  a real, currently-shipping gap, not a hypothetical one.
- **wasi-web height can be under-measured for oversized spans.** The same
  fallback measures total height by reflowing `content` in the BASE font
  only, while paint renders each span in its own font. A span set in a
  font taller than the surrounding base text can therefore get a
  under-reported container height, risking that span's content being
  clipped by the container's `overflow:hidden`. Same fix path as above (a
  real per-span host import), same out-of-scope status this round.

## Data model (`ui/widget`)

```koka
pub struct text-span<a>
  start    : int                    // grapheme offset into `content`, inclusive
  end      : int                    // exclusive
  font     : maybe<font> = Nothing  // Nothing = inherit the base font
  color    : maybe<color> = Nothing // Nothing = inherit the base color
  on-click : maybe<a> = Nothing     // Nothing = not clickable
```

New widget variant, parallel to `Text`:

```koka
Rich( owner : int32, content : string, base-font : font, base-color : color,
      spans : list<text-span<a>>, wrap : bool )
```

with a constructor `pub fun rich<a>( content : string, size : float64 = 15.0,
color : color = default-fg, spans : list<text-span<a>> = [], wrap : bool =
True, ?key : key ) : widget<a>` mirroring `paragraph`'s defaults (a `font/rich`
overload taking an explicit base `font` follows the existing `size/text` /
`font/text` overload pattern).

Spans index by **grapheme offset** into `content` (the same convention
`count`/`pad-right` already use elsewhere in this codebase), not byte
offset — extracted via `sslice` the way existing string helpers do.
Overlapping spans are undefined behavior for this version (callers are
expected to produce non-overlapping ranges; a tokenizer naturally does).
Color is a pure paint-time attribute and does not affect wrap geometry, so
only `font` overrides participate in measurement.

## Layout: extending the `measure` effect

```koka
pub effect measure
  fun measure-text( content : string, font : font, max-w : float64 ) : (float64, float64)
  fun measure-rich( content : string, base-font : font,
                     font-spans : list<(int, int, font)>,   // color-less: color doesn't affect geometry
                     max-w : float64, wrap : bool )
    : (float64, float64, list<list<(float64,float64,float64,float64)>>)
```

`measure-rich` returns the total `(w, h)` (same shape `measure-text`
returns) **plus** a per-span list of rects — usually one rect, more than
one if that span's text wraps across a line break. This is the geometry
that makes "clickable while wrapped" possible: hit-testing checks a click
point against each span's rect list directly, rather than re-deriving line
breaks itself.

`layout` gains an `Rich` case building `LRich` the same way `Text` builds
`LText` — storing `content`, `base-font`, `base-color`, `spans`, `wrap`,
the resolved `(w, h)`, and the resolved per-span rects (relative to the
node's own origin, the same convention every other `ltree` node's stored
geometry already uses).

## Native (Impeller) implementation

The existing `paragraph`/`draw-paragraph` wrapper
(`lib/ui/api/impeller/impeller.kk`, `shim.c`) builds one style, adds one
text run, and builds. Impeller's underlying `ImpellerParagraphBuilder`
already supports calling `PushStyle`/`AddText`/`PopStyle` repeatedly before
`Build` — that's the SDK's own multi-run mechanism (confirmed in
`lib/ui/api/impeller/sdk/include/impeller.h`). Rather than marshal a whole
span list across the FFI boundary in one call, this exposes that
incremental API directly as a handful of thin externs — `rich-begin`,
`rich-push-style`, `rich-add-text`, `rich-pop-style`, `rich-build` — and
the Koka side drives them with an ordinary fold over `spans`, filling the
gaps between spans with the base style. No new list-marshaling machinery
is needed.

Hit-testing and per-span rects use two SDK functions already present and
unused in this codebase:
`ImpellerParagraphCreateGlyphInfoAtParagraphCoordinatesNew` (point → glyph,
for resolving a click) and `ImpellerParagraphCreateGlyphInfoAtCodeUnitIndexNew`
plus `ImpellerGlyphInfoGetGraphemeClusterBounds` (character index → bounds,
for resolving a span's rect(s) during measurement — called once per span
boundary to bracket its extent, including across a wrap).

## Web implementation

Paint emits one wrapping `<div>` (the same `white-space:normal` flow
`LText`'s `wrap = True` case already uses) containing one `<span>` per
text-span, each with its own inline `font`/`color` style; the browser's
own reflow wraps them together as it already does for any inline HTML
content — no custom wrap logic needed for painting. A span with
`on-click = Just(msg)` gets the same click-listener wiring any other
clickable node already gets in `node-html`.

Layout still needs a real `(w, h)` number up front (Koka's layout model
positions siblings before paint runs), so `measure-rich` gets a JS extern
mirroring `measure-text-box-height`: build the same hidden multi-span
structure off-screen, force a layout, and read back the container's size
plus each span's `getClientRects()` (which already gives per-line rects
for free when a span wraps — no glyph-index bookkeeping needed on this
backend, unlike native).

## Hit-testing

`dispatch-click`/`hover-key` (or wherever the equivalent per-node case
lives for `LText` today, which is nowhere — `Text` isn't currently a hit
target) gain an `LRich` case: walk the resolved per-span rects, and on a
match with a span carrying `on-click = Just(msg)`, dispatch `msg` the same
way a `box`'s `on-click` does today.

## `prose` integration

`prose` gains a small backtick-span parser: scan `content` for
`` `...` `` ranges, produce a `text-span` per match with
`font = Just(mono(size))` (no color override, no click), and call `rich`
instead of `paragraph`. `note` gets the same treatment. The existing
`drop-backticks` stopgap from the last round of fixes is removed — this
replaces it, not layers on top of it.

## Testing

- `test/ui/rich-text.kk` (new, mirroring `nested-scroll.kk`'s headless
  pattern): pins wrap geometry for a multi-span string at a narrow width
  (spans split across a line break), and asserts a click on the WRAPPED
  continuation of a clickable span still resolves to that span's message
  (both native and jsweb, matching how existing framework tests run on
  both targets).
- `samples/ui/site` smoke suite: `prose` strings containing backticks
  render with a mono sub-run and no literal backtick characters.

## Open questions for the implementation plan

- Exact extern signatures for the native `rich-*` incremental builder
  calls (parameter shapes, error handling if `Build` is called with no
  `AddText` since the last `PushStyle`).
- Whether `measure-rich`'s font-only spans list needs de-duplication
  against `measure-text`'s existing cache (`measure-cached` in
  `ui/state.kk`) or gets its own cache keyed on the whole span list.
- Whether a clickable span gets any hover/press affordance (a cursor
  change, an underline) or is click-only with no visual feedback, unlike
  `interactive`'s hover/press state. Not raised as a requirement; default
  to click-only unless the plan's author sees an easy win bundling it in.
