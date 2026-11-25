# Reference Pages Group 1 (Layout & containers / Text & content / Interaction) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Retire the `reference-widgets` sampler page's cross-topic shape;
rebuild it as IA topic 1 (Layout & containers) and split its "Text and
content" / "Interactive" sections into two new pages for topics 2 and 3.

**Architecture:** Same content model throughout (`doc-page`/`doc-section`/
`api-entry`/`demo-panel`, no code changes to `model.kk`/`blocks.kk`). Three
tasks, one per page. Task 1 (`reference-widgets`, reused slug) also removes
the now-retired `ref-text-body`/`ref-interactive-body`/`ref-live-body`
functions and the `live-progress`-only "Live sample" section from
`pages.kk`, since Tasks 2/3 recreate their content on new pages and nothing
else references those functions after this plan (`live-progress` itself
stays — Group 2's State & animation page will use it).

**Tech Stack:** Koka, `lib/ui`, `samples/ui/site`.

## Global Constraints

Every entry follows the content style guide's four rules and reference-
depth standard (`docs/superpowers/specs/2026-07-31-docs-site-content-style-design.md`,
required reading for every task brief):

- **Rule 1** — no claim without a same-page receipt (or, where a live demo
  genuinely isn't achievable, ground the claim in mechanism and say plainly
  why there's no demo — never omit silently).
- **Rule 2** — task-first section/page intros.
- **Rule 3** — internals stay off these pages (they're reference, not the
  explanation page).
- **Rule 4** — banned words in new/edited prose: "portable" (bare
  adjective), "powerful", "elegant", "simply".
- **Depth standard** — every `api-entry`: signature, a paragraph naming
  behavior + non-obvious parameters, a "vs." note where a nearby
  alternative exists, and a live demo unless truly not achievable.

**Demo-panel width discipline** (learned the hard way in the prior plan):
`demo-panel`'s code half already shrink-wraps via `intrinsic-width`
(`samples/ui/site/blocks.kk`) — do not touch that. Any NEW `fixed(width =
Just(N))` wrapping a demo's LIVE half must be verified in a real browser at
900px width (not just typechecked) before a task is considered done —
`fixed` only caps an axis; a value that doesn't fit silently overflows the
page. Where this plan gives a demo a `fixed` width, treat it as a starting
guess to verify, not a guaranteed-correct value.

**Slugs and titles** (from the rollout design spec): `reference-widgets`
(reused) → "Reference: layout & containers"; `reference-text-content` →
"Reference: text & content"; `reference-interaction` → "Reference:
interaction".

**Build/verify command** (run from `samples/ui/site`, used by every task):

```bash
KOKA=/Users/timwhiting/koka/.worktrees/koka-clang-wasm/.stack-work/install/aarch64-osx/f85b4dc81f126d06881fec188dc62cdb96d6f54b1fd1f1051955dc1d51fe411a/9.10.3/bin/koka
impdir=/Users/timwhiting/koka/.worktrees/koka-clang-wasm/lib/ui/api/impeller
sdk=$impdir/sdk
$KOKA --console=raw -i. -i../../../lib -e smoke.kk \
  "--ccopts=-I$sdk/include -I$impdir" \
  "--cclib=impeller;impellerhost" \
  "--cclinkopts=-L$sdk/lib -L$impdir -Wl,-rpath,$sdk/lib -Wl,-rpath,$impdir"
```

`smoke.kk`'s `site-scenario` mounts every page in `site-pages()` and checks
every section's slug resolves to exactly one id — after this plan the check
count changes (more pages/sections than before), so **do not** assert a
specific `SMOKE: N/N` number in a task's steps; report whatever N the run
prints and confirm zero `FAIL` lines.

**Typecheck command** (same flags, `-c main.kk` instead of `-e smoke.kk`):

```bash
$KOKA --console=raw -i. -i../../../lib -c main.kk \
  "--ccopts=-I$sdk/include -I$impdir" "--cclib=impeller;impellerhost" \
  "--cclinkopts=-L$sdk/lib -L$impdir -Wl,-rpath,$sdk/lib -Wl,-rpath,$impdir"
```

---

### Task 1: Reference — Layout & containers (rebuild `reference-widgets`)

**Files:**
- Modify: `samples/ui/site/pages.kk` — `ref-containers-body` (extend),
  `site-pages()`'s `reference-widgets` `Doc-page` entry (retitle,
  resection), delete `ref-text-body`, `ref-interactive-body`,
  `ref-live-body` and the `Doc-page`'s "Text and content" / "Interactive" /
  "Live sample" `Doc-section`s (their content moves to Tasks 2/3).

**Interfaces:**
- Consumes: `api-entry`, `demo-panel`, `code-block` (blocks.kk,
  unchanged); `box`, `row`, `column`, `spacer`, `stack`, `scroll`,
  `expanded`, `center`, `fixed`, `intrinsic-width`, `clip`, `overlay`,
  `positioned`, `lazy-column` (lib/ui, unchanged signatures — see each
  step below for the exact ones this task uses).
- Produces: `ref-containers-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>`
  (extended in place, same name/signature). `reference-widgets`'s
  `Doc-page` now has 4 sections instead of 4 differently-named ones —
  see Step 2.

- [ ] **Step 1: Split `ref-containers-body` into four section-body
  functions, keeping the 6 existing entries verbatim**

The existing `ref-containers-body` (box, row/column/spacer, stack, scroll,
expanded, center) already meets the depth standard — move its entries
unchanged into new functions grouped by natural sub-topic, don't rewrite
their prose:

```koka
fun ref-boxes-flex-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("box", ["box(child, padding = 0.0, bg = Nothing, on-click = Nothing)"],
      "A single child on a padded surface. `padding` adds space around the "
      ++ "child; `bg` fills the box (pass Nothing for no background at "
      ++ "all, which is what most layout-only boxes want). Reach for `box` "
      ++ "when you need padding or a background around one thing; reach "
      ++ "for `row`/`column` once you have more than one child. `box` also "
      ++ "carries every click/drag handler a widget can take — "
      ++ "`on-click`, `on-click-at` (with position), `on-context-at` "
      ++ "(right-click), `drag`/`on-drop` — see the interaction reference "
      ++ "for the drag-and-drop pattern built on the last two.",
      demo = Just(demo-panel(
        ["box(text(\"padded\", 14.0, theme.fg), padding = 12.0,",
         "    bg = Just(Fill(theme.surface, 8.0)))"],
        fixed(box(text("padded", 14.0, theme.fg), padding = 12.0,
                   bg = Just(Fill(theme.surface, 8.0))), width = Just(160.0))))),

    api-entry("row, column, spacer", ["row([..], gap = 10.0, fill = False)",
                                       "column([..], gap = 12.0, fill = False)",
                                       "spacer()"],
      "Lay children out horizontally (`row`) or vertically (`column`); "
      ++ "`gap` is the space between siblings. Put a `spacer()` anywhere "
      ++ "in the children list and it greedily takes whatever room is "
      ++ "left, which is how you push one child to the far edge without "
      ++ "computing widths yourself.",
      demo = Just(demo-panel(
        ["row([text(\"left\", 14.0, theme.fg), spacer(),",
         "     text(\"right\", 14.0, theme.fg)], gap = 8.0)"],
        fixed(row([text("left", 14.0, theme.fg), spacer(),
                    text("right", 14.0, theme.fg)], gap = 8.0), width = Just(110.0))))),

    api-entry("stack", ["stack([(x, y, child), ..])"],
      "Children at absolute (x, y) offsets within the space the parent "
      ++ "gives the stack — for overlapping content (a badge on a corner, "
      ++ "a label over an image) that `row`/`column` can't express, since "
      ++ "those only place children next to each other.",
      demo = Just(demo-panel(
        ["stack([",
         "  (0.0, 0.0,",
         "   rect(80.0, 40.0,",
         "        bg = Just(Fill(theme.surface, 6.0)))),",
         "  (10.0, 10.0,",
         "   text(\"on top\", 13.0, theme.fg)),",
         "])"],
        fixed(stack([
          (0.0, 0.0, rect(80.0, 40.0, bg = Just(Fill(theme.surface, 6.0)))),
          (10.0, 10.0, text("on top", 13.0, theme.fg)),
        ]), width = Just(80.0))))) ]

fun ref-scroll-space-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("scroll", ["scroll(child, name = \"\", horizontal = False)"],
      "Makes `child` scrollable along one axis once it's bigger than the "
      ++ "space `scroll` is given — pair it with `expanded` in a fixed-"
      ++ "height parent (see `expanded` below), or the scroll region "
      ++ "shrink-wraps to its content instead of clipping. `name` lets a "
      ++ "sibling read or set the scroll offset (`scroll-state`, "
      ++ "`scroll-to`). No live demo here that isn't already on the page: "
      ++ "every code block is `scroll(..., horizontal = True)` — try "
      ++ "panning one wider than this page's demo blocks (the demo blocks "
      ++ "themselves are kept narrow on purpose, see the interaction "
      ++ "and layout how-to guides for panning ones that aren't).",
      demo = Nothing),

    api-entry("expanded", ["expanded(child, flex = 1.0)"],
      "Inside a row or column, grows `child` to fill whatever main-axis "
      ++ "space is left after the rigid (non-expanded) siblings are "
      ++ "sized — see the layout how-to guide for the header-plus-"
      ++ "scrolling-body pattern this enables. `flex` splits leftover "
      ++ "space between multiple `expanded` siblings by weight. You're "
      ++ "looking at it right now: this site's own shell wraps every "
      ++ "page's content in `expanded(scroll(...))` beneath a fixed-"
      ++ "height header.",
      demo = Just(code-block(["expanded( scroll( box(page-body, padding = 8.0) ) )"]))),

    api-entry("center", ["center(child, max-width = 640.0)"],
      "Centers `child` horizontally, capping its width at `max-width` — "
      ++ "the app-shell idiom for keeping content readable on a wide "
      ++ "window without hand-computing margins. No live demo here: "
      ++ "centering only shows within a parent wider than the child, "
      ++ "which this compact reference layout doesn't provide. Try it "
      ++ "directly — wrap a page's top-level column in "
      ++ "`center(..., max-width = 640.0)`.",
      demo = Nothing),

    api-entry("fixed", ["fixed(child, width = Nothing, height = Nothing)"],
      "Pins `child`'s extent on the given axes: capped at the given size "
      ++ "(the child may measure smaller; it's never stretched), but "
      ++ "`fixed` always REPORTS exactly that size to its parent no "
      ++ "matter what the child actually measured. Every `fixed`-wrapped "
      ++ "demo on this site's reference pages uses it for exactly this: "
      ++ "pinning a small demo to a tidy width regardless of its "
      ++ "content's natural size.",
      demo = Just(demo-panel(
        ["fixed(text(\"clipped if too wide\", 14.0, theme.fg),",
         "      width = Just(90.0))"],
        fixed(text("clipped if too wide", 14.0, theme.fg), width = Just(90.0))))),

    api-entry("intrinsic-width", ["intrinsic-width(child)"],
      "Measures `child` at its own natural width first, then lays it out "
      ++ "tight at that measured size — Flutter's IntrinsicWidth. Costs a "
      ++ "second layout pass, so it's for the cases that need it, not a "
      ++ "default. `demo-panel` (the code-beside-live-demo block every "
      ++ "reference page uses) wraps its code half in this: without it, "
      ++ "a horizontal `scroll` claims the FULL width its row parent "
      ++ "offers instead of shrinking to its own content, which used to "
      ++ "push every demo's live half off the page — see "
      ++ "test/ui/intrinsic-scroll-row.kk for the mechanism this fixed.",
      demo = Nothing) ]
```

- [ ] **Step 2: Add `clip`, `overlay`, `positioned` (paint/positioning)
  and `lazy-column` (long lists) as two more section-body functions**

```koka
fun ref-clip-overlay-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("clip", ["clip(child, radius = 0.0, width = Nothing, height = Nothing)"],
      "Clips `child`'s paint to a rounded rect — `radius` rounds the "
      ++ "corners, `width`/`height` (if given) cap the clip region's size "
      ++ "independent of the child's own layout size. Use it when a "
      ++ "child's content (an image, a long block of text) might paint "
      ++ "past a boundary you want to enforce; `fixed` (above) caps "
      ++ "LAYOUT size and lets an oversize child overflow visually — "
      ++ "`clip` caps PAINT and cuts the overflow off instead.",
      demo = Just(demo-panel(
        ["clip(text(\"clipped, not shrunk\", 14.0, theme.fg),",
         "     width = Just(70.0), height = Just(20.0))"],
        clip(text("clipped, not shrunk", 14.0, theme.fg),
             width = Just(70.0), height = Just(20.0))))),

    api-entry("overlay", ["overlay(child)"],
      "Lays `child` out UNBOUNDED but reports zero size upward — for "
      ++ "content a `positioned` layer (below) will place independently "
      ++ "of normal flow, so its presence in a row/column doesn't shift "
      ++ "its siblings. `overlay` and `positioned` are usually paired: "
      ++ "`overlay` opts a subtree out of layout, `positioned` decides "
      ++ "where it actually paints.",
      demo = Nothing),

    api-entry("positioned", ["positioned(child, target = Nothing, target-align = top-left,",
                              "           self-align = top-left, offset-x = 0.0, offset-y = 0.0)"],
      "A full-viewport layer holding `child`, anchored to a target rect: "
      ++ "`child`'s `self-align` point is placed at the target's "
      ++ "`target-align` point (plus the offset), clamped on-screen. "
      ++ "`target = Nothing` anchors to the viewport itself (cursor "
      ++ "overlays, centered modals); a `Just` rect anchors to a specific "
      ++ "region. This is the primitive a tooltip, dropdown, or context "
      ++ "menu is built from — see the theming reference for "
      ++ "`ui/style/default`'s ready-made `dropdown`/`context-menu`, "
      ++ "which wrap `positioned` so you don't call it directly for the "
      ++ "common cases.",
      demo = Nothing) ]

fun ref-lazy-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("lazy-column", ["lazy-column(item, count = Nothing, item-extent = 40.0,",
                               "            cache = 4, name = \"\")"],
      "A scrolling list that only builds the rows near the viewport "
      ++ "instead of every row up front — `item(i, key)` builds row `i`; "
      ++ "`item-extent` is each row's fixed height (rows must be a "
      ++ "uniform, known height for the windowing math); `cache` is how "
      ++ "many extra rows to keep built just outside the viewport, "
      ++ "trading memory for smoother fast-scroll. Reach for it once a "
      ++ "plain `column` inside a `scroll` would build thousands of rows "
      ++ "at once; for a list of a few dozen items, a `column` is "
      ++ "simpler and the windowing isn't worth it. No live demo here — "
      ++ "a list long enough to show windowing behavior needs more "
      ++ "vertical room than this compact reference format has; see the "
      ++ "photo browser tutorial for `lazy-column` driving a real "
      ++ "scrolling grid.",
      demo = Nothing) ]
```

- [ ] **Step 3: Wire the new section functions into `site-pages()`, retire
  the old sections/functions**

In `pages.kk`, find `site-pages<a>()`'s `Doc-page(QReference, "reference-widgets", ...)`
entry. Replace it with:

```koka
    Doc-page(QReference, "reference-widgets", "Reference: layout & containers",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. Layout containers: "
      ++ "boxes, flex, scrolling, clipping, positioning, and long lists.",
      [ Doc-section("Boxes and flex", ref-boxes-flex-body),
        Doc-section("Scrolling and space", ref-scroll-space-body),
        Doc-section("Clipping and overlays", ref-clip-overlay-body),
        Doc-section("Long lists", ref-lazy-body) ]),
```

Then delete the old `fun ref-text-body`, `fun ref-containers-body`,
`fun ref-interactive-body`, `fun ref-live-body` definitions entirely (their
content now lives in the functions from Steps 1-2 above, and in Tasks 2-3's
new pages) — do NOT delete `live-progress` itself (defined earlier in the
file, in the "live demos" section) or `demo-button`; both stay, used
elsewhere on the site and by Group 2 later.

- [ ] **Step 4: Typecheck**

Run the Global Constraints typecheck command. Fix any errors before
continuing (the new entries above are hand-written against real signatures
but not compiler-verified in advance — small adjustments, e.g. an explicit
`?key` to disambiguate two demos in the same section, may be needed; follow
the existing `scope("...")`/`here()` idioms already used throughout this
file).

- [ ] **Step 5: Run the smoke suite**

Run the Global Constraints smoke command. Report the printed `SMOKE: N/N`
and confirm zero `FAIL` lines (N will be higher than before this task,
since the page now has 4 sections instead of 4 differently-shaped ones —
that's expected, don't try to match a specific number).

- [ ] **Step 6: Manually verify new demos in a browser at 900px width**

Per the Global Constraints' demo-width discipline: build the site for
jsweb, serve `out-js/`, navigate to `#/reference-widgets` at a 900px-wide
viewport, and confirm the `fixed`/`text` demo (in the `fixed` entry) and
the `clip`/`text` demo (in the `clip` entry) render fully within the
viewport (right edge < 900px) — these are the two new demos with an
explicit width that risk the overflow class of bug the prior plan hit.

- [ ] **Step 7: Verify no banned words**

```bash
grep -n "portable\|powerful\|elegant\|simply" samples/ui/site/pages.kk
```
Expected: no output (the file no longer has any of the four banned words
anywhere, not just in this task's new content).

- [ ] **Step 8: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: reference-widgets rebuilt as Layout & containers (topic 1 of 9)"
```

---

### Task 2: Reference — Text & content (new page)

**Files:**
- Modify: `samples/ui/site/pages.kk` — add `ref-text-body` (recreated,
  extended), add the new `Doc-page` entry to `site-pages()`.
- Create asset: `samples/ui/site/assets/mars.jpg` (copy of
  `samples/ui/gallery/assets/mars.jpg` — NASA/JPL PIA24543, public domain,
  same image the gallery sample already uses live).

**Interfaces:**
- Consumes: `api-entry`, `demo-panel` (blocks.kk); `text`, `paragraph`,
  `code`, `rect`, `sans`, `serif`, `mono`, `bold`, `font` (lib/ui/widget.kk);
  `image-path`, `FromPath` — wait, `image-path` takes a plain string path,
  not `FromPath` directly (`image-path<msg>(src : string, fit = Contain,
  load = Async, placeholder = default-placeholder(), min-load = zero,
  width = 0.0, height = 0.0)`, from `lib/ui/async.kk`) — imported via
  `ui/async` (NEW import this task needs to add to `pages.kk`'s import
  list, alongside the existing `ui/keytrie`/`ui/ident`/`ui/widget`/
  `ui/state`/`ui/style/default`/`model`/`blocks`).
- Produces: `ref-text-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>`
  (this name is reused — the old function of this name is deleted by
  Task 1; if Task 1 hasn't landed yet when this task starts, coordinate
  with the controller rather than leaving two definitions of the same
  name in the file).

- [ ] **Step 1: Copy the image asset**

```bash
mkdir -p samples/ui/site/assets
cp samples/ui/gallery/assets/mars.jpg samples/ui/site/assets/mars.jpg
```

- [ ] **Step 2: Add the `ui/async` import**

In `samples/ui/site/pages.kk`'s import block, add `import ui/async` (for
`image-path`) alongside the existing imports.

- [ ] **Step 3: Write `ref-text-body`, carrying the 3 existing entries
  over unchanged and adding 3 more**

```koka
fun ref-text-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("text", ["text(content, size, color)   // single line"],
      "Draws a single line of text; it does not wrap, and does not shrink "
      ++ "to fit — a string wider than its parent clips. Use "
      ++ "`text` for labels and short strings that should never wrap; use "
      ++ "`paragraph` for anything that might need more than one line.",
      demo = Just(demo-panel(["text(\"Hello\", 16.0, theme.fg)"],
                              text("Hello", 16.0, theme.fg)))),

    api-entry("paragraph", ["paragraph(content, size, color)  // wraps"],
      "Wraps text to the width its parent gives it, breaking at word "
      ++ "boundaries. Every paragraph of prose on this page — this "
      ++ "sentence included — is a `paragraph` widget."),

    api-entry("code", ["code(content, size)   // monospace"],
      "Text set in the mono font, sized for source lines rather than "
      ++ "prose. `code-block` (the layout reference's `Boxes and flex` "
      ++ "section describes its container) is a column of `code` widgets "
      ++ "on a panel background — every code sample on this page is "
      ++ "built from it."),

    api-entry("fonts: sans, serif, mono, bold, font",
      ["sans(size = 15.0)   // system sans, the default",
       "serif(size = 15.0)",
       "mono(size = 14.0)",
       "bold(f)             // weight 700 of an existing font",
       "font(family, size = 15.0, weight = 400, italic = False)"],
      "`text`/`paragraph` take either a plain `size : float64` (system "
      ++ "sans at that size — the common case, used throughout this "
      ++ "site) or a `font` value from one of these for anything else. "
      ++ "`bold` wraps an existing font rather than being its own family "
      ++ "— `bold(sans(16.0))`, not a separate bold-sans constructor. "
      ++ "Reach for `font` directly only for a family/weight/italic "
      ++ "combination none of `sans`/`serif`/`mono`/`bold` already "
      ++ "gives you.",
      demo = Just(demo-panel(
        ["text(\"bold serif\", bold(serif(16.0)), theme.fg)"],
        text("bold serif", bold(serif(16.0)), theme.fg)))),

    api-entry("rect", ["rect(w, h, bg = Nothing, on-click = Nothing)"],
      "A fixed-size, optionally clickable colored box — grid cells, "
      ++ "swatches, placeholders. Every colored rectangle in this site's "
      ++ "own demos (the `stack`/`clip` demos on the layout reference "
      ++ "page, for instance) is a `rect`. Unlike `box`, `rect` has no "
      ++ "child — reach for `box` the moment you need to put something "
      ++ "inside it.",
      demo = Just(demo-panel(
        ["rect(60.0, 30.0, bg = Just(Fill(theme.accent, 6.0)))"],
        rect(60.0, 30.0, bg = Just(Fill(theme.accent, 6.0)))))),

    api-entry("image, image-path", ["image-path(src, fit = Contain, load = Async,",
                                     "           placeholder = default-placeholder(),",
                                     "           min-load = zero, width = 0.0, height = 0.0)"],
      "Loads and paints an image. `image-path(src, ...)` is the common "
      ++ "case (a plain asset path or URL); `image(source, ...)` takes an "
      ++ "explicit `image-source` (`FromPath`/`FromBytes`/`FromPixels`) "
      ++ "when the bytes don't come from a simple path. `fit` (`Cover` "
      ++ "crops to fill, `Contain` letterboxes) matters once the image's "
      ++ "own aspect ratio doesn't match the box you give it; `load = "
      ++ "Async` (the default) decodes off the async pump and shows "
      ++ "`placeholder` until it's ready — `min-load` holds the "
      ++ "placeholder at least that long even if the decode finishes "
      ++ "sooner, so a fast local load doesn't flash. `load = Sync` "
      ++ "decodes inline on first paint instead (native only; simpler, "
      ++ "but blocks that frame).",
      demo = Just(demo-panel(
        ["image-path(\"assets/mars.jpg\", fit = Cover,",
         "           width = 120.0, height = 80.0)"],
        image-path("assets/mars.jpg", fit = Cover, width = 120.0, height = 80.0)))) ]
```

- [ ] **Step 4: Add the `Doc-page` entry to `site-pages()`**

Add this entry to the `[ ... ]` list `site-pages<a>()` returns, in
`QReference` order right after `reference-widgets` (order within a
quadrant is display order for next/prev and the sidebar):

```koka
    Doc-page(QReference, "reference-text-content", "Reference: text & content",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. The leaf widgets that "
      ++ "actually draw something: text, images, and plain colored "
      ++ "rects.",
      [ Doc-section("Text and content", ref-text-body) ]),
```

- [ ] **Step 5: Typecheck**

Run the Global Constraints typecheck command. Fix any errors before
continuing (same note as Task 1 Step 4 — the entries above are hand-written
against real signatures, not pre-verified).

- [ ] **Step 6: Run the smoke suite**

Run the Global Constraints smoke command. Report the printed `SMOKE: N/N`
and confirm zero `FAIL` lines.

- [ ] **Step 7: Manually verify the image and fonts demos in a browser**

Build for jsweb, serve, navigate to `#/reference-text-content` at 900px
width. Confirm: the `image-path` demo actually shows the Mars image (not a
placeholder stuck forever — if it never resolves, check the asset path is
correct relative to where jsweb serves from); the fonts demo renders
visibly bold serif text; nothing overflows past 900px.

- [ ] **Step 8: Verify no banned words**

```bash
grep -n "portable\|powerful\|elegant\|simply" samples/ui/site/pages.kk
```
Expected: no output.

- [ ] **Step 9: Commit**

```bash
git add samples/ui/site/pages.kk samples/ui/site/assets/mars.jpg
git commit -m "site: reference-text-content -- new page for topic 2 (text & content leaves)"
```

---

### Task 3: Reference — Interaction (new page)

**Files:**
- Modify: `samples/ui/site/pages.kk` — add `ref-interactive-body`
  (recreated, extended), add the new `Doc-page` entry.

**Interfaces:**
- Consumes: `api-entry`, `demo-panel`, `demo-button` (existing helper in
  `pages.kk`); `primary-button`, `quiet-button` (lib/ui/style/default),
  `text-input`, `slider`, `link`, `act`, `act-msg`, `field` (lib/ui/widget);
  `interactive`, `interaction` struct (lib/ui/state) — `interactive<msg>(
  on-click : msg, build : (interaction) -> <keytree,uistate,ioc> widget<msg>,
  disabled : bool = False, hit-slop : float64 = 0.0)`, where `interaction`
  has fields `hovered`/`pressed`/`focused`/`disabled : bool`.
- Produces: `ref-interactive-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>`
  (name reused — same coordination note as Task 2 if Task 1 hasn't landed
  first).

Note: this page absorbs the retired `ref-live-body`'s slider cross-
reference gap. The OLD `slider` entry's prose said "the Live sample section
below shows the same idea" — that section is retired by Task 1, and its
replacement (a real `use-state`/`animate` demo) doesn't land until Group
2's State & animation page, which doesn't exist yet when this task runs.
Don't reference a page that doesn't exist (the exact class of dangling
cross-reference the content-revision plan's final review caught and fixed
once already) — the `slider` entry below describes the mechanism honestly
instead of pointing anywhere.

- [ ] **Step 1: Write `ref-interactive-body`, carrying the 4 existing
  entries over (one with an updated cross-reference) and adding 4 more**

```koka
fun ref-interactive-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("primary-button, quiet-button", ["primary-button(label, on-click : msg, size = 15.0)",
                                                "quiet-button(label, on-click : msg, size = 15.0)"],
      "Themed, click-animated buttons: `primary-button` is filled with the "
      ++ "accent color for the main action on a screen; `quiet-button` "
      ++ "sits on the surface color for secondary actions. Both take an "
      ++ "app message (`on-click : msg`), which this page — like every "
      ++ "reference entry — is written without, so it can't embed the "
      ++ "real widgets live. The demo below shows the same click/press "
      ++ "animation via `act` (below), the lower-level primitive "
      ++ "`primary-button` and `quiet-button` are themselves built on:",
      demo = Just(demo-panel(
        ["act(",
         "  box(text(\"Try me\", 16.0, on-accent),",
         "      padding = 9.0,",
         "      bg = Just(Fill(theme.accent, 6.0))),",
         "  on )"],
        demo-button("Try me", fn() (), here())))),

    api-entry("text-input", ["text-input(value, on-input : string -> msg, placeholder = \"\", width = 220.0)"],
      "A single-line editable field. `on-input` fires with the field's "
      ++ "current text on every keystroke, so the app model always holds "
      ++ "the live value (a CONTROLLED input, in React terms). No live "
      ++ "demo here: `on-input` needs an app message this page doesn't "
      ++ "have. See `field` (below) for an UNCONTROLLED alternative whose "
      ++ "value lives in ui/state instead of the model.",
      demo = Nothing),

    api-entry("slider", ["slider(value, on-change : float64 -> msg, lo = 0.0, hi = 1.0, step = 0.0)"],
      "A horizontal slider over `[lo, hi]`, snapped to `step` (0.0 means "
      ++ "no snapping). Like `text-input`, `on-change` needs an app "
      ++ "message this page doesn't have, so there's no live `slider` "
      ++ "demo — the mechanism is the same as `text-input`'s: the app "
      ++ "model holds the current value, `on-change` updates it, the "
      ++ "slider redraws at the new position next render.",
      demo = Nothing),

    api-entry("link", ["link(route-path, child)"],
      "Wraps `child` in a navigation target for `route-path` (no leading "
      ++ "'#') — a real `<a href=\"#/...\">` on the web (right-click, "
      ++ "open-in-new-tab, and deep-linking all work), a click target the "
      ++ "router handles the same way natively. `link` takes no message "
      ++ "of its own, which is why it — unlike the buttons above — can "
      ++ "appear directly on this message-agnostic reference page. The "
      ++ "sidebar you're using right now is built from it, and so is "
      ++ "this:",
      demo = Just(demo-panel(
        ["link(",
         "  \"howto-layout\",",
         "  accented(",
         "    \"Go to the layout how-to\", 15.0))"],
        link("howto-layout", accented("Go to the layout how-to", 15.0))))),

    api-entry("act", ["act(child, on-act : () -> <uistate,ioc> ())"],
      "A click target that runs a thunk instead of emitting an app "
      ++ "message — the door for `ui/state` writes (toggles, uncontrolled "
      ++ "field reads) that never touch the model. You just clicked one: "
      ++ "the \"Try me\" button above is `act` wrapping a box, its thunk "
      ++ "bumping an `ui/state` counter — the same mechanism the live "
      ++ "counters throughout this site use.",
      demo = Nothing),

    api-entry("act-msg", ["act-msg(child, to-msg : () -> <uistate,ioc> msg)"],
      "Like `act`, but the thunk COMPUTES a message from `ui/state` at "
      ++ "click time instead of running a side-effecting write — the "
      ++ "form-submit primitive: read one or more `field`s, build one "
      ++ "message from what they hold. Use `act` when the click's only "
      ++ "job is an `ui/state` write; use `act-msg` when the click needs "
      ++ "to also tell the app model something.",
      demo = Nothing),

    api-entry("field", ["field(name = \"\", placeholder = \"\", width = 220.0,",
                         "      on-enter : maybe<string -> msg> = Nothing)"],
      "An UNCONTROLLED single-line text field: its value lives in "
      ++ "`ui/state`, not the app model, so typing in it causes no "
      ++ "re-render of anything that doesn't read it. Give it a `name` "
      ++ "and a sibling can read its live text with "
      ++ "`field-text(field-key(name))` — the pattern `act-msg`'s "
      ++ "form-submit button uses. `on-enter` optionally maps the Enter "
      ++ "key to a message, the one way a `field` CAN talk to the app "
      ++ "model directly without a submit button. No live demo here: "
      ++ "reading a field's value back to display it needs the same "
      ++ "app-message wiring `text-input`/`slider` don't have on this "
      ++ "page.",
      demo = Nothing),

    api-entry("interactive, interaction", ["interactive(on-click : msg, build : (interaction) -> widget<msg>,",
                                            "            disabled = False, hit-slop = 0.0)"],
      "The primitive `primary-button`/`quiet-button` (and every other "
      ++ "themed clickable in `ui/style/default`) are built on: owns the "
      ++ "click, tracks hover/press/focus by widget identity, and calls "
      ++ "`build` with the LIVE `interaction` state (`hovered`, "
      ++ "`pressed`, `focused`, `disabled` — all `bool`) so your content "
      ++ "can change color, border, even structure on hover/press without "
      ++ "any of that touching the app model. `disabled` blocks the click "
      ++ "and is passed through to `build` so the content can gray "
      ++ "itself out. `hit-slop` widens the CLICKABLE area beyond the "
      ++ "visual one without changing layout — for a small icon that "
      ++ "needs a bigger touch target than it visually occupies. Reach "
      ++ "for `interactive` directly when you're building your own "
      ++ "themed component; reach for `primary-button`/`quiet-button` "
      ++ "when an existing one already does what you need.",
      demo = Nothing) ]
```

- [ ] **Step 2: Add the `Doc-page` entry to `site-pages()`**

Add this entry to `site-pages<a>()`'s list, in `QReference` order right
after `reference-text-content`:

```koka
    Doc-page(QReference, "reference-interaction", "Reference: interaction",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. Buttons, fields, links, "
      ++ "and the lower-level primitives they're built on.",
      [ Doc-section("Interactive", ref-interactive-body) ]),
```

- [ ] **Step 3: Typecheck**

Run the Global Constraints typecheck command. Fix any errors before
continuing (same note as prior tasks).

- [ ] **Step 4: Run the smoke suite**

Run the Global Constraints smoke command. Report the printed `SMOKE: N/N`
and confirm zero `FAIL` lines.

- [ ] **Step 5: Manually verify the button and link demos in a browser**

Build for jsweb, serve, navigate to `#/reference-interaction` at 900px
width. Click the "Try me" button — confirm the press/hover animation
plays (same visual as the home page's live counter buttons). Click the
"Go to the layout how-to" link — confirm it navigates to
`#/reference-widgets` (Task 1's renamed page — the how-to page's own slug
is `howto-layout`, but if Task 1 already ran, double check this link's
target still makes sense given `reference-widgets` no longer has the same
content it did when this link text/target was originally written; if it
reads oddly, that's fine to leave — `howto-layout` is still the correct
navigation target regardless of what `reference-widgets` now contains).

- [ ] **Step 6: Verify no banned words**

```bash
grep -n "portable\|powerful\|elegant\|simply" samples/ui/site/pages.kk
```
Expected: no output.

- [ ] **Step 7: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: reference-interaction -- new page for topic 3 (interaction)"
```

---

## Final check (after all 3 tasks)

- [ ] Confirm no banned words remain anywhere in the file (same grep as
  above).
- [ ] Run the smoke suite one more time; confirm zero `FAIL` lines and
  note the final `SMOKE: N/N` count for the ledger.
- [ ] Confirm the sidebar (any page, any quadrant) now shows exactly 3
  entries under REFERENCE: "Reference: layout & containers", "Reference:
  text & content", "Reference: interaction" — no leftover "Reference:
  widget catalog" title, no 4th sampler entry.
- [ ] Confirm `next-prev-links` on each of the 3 reference pages links to
  the correct neighbor within the REFERENCE quadrant (first has no prev,
  last has no next since Groups 2/3 haven't landed yet — that's expected
  and correct for this plan's scope).
