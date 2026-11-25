# Docs Site Content Revision (5 pages) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rewrite the content (not structure) of the docs site's 5 existing
pages under the content style guide, so they stop leading with unbacked
claims/internals and start teaching.

**Architecture:** No new files, no changes to `doc-page`/`doc-section`/
`api-entry` (model.kk, blocks.kk unchanged). Every task edits page-body
functions in `samples/ui/site/pages.kk` only — same shape (functions
returning `list<widget<a>>`), different prose and, for the reference page,
more `api-entry`s per section. Section titles, page slugs, and page/section
counts are unchanged, so the existing smoke suite's structural checks stay
valid without modification.

**Tech Stack:** Koka, `lib/ui`, the existing `samples/ui/site` sample app.

## Global Constraints

Every task's edits must satisfy the content style guide in
`docs/superpowers/specs/2026-07-31-docs-site-content-style-design.md`
(required reading for every task brief). Summarized:

- **Rule 1 — no claim without a receipt on the same page.** A claim about
  the framework is only allowed where the page proves it to the reader
  immediately (a demo, a visible mechanism, or something already true of the
  page itself). Otherwise cut it, or ground it in the *mechanism* ("X works
  this way, which is why Y") rather than asserting the outcome as a bare
  fact.
- **Rule 2 — task-first opening.** Section/page intros lead with the
  reader's problem or what they're about to build, not with adjectives
  about the framework.
- **Rule 3 — internals stay on the explanation page.** Perceus/FBIP/
  reconciliation/backend-lowering talk belongs on `explanation-one-core`
  (Task 5), not leaking into reference/how-to/tutorial bodies.
- **Rule 4 — no unearned superlatives.** Banned words in new/edited prose:
  "portable" (as a bare adjective), "powerful", "elegant", "simply". Replace
  with the specific, verifiable behavior.
- **Reference depth standard** (applies to Task 4 only): every `api-entry`
  gets signature + a paragraph naming what it does, its non-obvious
  parameters, a "vs." note where a nearby alternative exists, and a live
  demo unless one is genuinely not achievable — in which case say so in the
  prose rather than silently omitting it.

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

Expected final line: `SMOKE: 16/16 passed` (unchanged from before this
plan — no sections are added or removed, only their body content changes).
If the koka binary path above is stale, `stack path --local-install-root`
from the repo root prints the current one.

---

### Task 1: Home page

**Files:**
- Modify: `samples/ui/site/pages.kk:62-79` (`home-body`)

**Interfaces:**
- Consumes: `live-counter(here())` (pages.kk, unchanged), `doc-link` (blocks.kk,
  unchanged), `doc-title`/`prose`/`heading` (blocks.kk, unchanged).
- Produces: nothing new — `home-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>`
  keeps its exact signature; `main.kk`'s `page-body` calls it unchanged.

- [ ] **Step 1: Replace `home-body`'s content**

Current (to replace):
```koka
pub fun home-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ doc-title("Koka × ui"),
    prose("A portable, declarative UI framework in Koka. One widget vocabulary "
          ++ "(widget<msg>) runs unchanged on three backends: the browser (jsweb "
          ++ "and wasi-web) and native desktop via Impeller. Views are pure data, "
          ++ "handlers are typed messages, and effects carry async and state."),
    heading("Try it"),
    prose("This whole page is built with lib/ui. The counter below is a live "
          ++ "widget -- its state lives in ui/state, not the app model:"),
    live-counter(here()),
    prose("Use the sidebar to explore the docs, organized the Diátaxis way: "
          ++ "tutorials to learn, how-to guides for tasks, reference for the API, "
          ++ "and explanation for the why."),
    // a CROSS-PAGE ANCHOR: this link switches to the explanation page AND
    // scrolls it so that section sits at the top -- one hash, both effects
    doc-link( "explanation-one-core#state-without-the-model",
              "how ephemeral state works (explanation)",
              ?key = scope("jump-state") ) ]
```

New:
```koka
pub fun home-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ doc-title("Koka × ui"),
    prose("Below is a counter. Click it — what you're clicking is a lib/ui "
          ++ "widget, and this whole page (sidebar, layout, the counter's own "
          ++ "state) is one lib/ui app, written in Koka."),
    live-counter(here()),
    prose("The counter's count lives in ui/state, not in this page's own "
          ++ "model — embedding it above took no wiring beyond that one "
          ++ "function call. See how ephemeral state works for what that "
          ++ "means and why it matters once a page has more than one "
          ++ "interactive thing on it:"),
    // a CROSS-PAGE ANCHOR: this link switches to the explanation page AND
    // scrolls it so that section sits at the top -- one hash, both effects
    doc-link( "explanation-one-core#state-without-the-model",
              "how ephemeral state works (explanation)",
              ?key = scope("jump-state") ),
    heading("Where to go from here"),
    prose("New to lib/ui? Start with \"Your first app\" — it builds a "
          ++ "complete counter app from a blank file in four steps. "
          ++ "Reference documents individual widgets and functions; how-to "
          ++ "guides answer one task at a time; explanation covers the "
          ++ "model underneath.") ]
```

- [ ] **Step 2: Typecheck**

```bash
cd samples/ui/site
impdir=/Users/timwhiting/koka/.worktrees/koka-clang-wasm/lib/ui/api/impeller
sdk=$impdir/sdk
$KOKA --console=raw -i. -i../../../lib -c main.kk \
  "--ccopts=-I$sdk/include -I$impdir" \
  "--cclib=impeller;impellerhost" \
  "--cclinkopts=-L$sdk/lib -L$impdir -Wl,-rpath,$sdk/lib -Wl,-rpath,$impdir"
```
Expected: no errors (warnings about unused pattern vars elsewhere in the
tree are pre-existing and fine).

- [ ] **Step 3: Run the smoke suite (Global Constraints command)**

Expected: `SMOKE: 16/16 passed`.

- [ ] **Step 4: Verify the banned phrase is gone**

```bash
grep -n "portable, declarative\|powerful\|elegant" samples/ui/site/pages.kk
```
Expected: no output.

- [ ] **Step 5: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: home page opens with the live counter, not framework claims"
```

---

### Task 2: Tutorial — "Your first app"

**Files:**
- Modify: `samples/ui/site/pages.kk:83-112` (`tut-result-body`) and the
  `tutorial-first-app` `Doc-page`'s `intro` string (around line 209-211).

**Interfaces:**
- Consumes: `live-counter` (pages.kk, unchanged).
- Produces: nothing new — same functions, same signatures.

- [ ] **Step 1: Replace `tut-result-body`'s content**

Current:
```koka
fun tut-result-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("That is a complete, portable app. Here is the same thing, live:"),
    live-counter(here()) ]
```

New:
```koka
fun tut-result-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("That's the whole app — three top-level functions. Here it is, "
          ++ "live, running right on this page:"),
    live-counter(here()) ]
```

- [ ] **Step 2: Replace the tutorial's `Doc-page` intro**

Find, inside `site-pages<a>()`, the `Doc-page(QTutorial, "tutorial-first-app", "Your first app", ...)`
entry. Current intro string:
```koka
      "An app is three things: a model, an update, and a view. The runtime "
      ++ "owns the loop -- you write pure functions.",
```
New:
```koka
      "You're about to build a counter app in three functions: a model, "
      ++ "an update, and a view. The runtime owns the render loop for you.",
```

- [ ] **Step 3: Typecheck**

```bash
cd samples/ui/site
impdir=/Users/timwhiting/koka/.worktrees/koka-clang-wasm/lib/ui/api/impeller
sdk=$impdir/sdk
$KOKA --console=raw -i. -i../../../lib -c main.kk \
  "--ccopts=-I$sdk/include -I$impdir" \
  "--cclib=impeller;impellerhost" \
  "--cclinkopts=-L$sdk/lib -L$impdir -Wl,-rpath,$sdk/lib -Wl,-rpath,$impdir"
```

- [ ] **Step 4: Run the smoke suite (Global Constraints command)**

Expected: `SMOKE: 16/16 passed`.

- [ ] **Step 5: Verify the banned phrase is gone**

```bash
sed -n '/pub fun site-pages/,/^$/p' samples/ui/site/pages.kk | grep -n "portable\|powerful\|elegant"
```
Expected: no output.

- [ ] **Step 6: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: tutorial-first-app drops the 'portable app' claim, keeps the receipt"
```

---

### Task 3: How-to — "Lay out a screen"

**Files:**
- Modify: `samples/ui/site/pages.kk:116-147` (`howto-rows-body`,
  `howto-fill-body`, `howto-center-body`) and the `howto-layout` `Doc-page`'s
  `intro` string.

**Interfaces:**
- Consumes: `code-block`, `prose` (blocks.kk, unchanged), `with-two-counters`
  (pages.kk, unchanged).
- Produces: nothing new — same functions, same signatures.

- [ ] **Step 1: Replace the how-to's `Doc-page` intro**

Current:
```koka
      "Layout is Flutter-style: constraints flow down, sizes flow up, the "
      ++ "parent positions its children. The core primitives:",
```
New:
```koka
      "The layout primitives you reach for constantly: putting things in a "
      ++ "row or column, making one thing fill whatever space is left, and "
      ++ "keeping content centered and readable on a wide window.",
```

- [ ] **Step 2: Add a lead-in to `howto-rows-body`**

Current:
```koka
fun howto-rows-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ code-block([
      "column([ header, body ], gap = 12.0)",
      "row([ left, spacer(), right ])   // spacer pushes apart",
    ]) ]
```
New:
```koka
fun howto-rows-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("Two calls cover most layouts: `column` stacks children top to "
          ++ "bottom, `row` places them left to right. Drop a `spacer()` "
          ++ "into either list to push everything after it to the far "
          ++ "edge:"),
    code-block([
      "column([ header, body ], gap = 12.0)",
      "row([ left, spacer(), right ])   // spacer pushes apart",
    ]) ]
```

- [ ] **Step 3: Rewrite `howto-fill-body`'s lead-in**

Current:
```koka
fun howto-fill-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("`expanded` grows a child to share the space left after the rigid "
          ++ "siblings -- the key to a fixed header over a scrolling body:"),
    code-block([
      "column([",
      "  header,                       // natural height",
      "  expanded( scroll( list ) ),   // takes the rest, scrolls",
      "], fill = True)",
    ]) ]
```
New:
```koka
fun howto-fill-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("You have a header and a scrolling list below it, and you want "
          ++ "the list to take whatever space is left. `expanded` is the "
          ++ "primitive for that — it grows a child to fill whatever room "
          ++ "the rigid (non-expanded) siblings didn't use:"),
    code-block([
      "column([",
      "  header,                       // natural height",
      "  expanded( scroll( list ) ),   // takes the rest, scrolls",
      "], fill = True)",
    ]) ]
```

- [ ] **Step 4: Add lead-ins to `howto-center-body`**

Current:
```koka
fun howto-center-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ code-block([
      "center( content, max-width = 640.0 )   // the app-shell idiom",
    ]),
    prose("Two live counters, independent because ephemeral state keys by call site:"),
    // NOTE: distinct source lines -> distinct `?child-key` -> independent state
    // (two `live-counter()` on ONE line would share a key and move together)
    with-two-counters(key) ]
```
New:
```koka
fun howto-center-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("On a wide window, content stretched edge to edge is hard to "
          ++ "read. Cap it and center it in one call:"),
    code-block([
      "center( content, max-width = 640.0 )   // the app-shell idiom",
    ]),
    prose("Two live counters below, independent of each other because "
          ++ "ephemeral state keys by call site — put both `live-counter` "
          ++ "calls on the same source line instead of two different ones "
          ++ "and they'd share state and move together:"),
    // NOTE: distinct source lines -> distinct `?child-key` -> independent state
    // (two `live-counter()` on ONE line would share a key and move together)
    with-two-counters(key) ]
```

- [ ] **Step 5: Typecheck**

```bash
cd samples/ui/site
impdir=/Users/timwhiting/koka/.worktrees/koka-clang-wasm/lib/ui/api/impeller
sdk=$impdir/sdk
$KOKA --console=raw -i. -i../../../lib -c main.kk \
  "--ccopts=-I$sdk/include -I$impdir" \
  "--cclib=impeller;impellerhost" \
  "--cclinkopts=-L$sdk/lib -L$impdir -Wl,-rpath,$sdk/lib -Wl,-rpath,$impdir"
```

- [ ] **Step 6: Run the smoke suite (Global Constraints command)**

Expected: `SMOKE: 16/16 passed`.

- [ ] **Step 7: Verify no banned words crept in**

```bash
sed -n '/^fun howto-/,/^fun ref-text-body/p' samples/ui/site/pages.kk | grep -n "portable\|powerful\|elegant\|simply"
```
Expected: no output.

- [ ] **Step 8: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: howto-layout opens each section with the reader's problem"
```

---

### Task 4: Reference — "Widget catalog"

This is the largest task: `ref-containers-body` and `ref-interactive-body`
move from bare `code-block`s to full `api-entry`s at the depth standard, and
`ref-text-body` gains vs.-notes. No `api-entry`/`demo-panel` signature
changes — every new entry uses the existing blocks.kk helpers exactly as
`ref-text-body`'s `text` entry already does.

**Files:**
- Modify: `samples/ui/site/pages.kk:151-180` (`ref-text-body`,
  `ref-containers-body`, `ref-interactive-body`) and the
  `reference-widgets` `Doc-page`'s `intro` string.

**Interfaces:**
- Consumes: `api-entry(name, signature, description, demo, ?key, ?kk-file-line)`,
  `demo-panel(code, live, ?key, ?kk-file-line)`, `code-block` (blocks.kk,
  unchanged); `box`, `row`, `column`, `spacer`, `stack`, `rect`, `text`,
  `link`, `fixed`, `demo-button` (widget.kk / pages.kk, unchanged
  signatures — `fixed<msg>(child, width = Nothing, height = Nothing)` caps
  an axis without stretching, used here only to keep demos a tidy width).
- Produces: nothing new — same functions, same signatures.

- [ ] **Step 1: Replace the reference page's `Doc-page` intro**

Current:
```koka
      "Every constructor returns a widget<msg>. A selection:",
```
New:
```koka
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the exact call that produced it. This is a "
      ++ "working selection of the widget vocabulary, not the full "
      ++ "catalog: text and content, the layout containers, and the "
      ++ "interactive primitives.",
```

- [ ] **Step 2: Add vs.-notes to `ref-text-body`**

Current:
```koka
fun ref-text-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("text", ["text(content, size, color)   // single line"],
      "Draws a single line of text; does not wrap.",
      demo = Just(demo-panel(["text(\"Hello\", 16.0, theme.fg)"],
                              text("Hello", 16.0, theme.fg)))),
    api-entry("paragraph", ["paragraph(content, size, color)  // wraps"],
      "Wraps text to the available width."),
    api-entry("code", ["code(content, size)   // monospace"],
      "Monospace text, sized for code samples.") ]
```
New:
```koka
fun ref-text-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("text", ["text(content, size, color)   // single line"],
      "Draws a single line of text; it does not wrap, and does not shrink "
      ++ "to fit — a string wider than its parent overflows visually. Use "
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
      ++ "prose. `code-block` (below, under Containers) is a column of "
      ++ "`code` widgets on a panel background — every code sample on "
      ++ "this page is built from it.") ]
```

- [ ] **Step 3: Rebuild `ref-containers-body`**

Current:
```koka
fun ref-containers-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ code-block([
      "box(child, padding, bg, on-click)",
      "row([..]) / column([..], gap, fill)",
      "stack([(x,y,child), ..])         // absolute",
      "scroll(child, name)              // scrollable viewport",
      "expanded(child, flex)            // flex-grow",
      "center(child, max-width)",
    ]) ]
```
New:
```koka
fun ref-containers-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("box", ["box(child, padding = 0.0, bg = Nothing, on-click = Nothing)"],
      "A single child on a padded surface. `padding` adds space around the "
      ++ "child; `bg` fills the box (pass Nothing for no background at "
      ++ "all, which is what most layout-only boxes want). Reach for `box` "
      ++ "when you need padding or a background around one thing; reach "
      ++ "for `row`/`column` once you have more than one child.",
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
                    text("right", 14.0, theme.fg)], gap = 8.0), width = Just(200.0))))),

    api-entry("stack", ["stack([(x, y, child), ..])"],
      "Children at absolute (x, y) offsets within the space the parent "
      ++ "gives the stack — for overlapping content (a badge on a corner, "
      ++ "a label over an image) that `row`/`column` can't express, since "
      ++ "those only place children next to each other.",
      demo = Just(demo-panel(
        ["stack([",
         "  (0.0, 0.0, rect(80.0, 40.0, bg = Just(Fill(theme.surface, 6.0)))),",
         "  (10.0, 10.0, text(\"on top\", 13.0, theme.fg)),",
         "])"],
        fixed(stack([
          (0.0, 0.0, rect(80.0, 40.0, bg = Just(Fill(theme.surface, 6.0)))),
          (10.0, 10.0, text("on top", 13.0, theme.fg)),
        ]), width = Just(120.0))))),

    api-entry("scroll", ["scroll(child, name = \"\", horizontal = False)"],
      "Makes `child` scrollable along one axis once it's bigger than the "
      ++ "space `scroll` is given — pair it with `expanded` in a fixed-"
      ++ "height parent (see `expanded` below), or the scroll region "
      ++ "shrink-wraps to its content instead of clipping. `name` lets a "
      ++ "sibling read or set the scroll offset (`scroll-state`, "
      ++ "`scroll-to`). No live demo here that isn't already on the page: "
      ++ "every code block is `scroll(..., horizontal = True)` — try "
      ++ "panning one sideways.",
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
      demo = Nothing) ]
```

- [ ] **Step 4: Rebuild `ref-interactive-body`**

Current:
```koka
fun ref-interactive-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ code-block([
      "primary-button(label, msg)       // themed",
      "text-input(value, on-input)",
      "slider(value, on-change, lo, hi)",
      "link(route-path, child)          // real <a> on web",
    ]) ]
```
New:
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
      ++ "animation via `act`, the lower-level primitive `primary-button` "
      ++ "and `quiet-button` are themselves built on:",
      demo = Just(demo-panel(
        ["act( box(text(\"Try me\", 16.0, on-accent), padding = 9.0,",
         "         bg = Just(Fill(theme.accent, 6.0))), on )"],
        demo-button("Try me", fn() (), here())))),

    api-entry("text-input", ["text-input(value, on-input : string -> msg, placeholder = \"\", width = 220.0)"],
      "A single-line editable field. `on-input` fires with the field's "
      ++ "current text on every keystroke, so the app model always holds "
      ++ "the live value (a CONTROLLED input, in React terms). No live "
      ++ "demo here: `on-input` needs an app message this page doesn't "
      ++ "have. See `field` in the async/forms reference for an "
      ++ "UNCONTROLLED alternative whose value lives in ui/state instead "
      ++ "of the model.",
      demo = Nothing),

    api-entry("slider", ["slider(value, on-change : float64 -> msg, lo = 0.0, hi = 1.0, step = 0.0)"],
      "A horizontal slider over `[lo, hi]`, snapped to `step` (0.0 means "
      ++ "no snapping). Like `text-input`, `on-change` needs an app "
      ++ "message this page doesn't have, so there's no live `slider` "
      ++ "demo — but the Live sample section below shows the same idea "
      ++ "(a value driving an animated bar) via plain buttons and "
      ++ "ephemeral state instead.",
      demo = Nothing),

    api-entry("link", ["link(route-path, child)"],
      "Wraps `child` in a navigation target for `route-path` (no leading "
      ++ "'#') — a real `<a href=\"#/...\">` on the web (right-click, "
      ++ "open-in-new-tab, and deep-linking all work), a click target the "
      ++ "router handles the same way natively. `link` takes no message "
      ++ "of its own, which is why it — unlike the three buttons above — "
      ++ "can appear directly on this message-agnostic reference page. "
      ++ "The sidebar you're using right now is built from it, and so is "
      ++ "this:",
      demo = Just(demo-panel(
        ["link(\"howto-layout\", accented(\"Go to the layout how-to\", 15.0))"],
        link("howto-layout", accented("Go to the layout how-to", 15.0))))) ]
```

- [ ] **Step 5: Typecheck**

```bash
cd samples/ui/site
impdir=/Users/timwhiting/koka/.worktrees/koka-clang-wasm/lib/ui/api/impeller
sdk=$impdir/sdk
$KOKA --console=raw -i. -i../../../lib -c main.kk \
  "--ccopts=-I$sdk/include -I$impdir" \
  "--cclib=impeller;impellerhost" \
  "--cclinkopts=-L$sdk/lib -L$impdir -Wl,-rpath,$sdk/lib -Wl,-rpath,$impdir"
```
Fix any type errors before continuing — the demos above are new combinations
of existing widgets and may need small adjustments (e.g. an explicit `?key`
if two demos on one section collide, per the existing `here()`/source-line
identity idiom already used throughout this file).

- [ ] **Step 6: Run the smoke suite (Global Constraints command)**

Expected: `SMOKE: 16/16 passed`.

- [ ] **Step 7: Verify no banned words crept in**

```bash
sed -n '/^fun ref-/,/^fun expl-backends-body/p' samples/ui/site/pages.kk | grep -n "portable\|powerful\|elegant\|simply"
```
Expected: no output.

- [ ] **Step 8: Manually verify in a browser** (per this project's UI-change
  norm — type checking and the smoke suite verify structure, not that the
  new demos render correctly)

```bash
cd samples/ui/site
$KOKA --console=raw -i../../../lib -e build.kk
PATH="/Users/timwhiting/koka/.worktrees/koka-clang-wasm/.stack-work/install/aarch64-osx/f85b4dc81f126d06881fec188dc62cdb96d6f54b1fd1f1051955dc1d51fe411a/9.10.3/bin:$PATH" \
  ./.koka/v3.2.7/clang-debug-*/build__main jsweb
(cd out-js && python3 -m http.server 8123 &)
```
Open `http://localhost:8123/#/reference-widgets` and confirm: the box,
row/spacer, and stack demos render as described; the "Try me" button
animates on click; the link at the bottom of Interactive navigates to the
how-to page.

- [ ] **Step 9: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: reference-widgets rebuilt to the depth standard (params, vs.-notes, demos)"
```

---

### Task 5: Explanation — "One core, three backends"

**Files:**
- Modify: `samples/ui/site/pages.kk:184-199` (`expl-backends-body`,
  `expl-style-body`, `expl-state-body`, `expl-reconcile-body`) and the
  `explanation-one-core` `Doc-page`'s `intro` string.

**Interfaces:**
- Consumes: `prose` (blocks.kk, unchanged).
- Produces: nothing new — same functions, same signatures.

This page is where internals talk belongs (Rule 3), so the fix here is
narrower than Task 4: drop the one banned adjective, and re-ground the two
paragraphs that assert an outcome the reader can't check on this page in the
*mechanism* instead (Rule 1) — not a rewrite from scratch.

- [ ] **Step 1: Replace the explanation page's `Doc-page` intro**

Current:
```koka
      "The portable core is ui/widget: a data type of widgets and a layout "
      ++ "pass that turns them into a laid-out tree (ltree). Nothing in the "
      ++ "core knows about the DOM or Impeller.",
```
New:
```koka
      "ui/widget is the core: a data type of widgets, and a layout pass "
      ++ "that turns them into a laid-out tree (ltree). Nothing in that "
      ++ "core knows about the DOM or Impeller — backends are a separate, "
      ++ "later step, covered below.",
```

- [ ] **Step 2: Re-ground `expl-backends-body` in mechanism**

Current:
```koka
fun expl-backends-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("The web backend lowers the laid-out tree to absolutely-positioned "
          ++ "DOM; the native backend paints it with Impeller. Text measurement "
          ++ "is an ambient effect each backend installs, so layout runs "
          ++ "identically everywhere.") ]
```
New:
```koka
fun expl-backends-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("The web backend lowers the laid-out tree to absolutely-"
          ++ "positioned DOM; the native backend paints it with Impeller. "
          ++ "Text measurement — the one thing layout can't do without "
          ++ "asking a backend how wide a string actually is — is an "
          ++ "ambient effect each backend installs beneath layout, rather "
          ++ "than layout hard-coding one backend's font metrics. That's "
          ++ "the seam: the layout pass calls the same effect either "
          ++ "way, and never branches on which backend is running.") ]
```

- [ ] **Step 3: Re-ground `expl-style-body` in mechanism**

Current:
```koka
fun expl-style-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("The core is style-agnostic (typed colors only). ui/style/default is "
          ++ "one design language; ui/style/material is another (Material 3). "
          ++ "Swapping the import swaps the look -- same call shapes.") ]
```
New:
```koka
fun expl-style-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("The core only knows typed colors, not a design system — style "
          ++ "lives behind one ambient `theme` effect that components "
          ++ "read from, instead of being threaded as a parameter through "
          ++ "every call. `ui/style/default` and `ui/style/material` "
          ++ "(Material 3) each install a different `theme`: same "
          ++ "component names, same call shapes, different palette and "
          ++ "shapes underneath.") ]
```

- [ ] **Step 4: Trim `expl-state-body`**

Current:
```koka
fun expl-state-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("Hover, press, expand/collapse, and animation are EPHEMERAL, not app "
          ++ "state. ui/state keeps them keyed by widget identity, so a component "
          ++ "owns its transient UI without polluting the model -- which is how "
          ++ "the live counters on these pages work.") ]
```
New:
```koka
fun expl-state-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("Hover, press, expand/collapse, and animation are EPHEMERAL, not "
          ++ "app state. ui/state keeps them keyed by widget identity, so "
          ++ "a component owns its transient UI without the app model "
          ++ "needing to track it — which is how the live counters "
          ++ "scattered across this site work.") ]
```
(Already Rule-1-compliant — this step only removes "polluting", a loaded
word not on the banned list but inconsistent with the neutral, mechanism-
first tone the rest of this pass establishes. If the implementer judges the
original wording fine as-is, skip this step and note why in the task
report; it is not a blocking requirement the way Steps 1-3 and 5 are.)

- [ ] **Step 5: Re-ground `expl-reconcile-body`, drop the unreceipted outcome claim**

Current:
```koka
fun expl-reconcile-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("Re-renders reconcile the new tree against the retained one, reusing "
          ++ "node cells in place (FBIP) where shapes line up -- so a small "
          ++ "change touches little memory.") ]
```
New:
```koka
fun expl-reconcile-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("Re-renders reconcile the new tree against the retained one, "
          ++ "reusing node cells in place (a technique called FBIP — "
          ++ "functional but in place) wherever the new tree's shape "
          ++ "lines up with the old one, instead of discarding everything "
          ++ "and rebuilding from scratch.") ]
```
(The dropped clause — "so a small change touches little memory" — asserted
an outcome this page doesn't demonstrate to the reader; the mechanism
sentence that remains is the receipted part of the original claim.)

- [ ] **Step 6: Typecheck**

```bash
cd samples/ui/site
impdir=/Users/timwhiting/koka/.worktrees/koka-clang-wasm/lib/ui/api/impeller
sdk=$impdir/sdk
$KOKA --console=raw -i. -i../../../lib -c main.kk \
  "--ccopts=-I$sdk/include -I$impdir" \
  "--cclib=impeller;impellerhost" \
  "--cclinkopts=-L$sdk/lib -L$impdir -Wl,-rpath,$sdk/lib -Wl,-rpath,$impdir"
```

- [ ] **Step 7: Run the smoke suite (Global Constraints command)**

Expected: `SMOKE: 16/16 passed`.

- [ ] **Step 8: Verify no banned words remain**

```bash
sed -n '/^fun expl-/,/^\/\/ ---- the pages/p' samples/ui/site/pages.kk | grep -n "portable\|powerful\|elegant\|simply"
```
Expected: no output.

- [ ] **Step 9: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: explanation-one-core grounds its claims in mechanism, drops one adjective"
```

---

## Final check (after all 5 tasks)

- [ ] Confirm no banned words remain anywhere in the file:

```bash
grep -n "portable, declarative\|\bportable\b\|\bpowerful\b\|\belegant\b\|\bsimply\b" samples/ui/site/pages.kk
```
Expected: no output. ("portable" may legitimately appear in a future page
describing e.g. `ui/transform` matrices in a receipted, specific way — this
check is scoped to `pages.kk` as it exists after this plan, not a
permanent ban on the word everywhere in the codebase.)

- [ ] Run the full smoke suite one more time (Global Constraints command):
  expect `SMOKE: 16/16 passed`.
- [ ] Run the anchor-scroll and existing headless UI suites to confirm no
  regression outside the docs site (unaffected by this plan, but cheap to
  confirm):

```bash
cd /Users/timwhiting/koka/.worktrees/koka-clang-wasm
KOKA=.stack-work/install/aarch64-osx/f85b4dc81f126d06881fec188dc62cdb96d6f54b1fd1f1051955dc1d51fe411a/9.10.3/bin/koka
$KOKA --console=raw -O1 -ilib -itest/ui -e test/ui/anchor-scroll.kk
```
Expected: `ui/test: scroll-to-anchor: 7 checks passed`.
