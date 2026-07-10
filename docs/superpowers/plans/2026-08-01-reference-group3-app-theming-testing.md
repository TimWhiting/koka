# Reference Pages Group 3 (App & routing / Theming / Testing) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the final 3 reference pages for IA topics 7-9 (App & routing,
Theming & styled components, Testing your app) — completing all 9 reference
topics from the IA spec.

**Architecture:** Same content model as Groups 1-2 — `doc-page`/
`doc-section`/`api-entry`/`demo-panel`, no code changes to `model.kk`/
`blocks.kk`. Three tasks, one per page, each independent.

**Tech Stack:** Koka, `lib/ui`, `samples/ui/site`.

## Global Constraints

Same four rules and reference-depth standard as Groups 1-2 (content style
guide, `docs/superpowers/specs/2026-07-31-docs-site-content-style-design.md`,
required reading for every task brief):

- **Rule 1** — no claim without a same-page receipt (or mechanism-grounded
  where a demo isn't achievable).
- **Rule 2** — task-first section/page intros.
- **Rule 3** — internals stay off reference pages. This matters more on
  this group's pages than any prior one: the IA spec's own exclusion line
  says runtime plumbing and backend/harness walks are OUT — document what
  an APP AUTHOR calls, not how the runtime implements it underneath.
- **Rule 4** — banned words: "portable" (bare adjective), "powerful",
  "elegant", "simply".
- **Depth standard** — every `api-entry`: signature, a paragraph naming
  behavior + non-obvious parameters, a "vs." note where a nearby
  alternative exists, a live demo unless truly not achievable.

**FACT-CHECK EVERY CLAIM BEFORE WRITING IT DOWN.** Every task in this
rollout so far (6 of 6 across Groups 1-2) has shipped at least one
plausible-sounding claim that turned out to be factually wrong when
checked against source or tested in a browser — including claims the
controller itself wrote into a plan's brief text. This is not a rare
mistake to guard against; it is the DEFAULT failure mode for this kind of
writing. Before committing any sentence that asserts what a function does,
what it's built on, or what another entry says, open the actual source
file and confirm it — do not rely on the general shape of similar APIs or
on memory of how something "probably" works.

**Most of this group's content cannot have live demos** — `app`, `window`,
router subscriptions, and `test-scenarios` are whole-app-shell constructs
this message-agnostic reference page format cannot embed live. That's
expected and fine: ground every one of these in mechanism, and where
something the site itself already demonstrates (routing, the header
theme toggle) applies, point at it as the receipt — but ONLY where it's
genuinely, verifiably true (see the fact-check requirement above).

**Do not re-document primitives already covered on earlier pages.** `link`
(interaction reference), `ripple`/`interactive` (paint/interaction
references), `theme` as an ambient effect concept (mentioned briefly on
the interaction reference's button entries) — cross-reference rather than
repeat.

**No forward references to pages that don't exist yet.** Currently live
after Groups 1-2: `home`, `tutorial-first-app`, `howto-layout`,
`reference-widgets`, `reference-text-content`, `reference-interaction`,
`reference-paint-effects`, `reference-state-animation`, `reference-async`.
This plan adds `reference-app-routing`, `reference-theming`,
`reference-testing` — the last 3 reference pages; there is no "next" page
after `reference-testing` within `QReference` for this plan's scope (that
changes only once explanation/how-to/tutorial pages, or a shell-spec pass,
add navigation elsewhere — out of scope here).

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

Do not assert a specific `SMOKE: N/N` — report whatever N prints, confirm
zero `FAIL` lines.

**Typecheck command** (same flags, `-c main.kk` instead of `-e smoke.kk`):

```bash
$KOKA --console=raw -i. -i../../../lib -c main.kk \
  "--ccopts=-I$sdk/include -I$impdir" "--cclib=impeller;impellerhost" \
  "--cclinkopts=-L$sdk/lib -L$impdir -Wl,-rpath,$sdk/lib -Wl,-rpath,$impdir"
```

**Demo-panel width discipline** (hit repeatedly in Groups 1-2): `demo-
panel`'s code half shrink-wraps via `intrinsic-width`. Keep every demo's
code sample lines well under 60 characters — this has been the actual
overflow driver every time, more often than the `fixed(width=...)` value
itself. This group has FEWER live demos than prior groups (most entries
are `demo = Nothing`), so this applies to fewer entries, but still applies
wherever a demo exists.

---

### Task 1: Reference — App & routing (new page)

**Files:**
- Modify: `samples/ui/site/pages.kk` — add `ref-app-routing-body`, add the
  new `Doc-page` entry.

**Interfaces:**
- Consumes: `api-entry`, `demo-panel` (blocks.kk); `app`, `App-config`
  (lib/ui/app.kk, lib/ui/widget.kk — exact signatures below); `window`,
  `compose` (lib/ui/view.kk); `route-sub`, `anchor-route-sub`, `navigate`,
  `route/link`, `split-fragment` (lib/ui/router.kk).
- Produces: `ref-app-routing-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>`.

- [ ] **Step 1: Write `ref-app-routing-body`, 6 entries**

```koka
fun ref-app-routing-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("app", ["app(init, view, update, config = App-config(),",
                       "    subs = [], threads = Single)"],
      "The entry point: runs the model/update/view loop until the window "
      ++ "closes. `init` is the starting model; `view`/`update` are your "
      ++ "app's two pure functions. `subs` are background subscriptions "
      ++ "(below); `threads = Threaded` moves layout/paint off the "
      ++ "input-handling thread on platforms that support OS threads "
      ++ "(falls back to `Single` where they don't, e.g. web). No live "
      ++ "demo here: `app` IS the whole running program, not a widget — "
      ++ "you're inside one right now, reading this page.",
      demo = Nothing),

    api-entry("app-config", ["App-config(title = \"Koka UI\", width = 480,",
                              "           height = 360, root-id = \"app\")"],
      "The window/canvas settings `app` reads: `title` and `width`/"
      ++ "`height` for a native window; `root-id` for the DOM element the "
      ++ "web backend mounts into. Every field has a default, so most "
      ++ "apps only override `title` and a starting size.",
      demo = Nothing),

    api-entry("subs", ["subs : list<(channel<msg>) -> <async,ioc> ()>"],
      "Background tasks `app` runs alongside the render loop, each with a "
      ++ "channel to post messages back through — a timer, a websocket "
      ++ "listener, or (the case every app with routing needs) the "
      ++ "router's own hash-change listener. This site's `app` call "
      ++ "passes exactly one sub: `anchor-route-sub`, below.",
      demo = Nothing),

    api-entry("route-sub, anchor-route-sub", ["route-sub(ch, parse, to-msg)",
                                               "anchor-route-sub(ch, parse, to-msg)"],
      "A `subs` entry that turns the URL hash into route messages: "
      ++ "`parse` reads the hash path into your route type, `to-msg` "
      ++ "wraps it as an app message. `anchor-route-sub` is `route-sub` "
      ++ "plus fragment handling — `page#slug` splits into a route change "
      ++ "AND a `scroll-to(slug)` (state & animation reference), so a "
      ++ "hash like `#/reference-testing#test-scenarios` both navigates "
      ++ "and scrolls to that heading. This site uses `anchor-route-sub` "
      ++ "for exactly that reason — every cross-page anchor link on this "
      ++ "site depends on it.",
      demo = Nothing),

    api-entry("navigate, route/link, split-fragment", ["navigate(print, route)",
                                                         "route/link(route, print, child)",
                                                         "split-fragment(path)   // -> (page, maybe<slug>)"],
      "`navigate` pushes a route programmatically (from `update`, in "
      ++ "response to a message); `route/link` is `link` (interaction "
      ++ "reference) typed to a route value instead of a raw path string "
      ++ "— pass it your route and its `print` function instead of "
      ++ "building the path yourself. `split-fragment` is the parsing "
      ++ "half `anchor-route-sub` uses internally to separate the page "
      ++ "path from an optional `#slug`.",
      demo = Nothing),

    api-entry("window, compose (multi-window)", ["window(key, content, title,",
                                                   "       width = 480.0, height = 360.0)"],
      "`window` opens a second, OS-level titled window showing `content` "
      ++ "— call it from `view` like any other emitted overlay (closing "
      ++ "it, via the OS close button, is reported through `on-dismiss`). "
      ++ "Under the hood, every open window/overlay is composited "
      ++ "together each frame — that compositing is backend/harness "
      ++ "machinery, not something you call directly, so it isn't "
      ++ "documented as its own entry here. No live demo: a second OS "
      ++ "window can't be shown inside this page's own layout.",
      demo = Nothing) ]
```

- [ ] **Step 2: Add the `Doc-page` entry**

```koka
    Doc-page(QReference, "reference-app-routing", "Reference: app & routing",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. The entry point every "
      ++ "app starts from, and the router that turns URL hashes into "
      ++ "route messages.",
      [ Doc-section("App and routing", ref-app-routing-body) ]),
```

Add it to `site-pages<a>()`'s list in `QReference` order right after
`reference-async` (the last page from Group 2).

- [ ] **Step 3: Typecheck**

Run the Global Constraints typecheck command. Fix any errors before
continuing — treat the snippets above as an accurate starting point, not
gospel.

- [ ] **Step 4: Run the smoke suite**

Run the Global Constraints smoke command. Report the printed `SMOKE: N/N`
and confirm zero `FAIL` lines.

- [ ] **Step 5: Fact-check every claim against source before considering
  this done**

For each of the 6 entries above, re-read the corresponding source
(`lib/ui/app.kk` for `app`/`app-config`/`subs`; `lib/ui/router.kk` for
`route-sub`/`anchor-route-sub`/`navigate`/`route/link`/`split-fragment`;
`lib/ui/view.kk` for `window`/`compose`) and confirm every claim in the
entry's prose is literally true — parameter names, defaults, what calls
what. This step is not optional busywork: every prior task in this
rollout shipped at least one wrong claim its own writer believed was
accurate.

- [ ] **Step 6: Manually verify in a browser at 900px width**

Build for jsweb, serve, navigate to `#/reference-app-routing`. Confirm
nothing overflows past 900px (this page has no `fixed`-wrapped demos, so
this should mostly be about the code-blocks' own width, not a live-widget
overflow — but verify anyway).

- [ ] **Step 7: Verify no banned words**

```bash
grep -n "portable\|powerful\|elegant\|simply" samples/ui/site/pages.kk
```
Expected: no output.

- [ ] **Step 8: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: reference-app-routing -- new page for topic 7 (app & routing)"
```

---

### Task 2: Reference — Theming (new page)

**Files:**
- Modify: `samples/ui/site/pages.kk` — add `ref-theming-body`, add the new
  `Doc-page` entry.

**Interfaces:**
- Consumes: `api-entry`, `demo-panel` (blocks.kk); `theme` effect,
  `palette`, `theme/light`, `theme/dark`, `palette/mix` (lib/ui/style/
  default/theme.kk — all signatures below already verified against this
  file); `page`, `card`, `body`, `accented`, `expander`, `dropdown`,
  `context-menu` (lib/ui/style/default/components.kk, likewise verified);
  `button-style`, `styled-paint` (lib/ui/style/base.kk).
- Produces: `ref-theming-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>`.

- [ ] **Step 1: Write `ref-theming-body`, 6 entries**

```koka
fun ref-theming-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("theme (the ambient effect)", ["effect val theme : palette",
                                              "theme/light, theme/dark : palette",
                                              "palette/mix(a, b, t)"],
      "Every themed component in this reference (and every one on this "
      ++ "site) reads colors from `theme` — an AMBIENT reader effect, not "
      ++ "a parameter threaded through every call. `light`/`dark` are the "
      ++ "two built-in palettes (`bg`/`fg`/`accent`/`surface`), qualified "
      ++ "as `theme/light`/`theme/dark` wherever a bare `light`/`dark` "
      ++ "would be ambiguous; `palette/mix` blends them by fraction `t`, "
      ++ "which is exactly how this site's own Light/Dark toggle works — "
      ++ "this page's own `view` animates a `t` and binds "
      ++ "`with val theme = theme/light.mix(theme/dark, t)` around the "
      ++ "whole page (verified: `samples/ui/site/main.kk`), so every "
      ++ "themed widget crossfades together instead of snapping.",
      demo = Just(demo-panel(
        ["rect(50.0, 30.0, bg = Just(Fill(theme/light.accent, 4.0)))",
         "rect(50.0, 30.0, bg = Just(Fill(theme/dark.accent, 4.0)))"],
        fixed(row([
          rect(50.0, 30.0, bg = Just(Fill(theme/light.accent, 4.0))),
          rect(50.0, 30.0, bg = Just(Fill(theme/dark.accent, 4.0))),
        ], gap = 8.0), width = Just(120.0))))),

    api-entry("page, card, body, accented", ["page(title, children, gap = 14.0, scroll = True)",
                                              "card(child, padding = 14.0)",
                                              "body(content, size = 15.0)",
                                              "accented(content, size = 15.0)"],
      "The structural/typography building blocks: `page` is a heading "
      ++ "over a scrolling column of content — this whole site's shell "
      ++ "is one; `card` is a single child on the theme's raised surface "
      ++ "color; `body` is wrapping prose text in the theme's foreground "
      ++ "color, `accented` the same but in the accent color. All four "
      ++ "are already in use throughout this site: every demo on the "
      ++ "layout reference sits in a `card`, and this sentence itself is "
      ++ "a `body`.",
      demo = Nothing),

    api-entry("expander", ["expander(title, body, key)"],
      "A collapsible section: clicking the header toggles `body` in or "
      ++ "out. Its open/closed state is ephemeral `ui/state` (state & "
      ++ "animation reference), keyed by the REQUIRED `key` parameter — "
      ++ "not `?key`, a plain positional `key` the caller must mint "
      ++ "(`expander(\"Files\", tree, here())`), so forgetting it is a "
      ++ "type error rather than a silent identity collision. Unlike "
      ++ "`dropdown`/`context-menu` below, `expander` takes no app "
      ++ "message at all — its toggle is pure `act`-style ephemeral "
      ++ "state — so it's the one component on this page that CAN "
      ++ "appear live:",
      demo = Just(demo-panel(
        ["expander(\"Details\",",
         "  text(\"the hidden content\", 14.0, theme.fg),",
         "  here())"],
        expander("Details", text("the hidden content", 14.0, theme.fg), here())))),

    api-entry("dropdown, context-menu", ["dropdown(label, items, on-open : msg)",
                                          "context-menu(items : list<(string, msg)>)"],
      "`context-menu` is a raised surface holding a column of "
      ++ "`(label, message)` rows, meant to be floated at a point with "
      ++ "`ui/overlay`'s `popup`; `dropdown` is just the TRIGGER button "
      ++ "for one — clicking it emits `on-open`, and the app responds by "
      ++ "floating a `context-menu` itself (the open/closed state is app "
      ++ "state, not something these components own). Both need an app "
      ++ "message this page doesn't have — same constraint the "
      ++ "interaction reference's `primary-button` entry explains. "
      ++ "Unlike `expander` above, there's no ephemeral-state escape "
      ++ "hatch here, since opening a menu is a real navigation the app "
      ++ "needs to know about.",
      demo = Nothing),

    api-entry("ui/style/material", [],
      "A second, sibling style library over the same style-agnostic "
      ++ "`ui/widget` core, NOT a call-compatible drop-in for "
      ++ "`ui/style/default`: it has its own separate `theme` effect "
      ++ "(over a `material-theme` record, not `palette`) and its own "
      ++ "button vocabulary (`filled-button`, `elevated-button`, "
      ++ "`filled-tonal-button`, `text-button` — Material 3's set, not "
      ++ "`primary-button`/`quiet-button`). What the two libraries DO "
      ++ "share is the mechanism underneath: `button-style`/"
      ++ "`styled-paint` (below) power both libraries' buttons, so "
      ++ "adopting `ui/style/material` means learning its own component "
      ++ "names, not swapping one import line. No live demo here: "
      ++ "showing both libraries side by side needs two independent "
      ++ "theme scopes this page doesn't have.",
      demo = Nothing),

    api-entry("button-style, styled-paint", ["button-style(bg, fg, hover, pressed,",
                                              "             radius = 20.0, padding = 12.0)",
                                              "styled-paint(style)"],
      "The custom-style escape hatch, for a button that doesn't fit "
      ++ "`primary-button`/`quiet-button`'s two built-in looks: "
      ++ "`button-style` is a plain data record (fill color at rest, "
      ++ "text color, and two more fills for hover/pressed); "
      ++ "`styled-paint(style)` turns that record into the paint "
      ++ "function `interactive`'s `build` callback takes, picking the "
      ++ "right fill by the LIVE interaction state. No live demo here: "
      ++ "needs `interactive`, the same message constraint every "
      ++ "interactive-primitive entry on this site runs into.",
      demo = Nothing) ]
```

- [ ] **Step 2: Add the `Doc-page` entry**

```koka
    Doc-page(QReference, "reference-theming", "Reference: theming",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. The ambient effect "
      ++ "every themed component reads from, the default component "
      ++ "library, and how to swap in a different look or build your "
      ++ "own.",
      [ Doc-section("Theming", ref-theming-body) ]),
```

Add it right after `reference-app-routing` in `QReference` order.

- [ ] **Step 4: Typecheck**

Run the Global Constraints typecheck command. Fix any errors before
continuing.

- [ ] **Step 5: Run the smoke suite**

Run the Global Constraints smoke command. Report the printed `SMOKE: N/N`
and confirm zero `FAIL` lines.

- [ ] **Step 6: Fact-check every claim against source**

Re-verify every signature and behavioral claim against `lib/ui/style/
default/theme.kk`, `lib/ui/style/default/components.kk`, and `lib/ui/
style/base.kk` — same discipline as Task 1's Step 5. Pay particular
attention to the `theme/light.mix(theme/dark, t)`-in-`main.kk` claim
(already verified once while drafting this plan — `samples/ui/site/
main.kk:135` — but re-confirm it wasn't broken by anything landed since)
and the `ui/style/material` "same names" claim — the latter was NOT
independently verified against `lib/ui/style/material/components.kk`
while drafting this plan and must be checked before this task is done.

- [ ] **Step 7: Manually verify in a browser at 900px width**

Build for jsweb, serve, navigate to `#/reference-theming`. Confirm the
`theme/light`/`theme/dark` swatch demo renders visibly different colors
for each palette, the `expander` demo actually toggles its body open and
closed on click, and nothing overflows past 900px.

- [ ] **Step 8: Verify no banned words**

```bash
grep -n "portable\|powerful\|elegant\|simply" samples/ui/site/pages.kk
```
Expected: no output.

- [ ] **Step 9: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: reference-theming -- new page for topic 8 (theming & styled components)"
```

---

### Task 3: Reference — Testing your app (new page)

**Files:**
- Modify: `samples/ui/site/pages.kk` — add `ref-testing-body`, add the new
  `Doc-page` entry.

**Interfaces:**
- Consumes: `api-entry`, `demo-panel` (blocks.kk); `test-scenarios`,
  `tester`, `find`, `click`, `click-at`, `type-text`, `press-key`,
  `hover`, `scroll` (the tester method), `settle`, `texts`, `check-eq`
  (lib/ui/test.kk, exact signatures below).
- Produces: `ref-testing-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>`.

- [ ] **Step 1: Write `ref-testing-body`, 4 entries**

```koka
fun ref-testing-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("test-scenarios", ["test-scenarios(name, init, view, update, scenarios,",
                                  "               config = App-config())"],
      "Runs your app headlessly against a list of named scenarios — each "
      ++ "one a function taking a `tester` and asserting against what the "
      ++ "app actually shows, not its internal model. This is how every "
      ++ "regression check across `lib/ui` and this site itself is "
      ++ "written; the site you're reading this on has its own smoke "
      ++ "suite built exactly this way. No live demo here: `test-"
      ++ "scenarios` runs a WHOLE separate app instance headlessly, not "
      ++ "something embeddable inside a reference page's own live app.",
      demo = Nothing),

    api-entry("tester ops: click, find, type-text, hover, scroll",
      ["t.click(selector)", "t.find(selector)   // -> maybe<(x,y,w,h)>",
       "t.type-text(selector, text)", "t.hover(selector)",
       "t.scroll(selector, dy)"],
      "The actions a scenario drives the app with, each addressing a "
      ++ "widget by a SELECTOR string (below) rather than a pixel "
      ++ "coordinate — `click`/`hover` find the selector's target and act "
      ++ "on its center; `type-text` focuses a field first; `find` "
      ++ "returns the target's laid-out rect (or `Nothing` if nothing "
      ++ "matches, or it's scrolled out of view) for assertions that need "
      ++ "geometry rather than just presence.",
      demo = Nothing),

    api-entry("settle, texts, check-eq", ["t.settle()", "t.texts(selector = \"\")",
                                           "check-eq(label, actual, expected)"],
      "`settle` drains pending async work and re-renders until the app "
      ++ "is quiet — call it after any action before asserting, so a "
      ++ "scenario isn't racing an animation or an async load. `texts` "
      ++ "reads back all visible text inside a selector's subtree (empty "
      ++ "selector = the whole app) — the assert-on-what-the-user-sees "
      ++ "idiom this page's title describes. `check-eq` is the assertion "
      ++ "itself: label, actual, expected, with a readable failure "
      ++ "message on mismatch.",
      demo = Nothing),

    api-entry("selector grammar, scenario patterns, and the live tier", [],
      "A selector matches a widget by its `?key` scope path — a plain "
      ++ "string like `\"nav-home\"` matches any widget keyed with that "
      ++ "scope, anywhere in the tree; ambiguous matches throw, naming "
      ++ "every match found, so a genuinely ambiguous selector fails "
      ++ "loudly instead of silently picking one. Write scenarios that "
      ++ "assert what a user would actually see (`t.texts(...)`, a "
      ++ "button's visible state) rather than reaching into the model — "
      ++ "the model is an implementation detail a scenario shouldn't "
      ++ "need to know about. Beyond the headless tier `test-scenarios` "
      ++ "runs by default, `lib/ui` also has a LIVE tier that drives a "
      ++ "real browser/window instead of the headless harness, for the "
      ++ "cases headless can't cover (real keystroke timing, actual "
      ++ "pixel rendering) — same scenario functions, a different "
      ++ "runner.",
      demo = Nothing) ]
```

Note: the "selector grammar" entry's claim about ambiguous selectors
throwing and naming every match is a specific, checkable behavior — verify
it against `lib/ui/test.kk`'s actual selector-resolution code (the
function that implements `find`/`click`'s selector lookup) before
committing, not just from this plan's description of it. The "live tier"
sentence is intentionally brief and general — do not invent specifics
about how the live tier works beyond what you can verify in
`test/ui/live/` or equivalent; if you can't verify a specific claim about
it, keep the sentence at the level of generality shown above rather than
adding unverified detail.

- [ ] **Step 2: Add the `Doc-page` entry**

```koka
    Doc-page(QReference, "reference-testing", "Reference: testing your app",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. How to test what you "
      ++ "build: headless scenarios that assert on what a user sees, not "
      ++ "on your model's internals.",
      [ Doc-section("Testing your app", ref-testing-body) ]),
```

Add it right after `reference-theming` in `QReference` order — this is
now the LAST reference page (all 9 topics complete).

- [ ] **Step 3: Typecheck**

Run the Global Constraints typecheck command. Fix any errors before
continuing.

- [ ] **Step 4: Run the smoke suite**

Run the Global Constraints smoke command. Report the printed `SMOKE: N/N`
and confirm zero `FAIL` lines.

- [ ] **Step 5: Fact-check every claim against source**

Re-verify every claim against `lib/ui/test.kk` directly — same discipline
as Tasks 1-2's fact-check steps. This page is documenting the TESTING
tool this whole rollout has used constantly; getting its own claims wrong
would be a particularly embarrassing instance of the pattern this
Global-Constraints section warns about.

- [ ] **Step 6: Manually verify in a browser at 900px width**

Build for jsweb, serve, navigate to `#/reference-testing`. Confirm nothing
overflows past 900px. This page has no live demos, so this step is mostly
confirming the code-blocks render cleanly.

- [ ] **Step 7: Verify no banned words**

```bash
grep -n "portable\|powerful\|elegant\|simply" samples/ui/site/pages.kk
```
Expected: no output.

- [ ] **Step 8: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: reference-testing -- new page for topic 9 (testing your app)"
```

---

## Final check (after all 3 tasks)

- [ ] Confirm no banned words remain anywhere in the file.
- [ ] Run the smoke suite one more time; confirm zero `FAIL` lines and
  note the final `SMOKE: N/N` count for the ledger.
- [ ] Confirm the sidebar's REFERENCE group now shows exactly 9 entries in
  order, matching the IA spec's 9 topics: Layout & containers, Text &
  content, Interaction, Paint & effects, State & animation, Async, App &
  routing, Theming, Testing your app.
- [ ] Confirm `next-prev-links` chains correctly across all 9 reference
  pages (Layout & containers has no prev, Testing your app has no next).
- [ ] Full fact-check sweep: with all 9 reference pages now complete, read
  every cross-page reference on these 3 new pages one more time and
  confirm each still resolves to something real (a real entry, a real
  section, a real receipted behavior) now that the full reference section
  exists — this is the last chance to catch a stale or wrong pointer
  before the entire reference section is considered done.
