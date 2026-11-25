# Reference Pages Group 2 (Paint & effects / State & animation / Async) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build 3 new reference pages for IA topics 4-6 (Paint & effects,
State & animation, Async), continuing the rollout Group 1 established.

**Architecture:** Same content model as Group 1 — `doc-page`/`doc-section`/
`api-entry`/`demo-panel`, no code changes to `model.kk`/`blocks.kk`. Three
tasks, one per page, each independent (no page depends on another's
content existing first, only on `pages.kk`'s shared helpers like
`demo-button`/`live-progress` already being defined earlier in the file,
which they are).

**Tech Stack:** Koka, `lib/ui`, `samples/ui/site`.

## Global Constraints

Same four rules and reference-depth standard as Group 1 (content style
guide, `docs/superpowers/specs/2026-07-31-docs-site-content-style-design.md`,
required reading for every task brief):

- **Rule 1** — no claim without a same-page receipt (or mechanism-grounded
  where a demo isn't achievable — say plainly why, never omit silently).
- **Rule 2** — task-first section/page intros.
- **Rule 3** — internals stay off reference pages.
- **Rule 4** — banned words: "portable" (bare adjective), "powerful",
  "elegant", "simply".
- **Depth standard** — every `api-entry`: signature, a paragraph naming
  behavior + non-obvious parameters, a "vs." note where a nearby
  alternative exists, a live demo unless truly not achievable.

**Lessons from Group 1's fix rounds** (four content-accuracy issues were
caught across per-task and final review — every one was a plausible-
sounding claim that didn't hold up when checked against source or tested
in a browser): before writing a claim about what a widget "is built on" or
"is the same mechanism as," verify it against the actual source file, not
from memory or pattern-matching to a similar widget. Before writing that a
demo "shows" some behavior, confirm the demo's actual code produces that
behavior (a no-op thunk doesn't "bump a counter" just because the prose
says it does).

**Do not re-document `image`/`image-path`** — Async's entry for it should
cross-reference the existing `reference-text-content` page's entry rather
than duplicate it (Rule 3's DRY spirit extends to not repeating full API
docs across pages).

**No forward references to pages that don't exist yet.** Currently live:
`home`, `tutorial-first-app`, `howto-layout`, `reference-widgets`,
`reference-text-content`, `reference-interaction`, `explanation-one-core`.
This plan adds `reference-paint-effects`, `reference-state-animation`,
`reference-async` (may reference each other once landed within this same
plan — Task 1 landing before Task 3 means Task 3 CAN reference Task 1's
page by then, but write each task assuming only the pages before it in
plan order exist, to keep tasks independently reviewable). Do not name
`reference-theming`, `reference-testing`, or any tutorial/how-to page not
in the live list above — those are future rollout steps.

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

**Demo-panel width discipline**: `demo-panel`'s code half shrink-wraps via
`intrinsic-width` (don't touch `blocks.kk`). Any `fixed(width = Just(N))`
wrapping a demo's LIVE half is a starting guess to verify in a browser at
900px, not a guaranteed-correct value.

---

### Task 1: Reference — Paint & effects (new page)

**Files:**
- Modify: `samples/ui/site/pages.kk` — add `ref-paint-body`, add the new
  `Doc-page` entry.

**Interfaces:**
- Consumes: `api-entry`, `demo-panel` (blocks.kk); `Fill`, `SLinear`,
  `SRadial`, `SImage`, `rgb`, `color/mix`, `brighten`, `color/contrasting`,
  `rotated`, `transform3d`, `ui/transform`'s matrix functions (lib/ui,
  unchanged — see each step for exact signatures); `ripple`
  (lib/ui/style/base.kk); `interactive` (lib/ui/state, already documented
  on `reference-interaction`).
- Produces: `ref-paint-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>`.

- [ ] **Step 1: Write `ref-paint-body`, 6 entries**

```koka
fun ref-paint-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("fill, paint-source", ["Fill(color, radius = 0.0, source = Nothing)",
                                      "SLinear(fx, fy, tx, ty, from-color, to-color)",
                                      "SRadial(cx, cy, radius, inner-color, outer-color)",
                                      "SImage(src, fit = Cover)"],
      "`Fill` is a surface fill: a solid `color` (the fallback), rounded by "
      ++ "`radius`, optionally overridden by a `source` — a gradient or an "
      ++ "image, native on both backends (an Impeller ColorSource, a CSS "
      ++ "background), never emulated. Every source's geometry is a "
      ++ "FRACTION of the box being filled — (0,0) top-left, (1,1) bottom-"
      ++ "right — so one source describes a small swatch and a full-bleed "
      ++ "header without knowing either's size.",
      demo = Just(demo-panel(
        ["rect(70.0, 40.0, bg = Just(Fill(theme.accent, 6.0,",
         "  source = Just(SLinear(0.0, 0.0, 1.0, 1.0, theme.accent, theme.surface)))))",
         "rect(70.0, 40.0, bg = Just(Fill(theme.accent, 6.0,",
         "  source = Just(SRadial(0.5, 0.5, 0.5, theme.accent, theme.surface)))))"],
        fixed(row([
          rect(70.0, 40.0, bg = Just(Fill(theme.accent, 6.0,
                 source = Just(SLinear(0.0, 0.0, 1.0, 1.0, theme.accent, theme.surface))))),
          rect(70.0, 40.0, bg = Just(Fill(theme.accent, 6.0,
                 source = Just(SRadial(0.5, 0.5, 0.5, theme.accent, theme.surface))))),
        ], gap = 8.0), width = Just(160.0))))),

    api-entry("color: rgb, mix, brighten, contrasting", ["rgb(r, g, b)   // 0.0..1.0 each",
                                                           "color/mix(x, y, t)",
                                                           "brighten(c, factor)",
                                                           "color/contrasting(c)"],
      "`rgb` builds a color from 0.0-1.0 channels. `mix` blends two colors "
      ++ "by fraction `t` — the theme crossfade this site's own light/dark "
      ++ "toggle uses. `brighten` multiplies channels by `factor` (clamped) "
      ++ "— the native hover/press affordance, mirroring CSS "
      ++ "`filter: brightness(...)`; `primary-button`/`quiet-button` "
      ++ "(interaction reference) use it for their press glow. "
      ++ "`contrasting` picks a readable foreground (near-black or near-"
      ++ "white) for an arbitrary background — how `on-accent` (used "
      ++ "throughout this site's own buttons) stays readable regardless of "
      ++ "the active theme's accent color.",
      demo = Just(demo-panel(
        ["rect(50.0, 30.0, bg = Just(Fill(brighten(theme.accent, 1.3))))"],
        rect(50.0, 30.0, bg = Just(Fill(brighten(theme.accent, 1.3))))))),

    api-entry("rotated", ["rotated(child, degrees)"],
      "Rotates `child`'s PAINT only, about its center — layout is "
      ++ "unchanged (the child keeps its laid-out rect, same as `clip`). "
      ++ "For a fixed decorative tilt; for something that turns in "
      ++ "response to interaction (a flip card, a spinner keyed to "
      ++ "progress), reach for `transform3d` below instead.",
      demo = Just(demo-panel(
        ["rotated(rect(50.0, 30.0, bg = Just(Fill(theme.accent, 4.0))), 15.0)"],
        rotated(rect(50.0, 30.0, bg = Just(Fill(theme.accent, 4.0))), 15.0)))),

    api-entry("transform3d", ["transform3d(child, m : mat4)"],
      "Applies a 4x4 matrix (`ui/transform`: `perspective`, `rotate-x`/"
      ++ "`-y`/`-z`, `translate3`, `scale3`, composed with `*`) to `child`'s "
      ++ "PAINT only, about its center — layout stays unchanged, like "
      ++ "`rotated` above but in 3D and composable. Hit-testing is "
      ++ "ACCURATE through the transform: a card tilted or flipped "
      ++ "hit-tests against its actual on-screen (projected) shape, not "
      ++ "its flat untransformed rect — this is the primitive a flip-card "
      ++ "or a tilt-on-hover effect is built from. No live demo here: a "
      ++ "3D flip needs press/click state this compact reference format "
      ++ "would need real app wiring to drive.",
      demo = Nothing),

    api-entry("ripple", ["ripple(content, pressed, radius = 6.0, tint = white,",
                          "       strength = 0.12, max-radius = 220.0)"],
      "A press ripple — a circle that grows from the press point and "
      ++ "fades, clipped to `content`'s bounds. `pressed` is the live "
      ++ "press state `interactive` (interaction reference) provides to "
      ++ "its `build` callback; the radius derives from the press "
      ++ "timestamp, not an eased cell, so consecutive presses each start "
      ++ "fresh from their own touch point instead of continuing from "
      ++ "wherever the last one ended. `primary-button`/`quiet-button` "
      ++ "(interaction reference) wrap every themed button in this. No "
      ++ "live demo here: like `interactive` itself, `ripple` needs "
      ++ "`on-click : msg` — an app message this page doesn't have (the "
      ++ "same constraint the `primary-button`/`quiet-button` entry on "
      ++ "the interaction reference explains). Click the Light/Dark "
      ++ "toggle in this page's own header for it in action — that's a "
      ++ "real `quiet-button`.",
      demo = Nothing) ]
```

- [ ] **Step 2: Add the `Doc-page` entry**

```koka
    Doc-page(QReference, "reference-paint-effects", "Reference: paint & effects",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. Fills, colors, and the "
      ++ "paint-only transforms: rotation, 3D, and the press ripple every "
      ++ "themed button uses.",
      [ Doc-section("Paint and effects", ref-paint-body) ]),
```

Add it to `site-pages<a>()`'s list in `QReference` order right after
`reference-interaction`.

- [ ] **Step 3: Typecheck**

Run the Global Constraints typecheck command. Fix any errors before
continuing — treat the snippets above as an accurate starting point, not
gospel; use the existing `scope("...")`/`here()` idioms for any identity
collisions.

- [ ] **Step 4: Run the smoke suite**

Run the Global Constraints smoke command. Report the printed `SMOKE: N/N`
and confirm zero `FAIL` lines.

- [ ] **Step 5: Manually verify in a browser at 900px width**

Build for jsweb, serve, navigate to `#/reference-paint-effects`. Confirm:
the fill-source swatches render a visible gradient (not a flat color); the
rotated rect is visibly tilted; clicking the ripple demo's button produces
a growing, fading circle (not a static button) — this is the one entry in
this task with real interactive behavior a typecheck can't verify. Confirm
nothing overflows past 900px.

- [ ] **Step 6: Verify no banned words**

```bash
grep -n "portable\|powerful\|elegant\|simply" samples/ui/site/pages.kk
```
Expected: no output.

- [ ] **Step 7: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: reference-paint-effects -- new page for topic 4 (paint & effects)"
```

---

### Task 2: Reference — State & animation (new page)

**Files:**
- Modify: `samples/ui/site/pages.kk` — add `ref-state-anim-body`, add the
  new `Doc-page` entry.

**Interfaces:**
- Consumes: `api-entry`, `demo-panel` (blocks.kk); `use-state`,
  `use-state-quiet`, `animate`, `animate-color`, `ease-in`, `ease-out`,
  `ease-in-out`, `set-time-dilation`, `scroll-state`, `set-scroll-offset`,
  `scroll-to`, `press-point`, `memo` (lib/ui/state.kk, exact signatures
  below); `live-progress` (existing helper in `pages.kk`, defined earlier
  in the file — reuse it directly, don't recreate its logic).
- Produces: `ref-state-anim-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>`.

- [ ] **Step 1: Write `ref-state-anim-body`, 7 entries**

```koka
fun ref-state-anim-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("use-state, use-state-quiet", ["use-state(init, name = \"\")   // (value, setter)",
                                              "use-state-quiet(init, name = \"\")"],
      "Ephemeral state keyed by call site — no app message, no model "
      ++ "field. `use-state` returns `(value, setter)`; calling the "
      ++ "setter re-renders. `use-state-quiet` is the same shape but its "
      ++ "write does NOT itself trigger a re-render — for state a caller "
      ++ "reads back on the SAME frame it wrote (like `animate`, below, "
      ++ "which retargets mid-build and reads its own write before the "
      ++ "frame is done), where a normal `use-state` write would cause an "
      ++ "extra, identical echo render. Reach for plain `use-state` unless "
      ++ "you have that specific reason not to — every live counter on "
      ++ "this site (this one included) uses it.",
      demo = Just(demo-panel(
        ["val (n, set) = use-state(0)",
         "row([",
         "  demo-button(\"−\", fn() set(fn(x) x - 1), here()),",
         "  text(n.show, 26.0, theme.fg),",
         "  demo-button(\"+\", fn() set(fn(x) x + 1), here()),",
         "], gap = 12.0)"],
        live-counter(here())))),

    api-entry("animate, animate-color", ["animate(target, duration = 200.0, ease = ease-out)",
                                          "animate-color(target, duration = 200.0, ease = ease-out)"],
      "A value (or color) that MOVES: returns the current interpolated "
      ++ "position, easing toward `target` over `duration` ms. Retargeting "
      ++ "mid-flight continues from the CURRENT position — no jump, so a "
      ++ "hover-out that reverses direction mid-animation looks natural. "
      ++ "Keyed like `use-state`, so each call site animates "
      ++ "independently. While unsettled it requests frames; once "
      ++ "settled, it goes quiet and the app stops re-rendering entirely "
      ++ "— the bar in the Live sample below stops requesting frames the "
      ++ "moment it reaches its target.",
      demo = Nothing),

    api-entry("easings: ease-in, ease-out, ease-in-out", ["ease-in(t)   // t in [0,1], returns [0,1]",
                                                            "ease-out(t)",
                                                            "ease-in-out(t)"],
      "The `ease` parameter `animate`/`animate-color` take: a plain "
      ++ "`float64 -> float64` curve over the unit interval. `ease-out` "
      ++ "(the default) starts fast and settles gently — the natural "
      ++ "choice for something moving TO a resting state, which is most "
      ++ "UI motion.",
      demo = Nothing),

    api-entry("set-time-dilation", ["set-time-dilation(factor)"],
      "Slows or speeds every `animate`/`animate-color` on the page by "
      ++ "`factor` (1.0 is real time, 0.25 is quarter speed) — a debug "
      ++ "toggle for watching a fast animation's easing curve rather than "
      ++ "a production feature. No live demo here: wiring a toggle needs "
      ++ "an app message this page doesn't have.",
      demo = Nothing),

    api-entry("scroll-state, set-scroll-offset, scroll-to", ["scroll-state(k)   // -> scroll-info",
                                                               "set-scroll-offset(k, v)",
                                                               "scroll-to(selector)"],
      "Read or drive a `scroll` region's live offset/content/viewport "
      ++ "from OUTSIDE it — `k` is the same key `scroll(name = ...)` "
      ++ "mints (`scroll-key(name)` derives it from the name directly). "
      ++ "`scroll-to(selector)` is higher-level: it resolves a selector "
      ++ "to a mounted widget and scrolls its enclosing region so that "
      ++ "widget lands at the viewport top — the mechanism behind every "
      ++ "\"on this page\" link and cross-page anchor on this site, "
      ++ "including the ones in this page's own on-this-page rail above.",
      demo = Nothing),

    api-entry("press-point", ["press-point()   // -> (x, y, timestamp)"],
      "The last press location within the CURRENT `interactive` region, "
      ++ "as an untracked ref (reading it doesn't itself trigger a "
      ++ "re-render — it rides on the press write's own invalidation). "
      ++ "`ripple` (paint & effects reference) is built on this: the "
      ++ "circle originates from the press point, not the widget's "
      ++ "center.",
      demo = Nothing),

    api-entry("memo", ["memo(build : (key) -> widget<msg>)"],
      "Establishes a memoization boundary at this call site: while "
      ++ "nothing the boundary's subtree READ has been written since last "
      ++ "render, `memo` returns the CACHED widget — the same pointer, so "
      ++ "reconcile skips relaying out the whole subtree via pointer "
      ++ "equality. Reads inside `build` auto-track; nothing to declare. "
      ++ "Reach for it around an expensive, rarely-changing subtree (a "
      ++ "long static list, a complex chart) once profiling shows re-"
      ++ "layout there costs something — it is not a default wrap-"
      ++ "everything primitive.",
      demo = Nothing),

    api-entry("Live sample: a value driving an animated bar", [],
      "`use-state` holding the target value, `animate` easing the bar "
      ++ "toward it — the two primitives above this page opens with, "
      ++ "combined:",
      demo = Just(live-progress(here()))) ]
```

The `use-state` entry's demo reuses `live-counter` directly (already
defined earlier in `pages.kk`, already proven to work — the home page and
tutorial page both use it) rather than inventing a new counter widget; the
code shown beside it illustrates `live-counter`'s actual implementation
(verbatim from its current definition in this file) even though the demo
call itself is just `live-counter(here())`, consistent with how the
`expanded` entry on the layout reference page shows real shell code
alongside a description of behavior the page's own chrome demonstrates.

- [ ] **Step 2: Add the `Doc-page` entry**

```koka
    Doc-page(QReference, "reference-state-animation", "Reference: state & animation",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. Ephemeral state that "
      ++ "doesn't touch the app model, and the primitives that animate it "
      ++ "smoothly.",
      [ Doc-section("State and animation", ref-state-anim-body) ]),
```

Add it right after `reference-paint-effects` in `QReference` order.

- [ ] **Step 3: Typecheck**

Run the Global Constraints typecheck command. Fix any errors before
continuing.

- [ ] **Step 4: Run the smoke suite**

Run the Global Constraints smoke command. Report the printed `SMOKE: N/N`
and confirm zero `FAIL` lines.

- [ ] **Step 5: Manually verify in a browser at 900px width**

Build for jsweb, serve, navigate to `#/reference-state-animation`. Confirm:
the `use-state` demo's counter increments on click; the `live-progress`
demo (Live sample entry) works exactly as it did before this plan (the
+10/−10 buttons move the bar, which eases smoothly rather than jumping).
Confirm nothing overflows past 900px.

- [ ] **Step 6: Verify no banned words**

```bash
grep -n "portable\|powerful\|elegant\|simply" samples/ui/site/pages.kk
```
Expected: no output.

- [ ] **Step 7: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: reference-state-animation -- new page for topic 5 (state & animation)"
```

---

### Task 3: Reference — Async (new page)

**Files:**
- Modify: `samples/ui/site/pages.kk` — add `ref-async-body`, add the new
  `Doc-page` entry.

**Interfaces:**
- Consumes: `api-entry`, `demo-panel` (blocks.kk); `future-boundary`,
  `default-placeholder`, `default-error` (lib/ui/async.kk); `retry-async`
  (lib/ui/state.kk); `dispatch` effect, `map-dispatch` (lib/ui/dispatch.kk
  — NEW import this task needs: `import ui/dispatch`, alongside the
  existing imports); `doc-link` (blocks.kk, for the cross-reference to
  `reference-text-content`'s `image`/`image-path` entry).
- Produces: `ref-async-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>`.

- [ ] **Step 1: Add the `ui/dispatch` import**

In `samples/ui/site/pages.kk`'s import block, add `import ui/dispatch`
alongside the existing imports.

- [ ] **Step 2: Write `ref-async-body`, 4 entries**

```koka
fun ref-async-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ api-entry("future-boundary", ["future-boundary(run, ready, placeholder = default-placeholder(),",
                                   "                failed = default-error, min-load = zero)"],
      "The general async primitive: `run` kicks off async work, `ready` "
      ++ "builds the widget once it resolves. While pending, shows "
      ++ "`placeholder`; `min-load` holds the placeholder at least that "
      ++ "long even if `run` finishes sooner, so a fast local resolve "
      ++ "doesn't flash. If `run` throws, `failed` gets the exception and "
      ++ "a retry thunk — clicking retry bumps an internal generation and "
      ++ "re-kicks `run`; a stale in-flight result from a PRIOR "
      ++ "generation is discarded rather than racing the new one. "
      ++ "`image`/`image-path` (text & content reference) are built on "
      ++ "this — see that page for the specific image-loading case. Two "
      ++ "runs below: one that resolves after a wait, one that fails once "
      ++ "and recovers on retry.",
      demo = Just(demo-panel(
        ["future-boundary(",
         "  fn() { wait(400.milli-seconds); \"done\" },",
         "  fn(v) text(\"Answer: \" ++ v, 15.0, theme.fg),",
         "  placeholder = text(\"loading...\", 15.0, theme.fg))"],
        future-boundary(
          fn() { wait(400.milli-seconds); "done" },
          fn(v : string) text("Answer: " ++ v, 15.0, theme.fg),
          placeholder = text("loading...", 15.0, theme.fg),
          ?key = scope("fb-demo"))))),

    api-entry("retry-async", ["retry-async(id : int)"],
      "The lower-level primitive `future-boundary`'s own retry button "
      ++ "calls: bumps the async entry at `id`'s generation directly. "
      ++ "Reach for `future-boundary` for the normal case (it wires this "
      ++ "up for you); reach for `retry-async` directly only if you're "
      ++ "building your own async boundary from the lower-level pieces "
      ++ "`future-boundary` itself composes.",
      demo = Nothing),

    api-entry("async images", [],
      "`image`/`image-path`'s `load = Async` mode is `future-boundary` "
      ++ "under the hood — see the text & content reference's `image, "
      ++ "image-path` entry for the full picture (fit modes, "
      ++ "placeholder, `min-load`, the Sync escape hatch).",
      demo = Just(doc-link("reference-text-content#text-and-content",
                            "image, image-path (text & content reference)",
                            ?key = scope("img-link")))),

    api-entry("dispatch", ["effect dispatch<a>", "  fun spawn( task : () -> <async,ioc> a ) : ()"],
      "An effect `update` can use to request async work WITHOUT doing "
      ++ "async work inside `update` itself: `spawn` hands the runtime a "
      ++ "task; the runtime runs it interleaved at the render-loop "
      ++ "boundary, and its result comes back around as an ordinary "
      ++ "message through `update`, same as a click. This is how "
      ++ "`update` stays a plain, testable function — no async threading "
      ++ "through your message-handling code — while still kicking off "
      ++ "real work (an HTTP-style call, a timer) in response to a "
      ++ "message. No live demo here: `dispatch` is only meaningful "
      ++ "inside an app's real `update` function, which this "
      ++ "message-agnostic reference page doesn't have.",
      demo = Nothing) ]
```

Note: the `future-boundary` demo's `run` lambda calls `wait` — confirm
`std/async` (for `wait`/`milli-seconds`) is already imported in
`pages.kk`, or add `import std/async` and `import std/time/duration` if
not already present (check the existing import block first; `wait` and
duration literals like `400.milli-seconds` may already be available via an
existing import this file has for other reasons).

- [ ] **Step 3: Add the `Doc-page` entry**

```koka
    Doc-page(QReference, "reference-async", "Reference: async",
      "Everything on this page compiles and runs — the code beside each "
      ++ "live sample is the call that builds it. The primitive async "
      ++ "work in lib/ui is built on, and how `update` requests it "
      ++ "without doing it inline.",
      [ Doc-section("Async", ref-async-body) ]),
```

Add it right after `reference-state-animation` in `QReference` order —
this is now the LAST reference page in Group 2, so it has no next-page
neighbor within `QReference` until Group 3 lands (expected and correct for
this plan's scope, same as Group 1's last page).

- [ ] **Step 4: Typecheck**

Run the Global Constraints typecheck command. Fix any errors before
continuing.

- [ ] **Step 5: Run the smoke suite**

Run the Global Constraints smoke command. Report the printed `SMOKE: N/N`
and confirm zero `FAIL` lines.

- [ ] **Step 6: Manually verify in a browser at 900px width**

Build for jsweb, serve, navigate to `#/reference-async`. Confirm: the
`future-boundary` demo shows "loading..." then "Answer: done" after
roughly 400ms (not stuck on the placeholder forever, not instant). Click
the "image, image-path" doc-link and confirm it navigates to
`#/reference-text-content` and scrolls to the "Text and content" section.
Confirm nothing overflows past 900px.

- [ ] **Step 7: Verify no banned words**

```bash
grep -n "portable\|powerful\|elegant\|simply" samples/ui/site/pages.kk
```
Expected: no output.

- [ ] **Step 8: Commit**

```bash
git add samples/ui/site/pages.kk
git commit -m "site: reference-async -- new page for topic 6 (async)"
```

---

## Final check (after all 3 tasks)

- [ ] Confirm no banned words remain anywhere in the file.
- [ ] Run the smoke suite one more time; confirm zero `FAIL` lines and
  note the final `SMOKE: N/N` count for the ledger.
- [ ] Confirm the sidebar's REFERENCE group now shows exactly 6 entries in
  order: Layout & containers, Text & content, Interaction, Paint &
  effects, State & animation, Async.
- [ ] Confirm `next-prev-links` chains correctly across all 6 reference
  pages now (Layout & containers has no prev, Async has no next, every
  page in between links to its correct neighbors).
- [ ] Fact-check sweep: re-read every NEW claim written in this plan's 3
  pages once more as a skeptical fact-checker (the same discipline that
  caught 4 issues across Group 1) — specifically the `ripple`/`use-state`
  demos' actual behavior, and the `use-state-quiet` entry's claim about
  when it differs from plain `use-state`, against `lib/ui/state.kk`'s real
  behavior one more time before calling this plan done.
