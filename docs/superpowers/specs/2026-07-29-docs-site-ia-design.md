# Docs Site Information Architecture & Content Model

Design for the overhaul of `samples/ui/site` into the lib/ui documentation
site, organized by Diátaxis. This spec covers the ORGANIZATION (what the site
contains, how it is structured, how structure derives navigation) and the
CONTENT MODEL (how pages and sections are declared). The visual shell (layout,
typography scale, responsive behaviour) gets its own spec after this one is
approved — the shell renders this model, so the model comes first.

## Decisions already made (recorded in task #62)

- **Purpose: teaching.** Tutorials and how-tos carry the weight; reference is
  complete but secondary; explanation covers the model. Not primarily a paper
  artifact, not primarily a showcase.
- **Tutorial style:** self-contained — just enough explanation to get through;
  depth is a link to explanation/how-to/reference. Tutorials link onward to
  further tutorials.
- **Build order: reference → explanation → how-to → tutorial** (link targets
  before the things that link to them).
- **Cross-page anchors** are required and SHIPPED: `scroll-to(slug)` resolves
  inside `bake-scroll` so a navigation with a fragment paints scrolled on its
  first frame (`4e1906f0a`); `anchor-route-sub` parses `page#slug` hashes
  (`6cdbf5277`). `heading(s)` self-keys by `scope(slugify(s))`, so every
  heading is an anchor.
- **Slugs derive from titles** ("Animate a value" → `animate-a-value`).
  Renaming a title breaks inbound links; accepted.
- **Testing is documented from the user's perspective** — how to test an app
  you built, not how the framework tests itself.
- **The gallery folds into reference**: each widget's entry shows the code
  that generates a sample NEXT TO the live sample. No separate gallery area.
- **Code blocks**: monospace panel with horizontal pan is done; syntax
  highlighting is deferred.

## The content model: pages as data, bodies as functions

Navigation, per-page contents, next/prev, and cross-links must all DERIVE
from one declaration. But section bodies host LIVE widgets (state, animation,
async), so a page cannot be pure data — bodies are widget-producing
functions, while everything navigation needs is plain data:

```koka
// what a section's body may contain is ordinary widget code; the STRUCTURE
// is the data wrapper around it
struct doc-section<a>
  title : string                      // slug derives: slugify(title)
  body  : (key) -> <keytree,uistate,ioc,theme> list<widget<a>>

struct doc-page<a>
  quadrant : quadrant                 // Tutorial | HowTo | Reference | Explanation
  slug     : string                   // the route path segment
  title    : string
  intro    : string                   // one-paragraph lead, also used by the home page
  sections : list<doc-section<a>>

val site-pages : list<doc-page<site-msg>>   // THE site, in reading order
// (pages emit no messages of their own, so `site-msg` only carries the
// shell's navigation/theme messages; a rank-2 `some<a>` field is not a
// thing Koka structs can hold, and does not need to be)
```

Derived from `site-pages` alone:

- **Sidebar**: pages grouped by quadrant, in list order.
- **Route parsing**: `slug` ↔ route; unknown → home. The route type in
  `main.kk` collapses to `Page(slug)` + `Home` instead of one constructor per
  page.
- **"On this page" rail**: section titles → `scroll-to(slugify(title))`
  links. (Shell spec decides where it renders; the data is free.)
- **Next/prev**: adjacent pages within a quadrant, "next tutorial" links at
  tutorial ends.
- **Cross-page links**: `doc-link("reference/state#animate", label)` — a thin
  wrapper over `link` that keeps the `page#slug` convention in one place.

The renderer is one function: title + intro + for each section,
`heading(title)` (which self-anchors) followed by `body(key)`, keyed by
`scope(slugify(title))` so section state is stable under reordering.

**Section-level reuse (the "reusable components" ask)** — the standard blocks
pages are written with, all existing or small:

| block | what it is |
|---|---|
| `prose`, `heading`, `doc-title` | exist (content.kk) |
| `code-block(lines)` | exists; monospace panel, pans horizontally |
| `api-entry(name, signature-lines, description, demo)` | NEW — the reference unit: name (anchored), signature as code, one paragraph, optional live demo beside it. This is the code-next-to-live-demo gallery pattern. |
| `demo-panel(code-lines, live)` | NEW — code on the left/top, the LIVE result of that code beside it; used by api-entry and tutorials |
| `note`, `see-also(links)` | NEW — callout box; the standard link-out block tutorials use |

## Reference: 9 pages, and an explicit exclusion line

The reference documents the APP AUTHOR surface. Runtime plumbing
(`install-*`, `drain-state`, `anim-tick`, `flush-*`, `publish-*`,
`take-frame-request`, `bake-scroll`) and backend/harness walks (`layout`,
`reconcile`, `hit*`, `hover-*`, `owner-*`, `sync-scroll-metrics`,
`scroll-anchor-pos`) are OUT — one line on the explanation "one tree, three
backends" page says these exist for backend/harness authors and points at the
source. Documenting them as user API would freeze internals we still move. What USERS
must be aware of conceptually -- keys, memoization, the state model -- is real
public API and gets full treatment (reference entries AND explanation pages).

Each entry below is an `api-entry` (signature + paragraph + demo where a demo
shows something):

1. **Layout & containers** — `box`, `row`, `column`, `stack`, `spacer`,
   `expanded`, `center`, `fixed`, `intrinsic-width`, `clip`, `overlay`,
   `scroll`, `lazy-column`, `positioned`. Demos: expanded-under-header,
   stack, clip-with-overflowing-child, lazy list.
2. **Text & content leaves** — `text` (size/font overloads), `paragraph`,
   `code`, `rect`, `image`/`image-path` (`image-fit`, `min-load`,
   placeholder), `link`; fonts (`sans`, `serif`, `mono`, `bold`, `font`).
3. **Interaction** — `interactive` (+ `interaction`), `act`, `act-msg`,
   `field`, `text-input`, `slider`, drag & drop (box's `drag`/`on-drop`,
   payload flow), click-at/context-at, `hit-slop`, `disabled`.
4. **Paint & effects** — `fill` + `paint-source` (`SLinear`, `SRadial`,
   `SImage`), color (`rgb`, `mix`, `brighten`, `contrasting`), `rotated`,
   `transform3d` (+ `ui/transform` matrices), `ripple`. Demos: the gallery's
   fill-sources row, ripple on a button, the flip card.
5. **State & animation** — `use-state`, `use-state-quiet` (when each),
   `animate`, `animate-color`, easings, `set-time-dilation`, scroll state
   (`scroll-state`, `set-scroll-offset`, `scroll-to`), `press-point`, `memo`.
6. **Async** — `future-boundary` (placeholder/ready/failed/retry,
   generations, `min-load`), async images, `retry-async`, `dispatch`
   (spawning from update).
7. **App & routing** — `app`, `app-config`, subs, `window`/`compose`
   (multi-window), router (`route-sub`, `anchor-route-sub`, `navigate`,
   `route/link`, `split-fragment`), deep links.
8. **Theming & styled components** — `theme` (light/dark/mix, crossfade
   idiom), `ui/style/default` components (`page`, `card`, `chrome`, buttons,
   `accented`, `body`, `dropdown`, `expander`, `context-menu`, scrollbars),
   `ui/style/material` as the drop-in proof, `button-style`/`styled-paint`
   for custom styles.
9. **Testing your app** — `test-scenarios`, the `tester` ops (`click`,
   `find`, `texts`, `type-text`, `settle`, `check-eq`), selector grammar,
   scenario patterns (assert on what the user sees), one paragraph on the
   live tier.

## Explanation: 8 concepts

Each is one page, a few sections, prose-heavy, diagrams later. Scope in one
sentence each:

1. **One tree, three backends** — widget → layout → ltree; what a backend is
   (lower/paint + input pump); where the seams genuinely are.
2. **Keys and identity** — `?key`, call-site keys, `scope`/`idx`, why two
   calls on one line collide, how identity drives state retention and
   reconciliation.
3. **The state model** — app model vs ephemeral ui/state; transitions vs
   quiet writes; why `update` is pure modulo `dispatch`.
4. **Memoization and dependency channels** — `memo`, tracked reads,
   invalidation, dirty storms (ledger §17's material, user-level).
5. **The layout model** — constraints down / sizes up; layout-neutral nodes
   (`overlay`, hit-slop) and why `fixed` caps rather than pins.
6. **Async boundaries and generations** — kick/pending/settle,
   stale-discard, retry as a generation bump; why min-load is a deadline.
7. **The painting model** — fills, paint sources, clips, transforms; what is
   native on each backend (nothing emulated).
8. **Portability and its honest limits** — same code on three backends; the
   week's finding that "the web can't do X" claims were compiler/design bugs,
   not platform limits; where the real boundary is (shaders, meshes).

## How-to: task recipes

Short, one problem each, heavy on `see-also`: scrolling list under a fixed
header · add a route (+ fragment links) · embed a live demo in a page ·
theme a button / add a custom style · load an image (asset vs URL, fits,
placeholder) · run an async task with retry · animate a value ·
drag and drop · test a widget · add a slow-motion debug toggle.

## Tutorials: build real apps

Diátaxis tutorials are LESSONS THROUGH DOING: the learner builds something
genuinely interesting end-to-end, and concepts arrive exactly when the app
needs them -- never as a topic tour. (The first draft of this section was a
syllabus -- "Layout and lists", "State and interaction" -- which is the
canonical mistake; those are how-to/explanation shapes.) Each tutorial below
is one complete app. Topic coverage is what the APP demands, with `see-also`
links carrying the depth; the mapping is noted so we can check nothing
important lacks a tutorial home.

1. **A pomodoro timer.** The first app, chosen over a counter because it is
   something you would actually keep open: a big animated ring or bar, start
   / pause / reset, work-break cycling. Teaches: model/view/update, buttons,
   `animate`, ephemeral vs model state -- and it is satisfying in under a
   hundred lines.
2. **A photo browser.** A scrolling, searchable grid of images with a detail
   view. Teaches: layout (rows/columns/expanded), `lazy-column`, async
   images with placeholders and retry, a text field driving a filter,
   fill sources for the polish pass.
3. **A kanban board.** Columns of cards, drag and drop between them, a route
   per board, deep-linkable. Teaches: drag & drop, keys and identity under
   reordering (the place learners actually hit it), routing with fragments,
   scroll regions.
4. **Ship it in style.** Take the kanban board from tutorial 3: theme it
   (default -> material -> a custom `button-style`), add light/dark with the
   crossfade idiom, then write the test scenarios that pin its behaviour --
   ending with the same assert-on-what-the-user-sees discipline the
   reference teaches.

5. **A real CRUD app** (GATED -- see below). Expand the kanban into an app
   backed by a server: boards and cards load from and persist to a backend,
   with loading and error states through `future-boundary`, optimistic
   updates and retry, and offline-tolerant reads. Teaches: backend
   communication -- the one thing most real apps need that tutorials 1-4
   never touch.

   Gate: lib/ui has NO designed backend-communication story yet (no
   fetch/HTTP surface; the `net` effect exists in rows but nothing user-
   facing sits on it). That design is its own piece of framework work and
   its own spec, and this tutorial is written only after it lands. Listed
   here so the tutorial arc is honest about where it ends today, and so the
   framework design has a named consumer waiting.

Tutorials 1-3 are independent (a learner can start at any); 4 deliberately
builds on 3's checkpoint, whose finished code ships in the repo so 4 stands
alone too; 5 extends the same app once its framework prerequisite exists.
Every tutorial ends with "where to go next": the next tutorial plus the
explanation pages for what was used but not explained.

## Rollout

1. **Content model + renderer** in the site: `doc-page`/`doc-section`,
   derived sidebar/contents/next-prev, `api-entry`/`demo-panel`/`note`/
   `see-also` blocks. The five existing pages refactor into it (small).
2. **Reference pages** (9), in the order listed — each page lands with its
   live demos.
3. **Explanation pages** (8).
4. **How-to recipes**, then **tutorials** (so their link targets exist).
5. **Shell spec** (separate): visual overhaul, responsive layout, typography
   scale — informed by real content rather than lorem ipsum.

Testing along the way: the anchor test exists; add a site smoke test
(headless: every page builds; every derived slug resolves via `find-ids`;
next/prev total order). The slug-resolution check is the one that catches a
renamed title breaking inbound links.
