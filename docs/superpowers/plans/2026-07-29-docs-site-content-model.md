# Docs Site Content Model Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rollout step 1 of the docs-site spec — pages become data, navigation derives from it, the reusable content blocks exist, and the five existing pages are refactored into the model.

**Architecture:** `samples/ui/site` splits into `model.kk` (page/section data + derivations), `blocks.kk` (the reusable content blocks), `pages.kk` (the site's pages as `doc-page` values; replaces `content.kk`), and a slimmer `main.kk` (slug routes, derived sidebar, one renderer). A headless smoke test pins the invariants the spec names: every page builds, every derived slug resolves, next/prev is a total order, and a cross-page anchor works against the real site view.

**Tech Stack:** Koka (worktree compiler), lib/ui, ui/test harness. Build/test commands below assume:

```bash
export KOKA=/Users/timwhiting/koka/.worktrees/koka-clang-wasm/.stack-work/install/aarch64-osx/f85b4dc81f126d06881fec188dc62cdb96d6f54b1fd1f1051955dc1d51fe411a/9.10.3/bin/koka
```

## Global Constraints

- Slugs DERIVE from titles via `slugify` ("Animate a value" → `animate-a-value`); no explicit slug fields on sections.
- Section headings self-anchor: `heading(s)` already keys by `scope(slugify(s))` — the renderer must NOT wrap headings in another scope that changes their selector, and section bodies are keyed `scope(slugify(title))`.
- Cross-page links use the `page#slug` hash convention via `anchor-route-sub` (already shipped); in-page rail links call `scroll-to(slugify(title))` directly.
- The route type collapses to `Home` + `Page(slug)`; unknown slugs parse to `Home`.
- Pages emit no messages of their own: bodies are `(key) -> <keytree,uistate,ioc,theme> list<widget<msg>>` at the site's `msg`.
- Every task ends with `samples/ui/site` building for jsweb (`$KOKA -e build.kk -- jsweb` from `samples/ui/site`, expect `staged : out-js/`) — the site must never re-rot mid-plan.
- Existing helper behavior (`prose`, `heading`, `doc-title`, `code-block`, `slugify`, live demos) moves, not changes.

---

### Task 1: `model.kk` — the data model and its derivations

**Files:**
- Create: `samples/ui/site/model.kk`
- Modify: `samples/ui/site/content.kk` (remove `slugify`/`slug-char`; import model)
- Test: `samples/ui/site/smoke.kk` (created here, grows in later tasks)

**Interfaces:**
- Produces: `type quadrant` (`QTutorial|QHowTo|QReference|QExplanation`), `struct doc-section<a>(title : string, body : (key) -> <keytree,uistate,ioc,theme> list<widget<a>>)`, `struct doc-page<a>(quadrant : quadrant, slug : string, title : string, intro : string, sections : list<doc-section<a>>)`, `slugify(s : string) : string`, `quadrant/show`, `find-page(pages, slug) : maybe<doc-page<a>>`, `next-prev(pages, slug) : (maybe<doc-page<a>>, maybe<doc-page<a>>)` (within the same quadrant only).

- [ ] **Step 1: Write `model.kk`**

```koka
// The docs site's content model (spec: docs/superpowers/specs/
// 2026-07-29-docs-site-ia-design.md). Metadata is DATA -- everything
// navigation needs derives from `list<doc-page>` -- while section BODIES are
// widget functions, because they host live demos. Slugs derive from titles;
// a heading is its own anchor (blocks.kk), so a section's title is also its
// cross-page address: "reference-widgets#text".
module model

import ui/keytrie
import ui/widget
import ui/state
import ui/style/default

pub type quadrant
  QTutorial
  QHowTo
  QReference
  QExplanation

// sidebar group headers, in display order
pub fun quadrant/show( q : quadrant ) : string
  match q
    QTutorial -> "LEARN"; QHowTo -> "TASKS"
    QReference -> "REFERENCE"; QExplanation -> "UNDERSTAND"

pub fun quadrant/same( a : quadrant, b : quadrant ) : bool
  a.show == b.show

pub struct doc-section<a>
  title : string                      // slug derives: slugify(title)
  body  : (key) -> <keytree,uistate,ioc,theme> list<widget<a>>

pub struct doc-page<a>
  quadrant : quadrant
  slug     : string                   // the route path segment
  title    : string
  intro    : string                   // one-paragraph lead
  sections : list<doc-section<a>>

// lowercase, spaces to dashes, everything else but letters/digits dropped
fun slug-char( c : char ) : char
  if c == ' ' then '-'
  elif (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' then c
  elif c >= 'A' && c <= 'Z' then (c.int + 32).char
  else '_'

pub fun slugify( s : string ) : string
  s.list.map(slug-char).filter(fn(c) c != '_').string

pub fun find-page<a>( pages : list<doc-page<a>>, slug : string ) : maybe<doc-page<a>>
  pages.find(fn(p) p.slug == slug)

// previous/next WITHIN the page's quadrant (reading order = list order);
// Nothing at either end, (Nothing, Nothing) for an unknown slug
pub fun next-prev<a>( pages : list<doc-page<a>>, slug : string ) : (maybe<doc-page<a>>, maybe<doc-page<a>>)
  match pages.find(fn(p) p.slug == slug)
    Nothing -> (Nothing, Nothing)
    Just(cur) ->
      val q = pages.filter(fn(p) p.quadrant.same(cur.quadrant))
      fun go( xs : list<doc-page<a>>, prev : maybe<doc-page<a>> ) : (maybe<doc-page<a>>, maybe<doc-page<a>>)
        match xs
          Cons(p, rest) | p.slug == slug -> (prev, rest.head)
          Cons(p, rest) -> go(rest, Just(p))
          Nil -> (Nothing, Nothing)
      go(q, Nothing)
```

- [ ] **Step 2: Move `slugify` out of `content.kk`**

In `samples/ui/site/content.kk`: delete `slug-char` and `slugify` definitions; add `import model` after the existing imports. (`heading` keeps calling `slugify` — it now resolves from model.)

- [ ] **Step 3: Write the failing smoke test (model half)**

Create `samples/ui/site/smoke.kk`:

```koka
// Headless invariants for the site's content model (spec's testing note):
// slugs derive predictably, and next/prev is a total order within a
// quadrant. Grows in later tasks: page builds, slug resolution, anchors.
module smoke

import std/core/unsafe
import ui/widget
import ui/keytrie
import ui/state
import ui/style/default
import model

val passed : ref<global,int> = unsafe-total{ ref(0) }
val failed : ref<global,int> = unsafe-total{ ref(0) }

fun check( name : string, cond : bool ) : ioc ()
  if cond then passed := !passed + 1
  else
    failed := !failed + 1
    println("FAIL: " ++ name)

type m
  MNone

fun no-body( k : key ) : <keytree,uistate,ioc,theme> list<widget<m>>
  []

val fixture : list<doc-page<m>> =
  [ Doc-page(QTutorial, "t-one", "T One", "", [Doc-section("Alpha Beta", no-body)]),
    Doc-page(QTutorial, "t-two", "T Two", "", []),
    Doc-page(QReference, "r-one", "R One", "", []) ]

pub fun main()
  check("slugify lowercases and dashes", slugify("Animate a Value") == "animate-a-value")
  check("slugify drops punctuation", slugify("Keys & identity!") == "keys--identity")
  val (p1, n1) = fixture.next-prev("t-one")
  check("first page has no prev", p1.is-nothing)
  check("first page's next is its quadrant sibling", n1.map(fn(p) p.slug).default("") == "t-two")
  val (p2, n2) = fixture.next-prev("t-two")
  check("last-in-quadrant has no next (other quadrants excluded)", n2.is-nothing)
  check("prev links back", p2.map(fn(p) p.slug).default("") == "t-one")
  check("unknown slug is (Nothing, Nothing)", fixture.next-prev("nope").fst.is-nothing)
  println("SMOKE: " ++ (!passed).show ++ "/" ++ (!passed + !failed).show ++ " passed")
  if !failed > 0 then println("SMOKE: FAILED")
```

Note: check `slugify("Keys & identity!")` output against the implementation before pinning — `&` and `!` drop, so `"keys--identity"` (space, dropped-&, space → two dashes). If the run disagrees, the TEST expectation is what moves.

- [ ] **Step 4: Run the smoke test**

```bash
cd samples/ui/site && $KOKA --console=raw -i. -i../../../lib -e smoke.kk
```
Expected: `SMOKE: 7/7 passed` (or fix `model.kk` until it does; before Task 1 exists it fails to compile — that is the red).

- [ ] **Step 5: Site still builds**

```bash
cd samples/ui/site && $KOKA -e build.kk -- jsweb
```
Expected: `staged : out-js/`

- [ ] **Step 6: Commit**

```bash
git add samples/ui/site/model.kk samples/ui/site/smoke.kk samples/ui/site/content.kk
git commit -m "site: content model -- doc-page/doc-section + derivations (spec step 1, task 1)"
```

---

### Task 2: `blocks.kk` — the reusable content blocks

**Files:**
- Create: `samples/ui/site/blocks.kk` (prose/heading/doc-title/code-block MOVE here from content.kk, unchanged; new blocks below)
- Modify: `samples/ui/site/content.kk` (remove the moved helpers; `import blocks`)

**Interfaces:**
- Consumes: `slugify` (model), existing `heading` self-anchoring behavior.
- Produces: `api-entry(name : string, signature : list<string>, description : string, demo : maybe<widget<a>>, ?key) : <keytree,uistate,ioc,theme> widget<a>` · `demo-panel(code : list<string>, live : widget<a>, ?key) : <keytree,uistate,ioc,theme> widget<a>` · `note(s : string, ?key) : theme widget<a>` · `see-also(links : list<(string,string)>, ?key) : <keytree> widget<a>` (target path, label) · `doc-link(target : string, label : string, ?key) : <keytree> widget<a>`.

- [ ] **Step 1: Create `blocks.kk`** — move `doc-title`, `heading`, `prose`, `code-block` (verbatim, with their current signatures) from `content.kk`, then add:

```koka
// a cross-page docs link: target is "page-slug" or "page-slug#section-slug"
// (the hash convention anchor-route-sub parses); label is the visible text
pub fun doc-link<a>( target : string, label : string, ?key : key ) : <keytree,theme> widget<a>
  link( target, accented("-> " ++ label, 15.0, ?key = scope("lbl")) )

// a callout: one tinted panel, for asides and warnings
pub fun note<a>( s : string, ?key : key ) : theme widget<a>
  box( paragraph(s, 15.0, theme.fg), padding = 12.0,
       bg = Just(Fill(theme.surface, 8.0)) )

// the standard link-out block tutorials and how-tos end with
pub fun see-also<a>( links : list<(string, string)>, ?key : key ) : <keytree,theme> widget<a>
  box( column( [ text("See also", 13.0, theme.accent, ?key = scope("hdr")) ] ++
               links.map-indexed(fn(i, l) doc-link(l.fst, l.snd, ?key = idx(i))),
               gap = 6.0 ),
       padding = 12.0, bg = Just(Fill(theme.surface, 8.0)) )

// code beside its LIVE result -- the gallery pattern (code left, demo right)
pub fun demo-panel<a>( code : list<string>, live : widget<a>,
                       ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<a>
  row( [ code-block(code, ?key = scope("code")), live ], gap = 16.0 )

// the reference unit: an anchored name, its signature, one paragraph, and
// (when one shows something) a live demo of it
pub fun api-entry<a>( name : string, signature : list<string>, description : string,
                      demo : maybe<widget<a>> = Nothing,
                      ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc,theme> widget<a>
  column( [ heading(name),                       // heading self-anchors: slugify(name)
            code-block(signature, ?key = scope("sig")),
            prose(description, ?key = scope("desc")) ] ++
          (match demo { Just(d) -> [d]; Nothing -> [] }),
          gap = 8.0 )
```

(Adjust `link`/`accented`/`idx` argument shapes to the current signatures if the compiler objects — behavior, not shape, is the contract. `content.kk` keeps only the live demos and pages after this.)

- [ ] **Step 2: Extend `smoke.kk`** — add to `main` (with `import blocks` and a `with-uistate`-style harness if required for building widgets; follow test/ui/state-channels.kk's `with-uistate` usage):

```koka
  // blocks build headlessly at a root key (no layout needed to construct)
  // -- this is a COMPILE + construct check, the render check is Task 4's
```
Concretely: inside a `with-uistate` block, construct `note("hi", ?key = root-key)`, `see-also([("reference-widgets#text","Text")], ?key = root-key)` and check `True` for each (construction not throwing IS the check). If widget construction needs `keytree`, wrap with the same harness `test-scenarios` uses — if that becomes heavy, defer block rendering to Task 4's scenario and keep this step compile-only.

- [ ] **Step 3: Run smoke + build**

```bash
cd samples/ui/site && $KOKA --console=raw -i. -i../../../lib -e smoke.kk && $KOKA -e build.kk -- jsweb
```
Expected: all smoke checks pass; `staged : out-js/`.

- [ ] **Step 4: Commit**

```bash
git add samples/ui/site/blocks.kk samples/ui/site/content.kk samples/ui/site/smoke.kk
git commit -m "site: reusable content blocks -- api-entry, demo-panel, note, see-also, doc-link (task 2)"
```

---

### Task 3: `pages.kk` — the five pages as data

**Files:**
- Create: `samples/ui/site/pages.kk`
- Delete: `samples/ui/site/content.kk` (live demos move into pages.kk; nothing else remains)

**Interfaces:**
- Consumes: model types, blocks, the live demos (`live-counter`, `live-progress`, `demo-button` move verbatim).
- Produces: `type site-msg` is NOT here (stays in main.kk); pages are polymorphic: `pub fun site-pages<a>() : list<doc-page<a>>` — a function, not a `val`, because bodies capture nothing and `doc-page<a>` must instantiate at main's msg. Also `pub fun home-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>` (home stays outside the quadrants).

- [ ] **Step 1: Write `pages.kk`** — move the live demos verbatim, then declare the pages. Carve each existing page's widget list into 2–4 `Doc-section`s at its current `heading(...)` boundaries; everything before the first heading becomes the page `intro` (paragraph text) or the first section. Exact mapping:

| old page | slug | quadrant | sections (titles = existing headings) |
|---|---|---|---|
| tutorial-page | `tutorial-first-app` | QTutorial | "The model and messages" / "The view" / "The update" / "The result" (strip the old numeric prefixes — "1. The model..." → "The model and messages", so slugs stay clean) |
| howto-page | `howto-layout` | QHowTo | "Rows and columns" / "Fill the leftover space" / "Center with a max width" (the two-counters demo joins this last section) |
| reference-page | `reference-widgets` | QReference | "Text" / "Containers" / "Interactive" / "Live sample" — and "Text" REWRITES as three `api-entry`s (`text`, `paragraph`, `code`) with a `demo-panel` on `text`, proving the Task 2 blocks in real content |
| explanation-page | `explanation-one-core` | QExplanation | "Backends lower the SAME tree" / "Style is a swappable layer" / "State without the model" / "Reconcile and reuse" |

Body shape, one concrete example (the rest follow it):

```koka
fun tut-model-body<a>( key : key ) : <keytree,uistate,ioc,theme> list<widget<a>>
  [ prose("An app is three things: a model, an update, and a view. ..."),
    code-block(["struct model( count : int )", "type msg", "  Inc", "  Dec"]) ]

pub fun site-pages<a>() : list<doc-page<a>>
  [ Doc-page(QTutorial, "tutorial-first-app", "Your first app",
      "An app is a model, an update, and a view -- the runtime owns the loop.",
      [ Doc-section("The model and messages", tut-model-body),
        Doc-section("The view", tut-view-body),
        ... ]),
    ... ]
```

The home page's cross-page anchor link updates its target to the new slug: `"explanation-one-core#state-without-the-model"`.

- [ ] **Step 2: Build check** (main.kk still imports content — expect FAILURE here; that red belongs to Task 4). Compile pages alone instead:

```bash
cd samples/ui/site && $KOKA --console=raw -i. -i../../../lib -c pages.kk
```
Expected: compiles. Keep `content.kk` deleted only when Task 4 lands if the site must stay green between commits — otherwise delete now and commit Tasks 3+4 together. Preferred: do Task 3 and 4 on one branch-local commit boundary but keep the diffs reviewable as two.

- [ ] **Step 3: Commit** (with Task 4 if the build gate demands it)

```bash
git add samples/ui/site/pages.kk
git commit -m "site: the five pages as doc-page data (task 3)"
```

---

### Task 4: `main.kk` — slug routes, derived sidebar, one renderer

**Files:**
- Modify: `samples/ui/site/main.kk`
- Delete: `samples/ui/site/content.kk`

**Interfaces:**
- Consumes: `site-pages()`, `home-body`, `find-page`, `next-prev`, `quadrant/show`, `slugify`, blocks.
- Produces: `pub fun view`, `pub fun update`, `pub type msg` (exposed `pub` so smoke.kk can drive the real shell), route `type route { Home; Page(slug : string) }`.

- [ ] **Step 1: Rewrite main.kk's routing + shell**

```koka
type route
  Home
  Page( slug : string )

fun parse-route( path : string ) : route
  if path.is-empty then Home
  else match site-pages().find-page(path)   // msg instantiates at site's msg
    Just(_) -> Page(path)
    Nothing -> Home

fun print-route( r : route ) : string
  match r { Home -> ""; Page(s) -> s }
```

Sidebar derives: for each quadrant in `[QTutorial, QHowTo, QReference, QExplanation]`, a `text(q.show, 12.0, theme.accent)` header then `site-pages().filter(same quadrant)` as nav links (`link(p.slug, ...)`, active when `m.route` is `Page(p.slug)`), each `?key = scope("nav-" ++ p.slug)`. Home keeps its explicit entry.

Renderer replaces `page-body`:

```koka
fun render-page( p : doc-page<msg>, key : key ) : <keytree,uistate,ioc,theme> widget<msg>
  column(
    [ doc-title(p.title, ?key = scope("title")),
      prose(p.intro, ?key = scope("intro")),
      // the on-this-page rail: section titles -> in-page anchors
      row( p.sections.map-indexed(fn(i, s)
             act( text(s.title, 13.0, theme.accent, ?key = scope("toc-" ++ slugify(s.title))),
                  fn() scroll-to(slugify(s.title)) )), gap = 12.0 ) ] ++
    p.sections.flatmap(fn(s)
      [ heading(s.title) ] ++ (s.body)(scope(slugify(s.title))) ) ++
    next-prev-links(p),
    gap = 15.0 )

fun next-prev-links( p : doc-page<msg> ) : ... 
  // from next-prev(site-pages(), p.slug): "<- prev.title" / "next.title ->"
  // as link(prev.slug, ...) entries in a row; omit Nothing sides
```

(`act`'s current signature takes the thunk positionally — match it. `next-prev-links` is ordinary code the implementer writes from the derivation; both sides are plain `link`s.)

- [ ] **Step 2: Extend smoke.kk into a scenario test** — drive the REAL shell with `test-scenarios` (pattern: test/ui/anchor-scroll.kk):

```koka
pub fun site-scenario( t : tester<msg> ) : <async,keytree,uistate,uicheck,ioc,exn> ()
  // 1. every page mounts and every derived slug resolves
  site-pages().foreach fn(p)
    navigate(print-route, Page(p.slug))   // or click its sidebar link
    t.settle()
    p.sections.foreach fn(s)
      check("slug resolves: " ++ p.slug ++ "#" ++ slugify(s.title),
            find-ids(slugify(s.title)).is-cons)
  // 2. cross-page anchor: from home, the state-without-the-model link works
  //    (t.click on the link; then t.find("state-without-the-model") is Just
  //     with y at the content viewport top -- reuse anchor-scroll.kk's
  //     top-of pattern with this shell's header height)
```

If `navigate` (hash-based) does not drive the headless harness, dispatch the route msg directly: `t.emit(Navigated(Page(p.slug)))`-style — the harness exposes clicks; if no emit exists, click the sidebar nav links (`t.click("nav-" ++ p.slug)`), which is truer anyway.

- [ ] **Step 3: Run everything**

```bash
cd samples/ui/site && $KOKA --console=raw -i. -i../../../lib -e smoke.kk   # all checks green
$KOKA -e build.kk -- jsweb    # staged : out-js/
$KOKA -e build.kk -- native && KOKA_IMP_FRAMES=40 ./app-native   # exit 0
```

- [ ] **Step 4: Browser spot-check** (cache disabled — stale .mjs burned us): serve `out-js`, deep-link `#/explanation-one-core#state-without-the-model`, confirm the page lands scrolled; click a sidebar link; click one on-this-page rail entry.

- [ ] **Step 5: Commit**

```bash
git add samples/ui/site/main.kk samples/ui/site/smoke.kk
git rm samples/ui/site/content.kk
git commit -m "site: derived nav + renderer over the content model; content.kk retired (task 4)"
```

---

### Task 5: regression + docs

**Files:**
- Modify: `docs/ui/design-notes.md` (short ledger entry: the site's content model, what derives, the smoke invariants)

- [ ] **Step 1: Full lib regression** (the site work touched no lib code after Task 4, but the suites are the gate):

```bash
cd test/ui && for t in anchor-scroll basic retain lazy windows selector clip-hit transform-hit async-boundary state-channels web-image-settle mat4; do $KOKA --console=raw -i.. -e $t.kk 2>&1 | grep -Ei "passed|FAILED"; done
cd live && ./build.sh && ./test-live   # 46/46 (re-run once if the known #57 keystroke flake trips)
```

- [ ] **Step 2: Ledger entry + commit**

```bash
git add docs/ui/design-notes.md
git commit -m "docs/ui: ledger -- the docs site's page-as-data content model (task #62 step 1)"
```

---

## Self-review notes

- Spec coverage: content model ✓ (T1), derived sidebar/rail/next-prev/routes ✓ (T4), blocks ✓ (T2, proven in real content by T3's reference rewrite), five pages refactored ✓ (T3), smoke invariants ✓ (T1/T4), home outside quadrants ✓ (T3/T4). Out of scope by design: reference pages 2–9, explanation/how-to/tutorial content, shell visual overhaul (later rollout steps).
- Known soft spots the implementer owns: exact current signatures of `act`/`link`/`accented`/`idx` (match the code, not this plan); whether smoke block-construction needs the harness (defer to the T4 scenario if heavy); T3/T4 may need to land as one build-green commit pair.
