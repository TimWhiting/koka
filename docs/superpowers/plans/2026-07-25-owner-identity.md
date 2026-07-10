# Owner Identity + Selector Addressing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Every widget/ltree node carries its owning identity (`owner : int32`), addressing becomes selector queries over the keytrie path table resolved to owner-geometry, and `keyed`/`anchored`/`Region` are removed — per `docs/superpowers/specs/2026-07-25-owner-identity-design.md`.

**Architecture:** `owner` is captured at widget construction (smart constructors stamp the ambient `?key`), flowed through `layout` onto the ltree (layout has no keytree, so it cannot re-derive), and read by a pure `owner-rect(ltree, id)` walk. A new `kt-find(selector)` keytree op resolves path selectors to ids against the existing id→path table. This is the widest refactor in the project: it touches every widget/ltree constructor and every walk.

**Tech Stack:** Koka (lib/ui, lib/web-ui), both backends (Impeller native, web DOM).

## Global Constraints

- `owner : int32` on EVERY widget ctor and EVERY ltree ctor. Captured at widget build (smart constructors stamp `?key.key-id.int32`; id-bearing widgets — Interactive/Field/Input/Scroll/Memo — stamp their own minted id); `layout` copies widget owner → ltree owner. NEVER derived at query time (the ltree walk has no keytree).
- Ids are content-addressed int32, stable across renders regardless of siblings (the #50 property). No id recycling; stale ids miss harmlessly.
- Selector grammar (MVP): whitespace-separated DESCENDANT steps; a step is `name` (Named), `:i` (Index), or `name:i` (both, adjacent). Gaps allowed between steps. `kt-find` returns ALL matches; consumers decide (tester errors on ambiguity, listing paths via `segment/show`).
- PRE-PUBLICATION REMOVAL (Tim, memory feedback-pre-publication-removal): `keyed`/`anchored`/`Keyed`/`LKeyed`/`Region` are DELETED, not deprecated; ALL in-repo users (tests + samples + docs) migrate in this plan. No shims.
- Reconcile/FBIP: `owner` participates in node identity exactly as existing fields; it changes only on structure change → no reuse regression. Verify the bench (lib/ui/bench/reuse.kk) reuse counts do not degrade.
- Green between tasks: each task ends with the full existing matrix passing (headless ×4 runtimes incl. wasi-web, native live ×2, web live pass:9), same counts unless a task changes them intentionally.
- Koka gotchas: implicits can't default (a smart ctor gaining `?key` forces every caller to have `?key` in scope — the compiler's missing-implicit errors are the migration checklist, finishing rule 1c); `.int32` conversions; exhaustive-match errors are the walk checklist; named local funs; `ctx`/`use`/`raw` reserved; touch the owning .kk when a bundled .js changes; LOCAL .koka caches; live tier builds at -O1; wasi-web needs node ≥ 24 (`nvm use 24`).

## File Map

| File | Change |
|---|---|
| `lib/ui/keytrie.kk` | `kt-find` op + resolution over the id→path table; segment-selector parse |
| `lib/ui/widget.kk` | `owner` on widget + ltree ctors; smart ctors stamp `?key`; `layout`/`reconcile`/`size`/`hit`/`scroll-keys`/`map-msg` thread it; new `owner-rect` walk; `keyed`/`anchored`/`Keyed`/`LKeyed` removed (T5); `LLayer` marker |
| `lib/ui/state.kk`, `lib/ui/reactive.kk` | memo widget/ltree owner; anchor registry int-keyed (T4); `bake-scroll`/`apply-wheel`/metrics thread owner |
| `lib/ui/view.kk` | `target = Display \| Scope(sel)` (Region removed); Scope resolution via kt-find + owner-rect |
| `lib/ui/api/impeller/backend.kk`, `lib/ui/api/web/backend.kk` | every ltree walk threads owner; paint/present unaffected by value but arms rebind; `kk:layer`→`LLayer` lowering; anchor publication int-keyed |
| `lib/ui/test.kk`, `lib/ui/test-live.kk` | tester find/click/texts → selectors + owner-rect; string-name walk removed |
| `test/ui/*.kk`, `samples/ui/*`, `samples/web-ui/*` | migrate keyed→scope-mint / selectors; Region→Scope |
| `docs/ui/design-notes.md`, `docs/ui/paper-outline.md` | ledger §14 |

Tasks 1 is additive. Task 2 is the atomic crux (may split — see its note). Tasks 3–5 are green rewires/removals. Task 6 docs.

---

### Task 1: `kt-find` selector resolution (additive, no type change)

**Files:** Modify `lib/ui/keytrie.kk`; Test: new `test/ui/selector.kk` (a plain keytree program, not a UI app).

**Interfaces (produces):**
```koka
// a parsed selector step
pub type sel-step
  SName( name : string )
  SIndex( i : int )
  SBoth( name : string, i : int )
// parse "todos row:3 bump" -> [SName("todos"), SBoth("row",3), SName("bump")]
pub fun parse-selector( s : string ) : list<sel-step>
// keytree op: ids whose root path matches the steps in order (gaps allowed
// between steps; SBoth requires adjacent Named+Index)
fun kt-find( steps : list<sel-step> ) : list<int>
pub fun find-ids( sel : string ) : keytree list<int>   // parse + kt-find
```

- [ ] **Step 1: failing test** `test/ui/selector.kk` — a `main` under `with-keytree` that mints a known shape (e.g. via `kt-child`: root→Named "todos"→Index 3→Named "bump"; and a sibling Named "todos"→Index 4), then asserts `find-ids("todos row:3 bump")`… — but note the shape uses raw segments; build paths with `kt-child(root-key, Named("todos"))` etc. Assert exact id lists (capture the minted ids). Include: bare name unique → single id; `:i` alone; `name:i`; a gap (`todos bump` skipping the index); ambiguous (two matches). Print pass/fail counts; exit nonzero on fail (this is a standalone program, not the test-scenarios harness — mirror how test/async tests self-check, or use simple `println` + a `fail` counter + an exit extern; grep test/ui/live/winprobe.kk for the standalone exit idiom).
- [ ] **Step 2:** run `stack exec koka -- -v0 --console=raw -ilib -itest/ui -e test/ui/selector.kk` — fails (kt-find undefined).
- [ ] **Step 3:** implement in keytrie.kk: `kt-find` reads the handler's `paths` int32-map (id→list<segment>), matching each id's path against the steps (subsequence match with SBoth adjacency). `find-ids` = parse + op. Add `kt-find`/`find-ids` to the `keytree` effect + handler.
- [ ] **Step 4:** green. Headless suite unaffected (nothing else changed) — run basic.kk as a sanity check.
- [ ] **Step 5:** commit `git commit -am "ui/keytrie: kt-find -- selector resolution over the id->path table"`.

### Task 2: `owner` on every ctor (THE ATOMIC CRUX)

**Files:** `lib/ui/widget.kk` (widget+ltree types, all walks, smart ctors), `lib/ui/state.kk` (memo, use-state-adjacent builders), `lib/ui/view.kk` (scene widgets), both backends (lowering walks), `lib/ui/test.kk` (harness layout). Test: existing suites unchanged.

**Interfaces (produces):** `owner : int32` first field on every widget ctor and ltree ctor; `pub fun owner-rect<msg>( t : ltree<msg>, id : int, x : float64 = 0.0, y : float64 = 0.0 ) : maybe<(float64,float64,float64,float64)>` (shallowest node with `owner == id.int32`, with accumulated absolute position).

**NOTE — this is the largest single task in the repo.** If, mid-implementation, the field+walks prove too large to land coherently in one pass, STOP and report DONE_WITH_CONCERNS or BLOCKED with the natural split (suggested: 2a = types + smart ctors + layout + reconcile + size in widget.kk compiling with the two backends stubbed to bind-and-ignore owner via a mechanical pass; 2b = the rest of the walks + owner-rect). Do NOT leave the tree uncompilable across a task boundary.

- [ ] **Step 1:** Add `owner : int32` as the FIRST field of every `widget` ctor (Text, WBox, Flex, Spacer, Expanded, Keyed, Stack, Link, Scroll, Center, IntrinsicWidth, Rotated, Fixed, Memo, Positioned, Act, Interactive, TextInput, TextField, ActMsg, Slider, SizedBox) and every `ltree` ctor (LText, LBox, LFlex, LKeyed, LLink, LScroll, LAct, LRotate, LMemo, LInteractive, LField, LActMsg, LInput, LSlider). The compiler now errors at every construction and match — those errors are your exhaustive checklist.
- [ ] **Step 2:** Smart constructors gain `?key : key` and stamp `owner = ?key.key-id.int32`: `text`/`body`/`paragraph`/`code`, `box`, `row`/`column`, `spacer`, `expanded`, `stack`, `link`, `center`, `intrinsic-width`, `rotated`, `fixed`, `rect`, and the leaf helpers. Id-bearing constructors (`interactive`, `text-input`, `field`, `scroll`, `memo`) stamp their OWN minted id as owner (they already compute it). `keyed`/`anchored` (still present this task) stamp `?key` like any wrapper.
- [ ] **Step 3:** `layout` copies each widget's owner onto the ltree node it produces (owner is the first field on both — mechanical 1:1). `reconcile` preserves owner from the spec widget (a reused node adopts the new widget's owner; owner changing = a structural change that already forces a fresh node). `size`/`main-extent`/`cross` ignore owner (bind `_`). `map-msg` preserves. `scroll-keys` ignores.
- [ ] **Step 4:** Both backends: every ltree match arm binds owner (paint/hit/hover/bake/scroll/each-anchor rebind and pass through; owner does not change paint/hit behavior in this task). state.kk memo + view.kk scene widgets thread it. test.kk harness layout unchanged in behavior.
- [ ] **Step 5:** `owner-rect` walk (in widget.kk): descend accumulating (x,y) like `each-anchor`; return the first node whose `owner == id.int32` with its (x,y,w,h). Add a companion `owner-texts(t, id)` (collect LText content under nodes whose owner is `id` OR a descendant identity — for the tester's texts; "descendant identity" = the subtree rooted at the shallowest owner==id node, so texts is just "all LText in that subtree").
- [ ] **Step 6:** GREEN: full existing matrix unchanged — the string addressing (keyed/anchored/Region, each-anchor) still works untouched; owner is stored but only owner-rect reads it, and nothing calls owner-rect yet. Run headless basic/retain/windows/lazy/lazy-oversize; native live ×2; web live pass:9; wasi-web basic (node 24). Bench check: `lib/ui/bench/reuse.kk` reconcile reuse counts unchanged (owner is a value field, reused in place).
- [ ] **Step 7:** commit `git commit -am "ui: owner identity on every widget/ltree node (captured at build, flowed through layout)"`.

### Task 3: tester → selectors + owner-rect; migrate test call sites

**Files:** `lib/ui/test.kk`, `lib/ui/test-live.kk`, `test/ui/*.kk`.

- [ ] **Step 1:** Rewire the tester: `find(sel)`/`click(sel)`/`texts(sel)` resolve `find-ids(sel)` (under the harness's keytree) → error on ambiguity (print the matching `segment/show` paths) → `owner-rect`/`owner-texts` over the current scene ltree. The live driver's window-offset routing (the synthetic-offset combined tree) stays; it now offsets by owner-rect results. Coordinate/scroll/key actions unchanged.
- [ ] **Step 2:** Migrate `test/ui/*.kk` addressing: every `keyed("x", w)` that a scenario addresses becomes an identity mint — either the enclosing component already has `scope("x")` (drop the keyed) or the leaf gains `?key = scope("x")`. Scenario `find/click/texts` names become selectors (bare names for unique scopes; `"list :i"` for rows). Lazy tests drop per-row `keyed("row-"++i.show)` for `idx(i)` addressed as `"rows :i"`.
- [ ] **Step 3:** GREEN: all headless UI tests (×4 runtimes) + native live ×2 + web live at the SAME check counts, now selector-addressed. `keyed`/`Region` still exist (removed T4/T5) but tests no longer depend on them for addressing.
- [ ] **Step 4:** commit `git commit -am "ui/test: selector addressing over owner geometry; migrate test call sites"`.

### Task 4: `Scope` anchor target; remove `Region`

**Files:** `lib/ui/view.kk`, `lib/ui/state.kk`/`lib/ui/reactive.kk` (anchor registry → int-keyed), both backends (scroll-region rect publication → int-keyed), `samples/ui/overlay`, `samples/ui/windows`.

- [ ] **Step 1:** `pub type target { Display; Scope( sel : string ) }` (Region deleted). `view/layers`/`compose`/`place-panel` resolve `Scope(sel)` via `find-ids` + `owner-rect` against the current tree (not the previous-frame string registry). Panel placement + auto-scrollbar anchoring read owner-rect for their region ids (int, no `id.show` bridge).
- [ ] **Step 2:** The string anchor registry (`publish-anchor-rect(k:string,...)`/`all-anchor-rects`/`set-anchor`/`list-anchors`) becomes int-keyed OR is dropped if owner-rect subsumes it (scrollbar metrics still need per-region content/viewport, which live in scroll-state, not the anchor registry — verify what still needs a registry vs. what owner-rect now answers directly, and delete what's dead).
- [ ] **Step 3:** Migrate samples/tests using `target = Region(...)` to `Scope(...)`.
- [ ] **Step 4:** GREEN: overlay + windows samples (native 30-frame + jsweb load), windows live scenario (Panel anchors), full suite.
- [ ] **Step 5:** commit `git commit -am "ui/view: Scope anchor targets over owner geometry; remove Region"`.

### Task 5: remove `keyed`/`anchored`/`Keyed`/`LKeyed`; `LLayer` marker

**Files:** `lib/ui/widget.kk`, both backends, `lib/ui/view.kk`, remaining `test/ui/*`, `samples/*`.

- [ ] **Step 1:** New `LLayer( owner, w, h, kids )` ltree ctor (identical to LFlex in every walk; the web lowering styles it pointer-transparent — the `kk:layer` case). Positioned's layout emits `LLayer` instead of `LKeyed("kk:layer", ...)`. Both backends' walks gain the LLayer arm; web lowering moves the pointer-transparent style there.
- [ ] **Step 2:** Delete `keyed`, `anchored` (funs), `Keyed` (widget ctor), `LKeyed` (ltree ctor), and their arms in every walk. Delete the string-name `each-anchor` walk and any residual string anchor registry surface. `scroll(name=...)` keeps its `Named` segment (unchanged).
- [ ] **Step 3:** Migrate every remaining `keyed(`/`anchored(` call site (samples/ui/*, samples/web-ui/* if any, docs snippets) to scope mints or deletion.
- [ ] **Step 4:** GREEN: full suite (×4 runtimes, live ×2, web pass:9), all samples smoke (native 30-frame + jsweb load for the web-ui/ui samples).
- [ ] **Step 5:** commit `git commit -am "ui: remove keyed/anchored/Region; LLayer marker (one identity system)"`.

### Task 6: docs + ledger + measurement

**Files:** `docs/ui/design-notes.md` (§14), `docs/ui/paper-outline.md`.

- [ ] **Step 1:** Ledger §14 (terse): owner-on-every-node (why STORED not derived — the no-keytree-at-walk-time argument); selector addressing; keyed/Region removed = one identity system; the 4-byte/node cost + bench reuse-count-unchanged measurement; the "finishing 1c" note (smart ctors now take `?key`). Outline: claims row (`Owner identity + selector addressing: one identity system, no dual-tagging | ledger §14`), and update section 3 (identity-by-implicits) to mention owner completes it.
- [ ] **Step 2:** commit `git commit -am "docs: ledger 14 -- owner identity + selector addressing"`.

## Self-review notes
- Spec coverage: kt-find/selectors (T1), owner field + capture-at-build + owner-rect (T2), tester rewire + migration (T3), Scope/Region (T4), keyed/anchored/LKeyed removal + LLayer (T5), docs (T6). Removal policy honored (delete + migrate, no shims).
- Green-between-tasks: T2 adds owner additively (old string addressing still works), so the suite is green before the tester even uses owner; T3–T5 swap over and remove.
- The atomic risk is isolated to T2 with an explicit split-if-blocked instruction and a suggested 2a/2b boundary.
- Type consistency: `owner : int32` first field everywhere; `owner-rect`/`owner-texts`/`find-ids`/`kt-find`/`sel-step` names used identically across T1–T5; `Scope(sel)`/`LLayer(owner,w,h,kids)` consistent T4/T5.
