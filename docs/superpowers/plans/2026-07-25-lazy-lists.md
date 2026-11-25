# Builder Lists (`lazy-column`) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `lazy-column` per `docs/superpowers/specs/2026-07-25-lazy-lists-design.md` — on-demand item building over the unified scroll model, with the key-retention machinery as the recycler; infinite lists included.

**Architecture:** A pure combinator in a new `lib/ui/lazy.kk`: window off last-frame scroll metrics → build only `idx(i)`-keyed items inside a `kt-open`/`kt-close` consumption boundary → lower to existing `scroll(column(spacer ++ items ++ spacer))`. No new ltree nodes; no backend changes.

**Tech Stack:** Koka (lib/ui), existing test tiers.

## Global Constraints

- API exactly as the spec: `lazy-column(item, count = Nothing, item-extent = 40.0, cache = 4, keep = Transient, name = "", ?key, ?kk-file-line)`; `item-extent` documented as the extent ESTIMATE (exact in this MVP).
- `keep` uniform per list, stamped on each `idx(i)` at mint; document that nested KeepAlive under a Transient item does not survive scroll-out.
- Zero new ltree nodes, zero backend changes; spacers are `rect(0.0, h)`, column `gap = 0.0`.
- Bounded content height EXACT (`count * item-extent`); infinite = one viewport ahead (`(first + n + visible) * item-extent`).
- Koka gotchas: named local funs; `ctx`/`use`/`raw` reserved; effectful default args don't auto-call providers; LOCAL .koka caches; headless run idiom `stack exec koka -- -v0 --console=raw -ilib -itest/ui -e test/ui/<t>.kk`.

## File Map

| File | Change |
|---|---|
| `lib/ui/lazy.kk` | NEW: the combinator |
| `test/ui/lazy.kk` | NEW: deep headless tests (window size, exact height, recycling, infinite) |
| `test/ui/basic.kk` | small lazy region + one shared scenario (rides ALL tiers) |
| `util/test-wasi.sh` | web-live pin `uitest:pass:7` → the new count |
| `samples/ui/lazy/` | 10k demo + build.kk + .gitignore + readme |
| `docs/ui/design-notes.md`, `docs/ui/paper-outline.md` | ledger §13, claims row |

---

### Task 1: `lib/ui/lazy.kk` + deep headless tests

**Files:** Create `lib/ui/lazy.kk`, `test/ui/lazy.kk`.

**Interfaces (produces):** the spec's `lazy-column` signature, verbatim.

- [ ] **Step 1: write the combinator.** Starting shape (the implementer owns final details; deviations reported):

```koka
module ui/lazy
import std/num/float64
import ui/keytrie
import ui/widget
import ui/state

pub fun lazy-column<msg>( item : (int, key) -> <keytree,uistate,ioc> widget<msg>,
                          count : maybe<int> = Nothing,
                          item-extent : float64 = 40.0,
                          cache : int = 4,
                          keep : keep = Transient,
                          name : string = "",
                          ?key : key, ?kk-file-line : string ) : <keytree,uistate,ioc> widget<msg>
  val sk = scroll-key(name, ?key = ?key, ?kk-file-line = ?kk-file-line)
  val st = scroll-state(sk)
  val lk = kt-child(?key, Slot("lz", ?kk-file-line))   // items are lk's ONLY children
  val vis = if st.viewport > 0.0 then (st.viewport / item-extent).ceiling.int + 1 else 1
  val first = ((st.offset / item-extent).int - cache).max(0)
  val n0 = vis + 2 * cache
  val (n, total) = match count
    Just(c) -> ((n0.min(c - first)).max(0), c)
    Nothing -> (n0, first + n0 + vis)                  // infinite: one page ahead
  kt-open(lk.key-id)
  fun build-item( i : int ) : <keytree,uistate,ioc> widget<msg>
    // items must respect item-extent (documented); the stack pins the height
    stack([ (0.0, 0.0, rect(0.0, item-extent)),
            (0.0, 0.0, item(i, idx(i, keep = keep, ?key = lk))) ])
  val items = list(first, first + n - 1).map(build-item)
  val pruned = kt-close(lk.key-id)
  if !pruned.is-nil then drop-ids(pruned)
  val lead  = rect(0.0, first.float64 * item-extent)
  val trail = rect(0.0, ((total - first - n).max(0)).float64 * item-extent)
  scroll( column([lead] ++ items ++ [trail], gap = 0.0), name = name )
```

Verify against reality: `scroll-key`/`scroll-state` signatures (ui/widget:217 / ui/state), `idx(i, keep, ?key)` (ui/ident), `kt-open/kt-close/drop-ids` usage in `memo-run` (ui/state:~406), `ceiling` on float64, `stack` entry shape, `rect` signature, `column(gap=)`. `scroll(name=name)` must reuse `sk` — if `scroll` re-mints a DIFFERENT key for empty names, pass the same `name`/key path so metrics land on the key the windowing reads (this is the one wiring subtlety: the region key READ must equal the region key SCROLLED — write a comment proving it).

- [ ] **Step 2: failing tests first** — `test/ui/lazy.kk`, a `test-scenarios` app:
  - model-free app: `lazy-column` of `Just(10000)` items, each `keyed("row-" ++ i.show, text("row " ++ i.show))` with a `use-state` bump counter behind an `act` (mirror test/ui/retain.kk's pane shape) — expose two lists: one `keep = Transient` (name "tl"), one `keep = KeepAlive` (name "kl"); plus one infinite list (name "inf").
  - `window`: only ~`vis + 2*cache` rows materialize (assert `t.texts("row-0")` exists, `t.texts("row-100")` empty; count materialized via a helper — e.g. assert row-k present iff k < n0).
  - `exact-height`: `scroll-state` content == `10000 * extent` after settle.
  - `moved`: `t.scroll("tl", -large)` then assert early rows gone, later rows present.
  - `recycle`: bump row 2's counter in BOTH lists, scroll far, scroll back: Transient reset, KeepAlive kept.
  - `infinite`: scroll "inf" far; content grew ahead of offset (scroll-state content > offset + viewport).
- [ ] **Step 3:** run `stack exec koka -- -v0 --console=raw -ilib -itest/ui -e test/ui/lazy.kk` until green; then basic/retain/windows unchanged.
- [ ] **Step 4:** commit `git commit -am "ui/lazy: builder lists -- windowed items over the unified scroll model"` (add both new files).

### Task 2: all-tier scenario + suite pins

**Files:** Modify `test/ui/basic.kk`, `util/test-wasi.sh`.

- [ ] **Step 1:** basic.kk shared app gains a SMALL lazy region (e.g. `keyed("lz", lazy-column(fn(i, k) keyed("lz-" ++ i.show, text("lz " ++ i.show)), count = Just(200), item-extent = 20.0, name = "lz"))` inside the existing layout — placed so it does not disturb existing scenario coordinates (append below "lines" or swap the "lines" region's content? DO NOT change existing checks: append as a new region after the existing ones, inside the expanded area or a second expanded row — verify existing 7 checks still pass before adding the new scenario).
- [ ] **Step 2:** one new shared scenario `lazy`: assert `lz-0` present + `lz-150` absent; `t.scroll("lz", -1200.0)`; settle; assert a later row materialized. Add to `shared-scenarios`.
- [ ] **Step 3:** counts: headless basic (new total), native live, web live — update util/test-wasi.sh's `uitest:pass:7` pin to the new count. Run: headless basic; native live both invocations; web live via the suite's chrome idiom.
- [ ] **Step 4:** full suite `./util/test-wasi.sh` green (known kklib first-run flakes rerun individually; #46 typing flake reruns).
- [ ] **Step 5:** commit `git commit -am "ui/test: lazy-list scenario on every tier"`.

### Task 3: sample + docs + bookkeeping

**Files:** Create `samples/ui/lazy/{main.kk,build.kk,.gitignore,readme.md}`; modify `util/test-wasi.sh` (native smoke list), `docs/ui/design-notes.md` (§13), `docs/ui/paper-outline.md`.

- [ ] **Step 1:** demo: a 100k-row styled list (page/card idiom from samples/ui/threads) with a per-row bump counter and a `keep = KeepAlive` toggle pair (two lists side by side), plus an infinite feed tab-like second region; `--rows=n` optional arg unnecessary — keep static. build.kk = copy of samples/ui/threads/build.kk; .gitignore = `app-native`, `out*/`, `.koka/`.
- [ ] **Step 2:** native smoke `KOKA_IMP_FRAMES=60` exit 0; add `lazy` to the suite's native sample list; jsweb build loads in headless Chrome without console errors.
- [ ] **Step 3:** ledger §13 (terse: what landed, the window arithmetic, the recycling client, the keep-per-list decision + follow-up, measurement note: materialized window independent of count); outline claims row (`Builder lists ... implemented + tested`); mark task #47 completed.
- [ ] **Step 4:** commit `git commit -am "samples/ui/lazy + ledger 13: builder lists land"`.

## Self-review notes
- Spec coverage: API/infinite/keep semantics (T1), windowing + spacers + boundary (T1), all-tier scenario (T2), sample + ledger + measurement (T3). Cuts respected (no variable extents, no per-item keep, vertical only).
- The one wiring subtlety (windowing reads the SAME region key scroll writes) is called out in T1 with a required comment.
- Type consistency: `lazy-column` signature identical in T1 code and spec; scenario names `tl`/`kl`/`inf`/`lz` used consistently.
