# Web Scroll Takeover Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Koka-owned scrolling on the web backends (jsweb + wasi-web), per `docs/superpowers/specs/2026-07-24-web-scroll-takeover-design.md` — one scroll model everywhere, no escape hatch.

**Architecture:** The `overflow:auto` lowering becomes clip + baked-offset `translate3d`; `bake-scroll` and the wheel clamp/apply core hoist into `ui/state` and both backends call them; a root wheel listener (preventDefault, deltaMode-normalized) posts `EvWheel` into the existing pump; web publishes scroll metrics so the composer's scrollbar views appear there unchanged; the browser-owned-scroll test gates come out.

**Tech Stack:** Koka (lib/ui, lib/web-ui), JS (jsweb dom.js), C + JS host table (wasiweb dom.c / web-ui-host.js).

## Global Constraints

- NO escape hatch / per-region browser-scroll fallback (Tim, spec): the overflow:auto path is DELETED, not gated.
- Wheel-first scope: touch physics / keyboard paging / rubber-band are explicit non-goals of this change.
- Shared logic has ONE home: the offset-bake walk and the wheel clamp/apply core live in `ui/state`; backends may not carry private copies.
- Wheel deltas normalized by `deltaMode` (0 pixel ⇒ ×1, 1 line ⇒ ×16, 2 page ⇒ ×viewport-height... use ×16/×viewport approximations noted in code) before they reach Koka.
- The wheel listener must `preventDefault()` (the page must not scroll behind the app); register non-passive.
- jsweb and wasi-web host files change in lockstep (dom.js ↔ dom.c + web-ui-host.js koka:dom table).
- Native behavior unchanged: full suite green; the shared-hoist refactor is invisible to impeller.
- Koka gotchas: named local funs (no multi-line paren lambdas); don't spell effect rows needlessly; touch the owning .kk when a bundled .js changes or it won't rebuild; clear LOCAL .koka caches on stale weirdness.

## File Map

| File | Change |
|---|---|
| `lib/ui/state.kk` | + `bake-scroll` (moved from impeller backend), + `apply-wheel` (clamp/apply core from native drain-scroll) |
| `lib/ui/api/impeller/backend.kk` | use the shared fns (delete private copies) |
| `lib/ui/api/web/backend.kk` | LScroll lowering (clip+translate), bake at render, metrics publication, `EvWheel` + pump arm, wheel subscribe |
| `lib/web-ui/api/jsweb/dom.js` + `dom.kk` | `event-wheel-dx/dy` (normalized), non-passive wheel subscribe support, inject-wheel → real WheelEvent dispatch |
| `lib/web-ui/api/wasiweb/dom.c` + `support/wasi-web/web-ui-host.js` | same surface, host-table side |
| `test/ui/basic.kk` | scroll scenario joins `shared-scenarios` (no web gating) |
| `test/ui/live/main.kk` | drop the web scroll gate |
| `util/test-wasi.sh` | web live expectation 6 → 7 checks |
| `docs/ui/design-notes.md` | ledger entry 12 |

---

### Task 1: hoist `bake-scroll` + `apply-wheel` into ui/state (native refactor, behavior-preserving)

**Files:** Modify `lib/ui/state.kk`, `lib/ui/api/impeller/backend.kk:184-200` (bake-scroll), `:499-514` (drain-scroll core). Test: existing suites.

**Interfaces (produces):**
```koka
// ui/state — the ONE offset-bake walk: write each region's clamped ui/state
// offset (and each field's live text) into the laid-out tree
pub fun bake-scroll<msg>( t : ltree<msg> ) : <uistate,ioc> ltree<msg>
// ui/state — the ONE wheel application: region under (x,y), horizontal
// consumes dx (falling back to dy), clamp, write; True if the offset changed
pub fun apply-wheel<msg>( t : ltree<msg>, x : float64, y : float64,
                          dx : float64, dy : float64 ) : <uistate,ioc,exn> bool
```

- [ ] **Step 1:** Move the impeller backend's `bake-scroll` walk verbatim into `lib/ui/state.kk` (it reads `scroll-offset`/`field-text` — both ui/state ops; the ltree ctors come from ui/widget which state already imports). Export `pub`. Delete the backend copy; the backend calls `ui/state/bake-scroll`.
- [ ] **Step 2:** Extract native `drain-scroll`'s core into `apply-wheel` in ui/state (the `scroll-at` walk + horizontal dx-fallback + clamp + `set-scroll-offset`, returning changed?). Rewrite the backend's `drain-scroll` as: take deltas from the host rings; `if apply-wheel(tree-for(...), cursor-x, cursor-y, dx, dy) then request-render()`.
- [ ] **Step 3:** Gates: headless basic/retain/windows green; native live `./test-live` 7/7; one sample smoke (scroll sample: `samples/ui/scroll`, KOKA_IMP_FRAMES=30, exit 0).
- [ ] **Step 4:** Commit `git commit -am "ui/state: shared bake-scroll + apply-wheel (hoisted from the impeller backend)"`.

### Task 2: web lowering + baked offsets + metrics (scrollbars appear on web)

**Files:** Modify `lib/ui/api/web/backend.kk` (LScroll arm ~:334, `mount`/`render`). Test: headless + jsweb sample probe.

- [ ] **Step 1:** LScroll lowering: replace the overflow:auto viewport with
```
clip div: pos-style(x, y, w0, h0) ++ ";overflow:hidden"
inner div: "position:relative;width:<inner-w>;height:<inner-h>;transform:translate3d(" ++
           (if horizontal then "-" ++ px(offset) ++ ",0," else "0,-" ++ px(offset) ++ ",") ++ "0)"
```
using the node's baked `offset` field (the arm currently ignores it with `_`).
- [ ] **Step 2:** In web `mount` and `render`, bake before lowering: `val laid = w.laid-out(tight(cw, ch)).bake-scroll` (both call sites), and publish metrics after layout: reuse the impeller backend's `sync-scroll-metrics` — MOVE it too into ui/state (same shared-home rule; it walks `each-scroll` + `publish-scroll-metrics`, all shared) and call it from web render/mount: `if sync-scroll-metrics(laid) then request-render()`. Also publish each scroll region's RECT into the anchor registry the way native does (grep impeller backend for the scroll-rect anchor bridging — `id.show` keyed — and mirror it in web's `publish-anchors` walk).
- [ ] **Step 3:** Verify auto scrollbars: `samples/ui/scroll` built for jsweb (`stack exec koka -- -v0 --console=raw -e build.kk -- jsweb` in that sample dir) — load the page in headless Chrome (grep util/test-wasi.sh for the chrome invocation idiom) and assert the page still renders (title/self-test if the sample has one). Scroll behavior itself lands with Task 3; this task only requires the offset-translate lowering to render at offset 0 and metrics to publish.
- [ ] **Step 4:** Headless suites green (basic scroll scenario still headless-only here). Commit `git commit -am "ui/web: clipped+translated scroll lowering, baked offsets, shared metrics"`.

### Task 3: wheel input end-to-end (both hosts) + inject path

**Files:** Modify `lib/ui/api/web/backend.kk` (web-ev + pump + subscribe), `lib/web-ui/api/jsweb/dom.js` + `lib/web-ui/api/jsweb/dom.kk` (or wherever the dom externs live — grep `event-xy`), `lib/web-ui/api/wasiweb/dom.c`, `support/wasi-web/web-ui-host.js`.

- [ ] **Step 1:** dom surface: add `event-wheel-dx() : ioc float64` / `event-wheel-dy() : ioc float64` reading the CURRENT event's deltaX/deltaY normalized by deltaMode (0 ⇒ ×1; 1 ⇒ ×16; 2 ⇒ ×window.innerHeight), and make the wheel subscription non-passive + preventDefault. Follow the existing `kk_dom_subscribe` shape; either extend it with an options flag for "wheel" or add `kk_dom_subscribe_wheel(el, action)` that registers `{passive:false}`, calls `e.preventDefault()`, and stashes the event for the `current-event`/`event-xy` readers exactly as other listeners do (read dom.js:100-125 first and copy its stash discipline). Mirror in dom.c + web-ui-host.js.
- [ ] **Step 2:** backend: `EvWheel( x : float64, y : float64, dx : float64, dy : float64 )` ctor on `web-ev`; subscribe at mount next to the other root listeners: the callback posts `EvWheel` with `event-xy()` + the two deltas. Pump arm: `EvWheel(x, y, dx, dy) -> if apply-wheel(!m.tree, x, y, dx, dy) then request-render()`.
- [ ] **Step 3:** test inject: rewrite `kk_dom_inject_wheel` to dispatch a real `window.WheelEvent("wheel", {clientX, clientY, deltaY, bubbles:true, cancelable:true})` on the element at the point (setTimeout(0)-deferred like the other injectors; window.WheelEvent — module scope shadows bare names). Delete the scroller-search/scrollTop code. Mirror in dom.c/host table. NOTE untrusted-event rule: a synthetic wheel fires listeners but performs no default scroll — which is exactly right now that OUR listener does the scrolling.
- [ ] **Step 4:** Probe: `samples/ui/scroll` jsweb in headless Chrome — if the sample has a self-test drive extend it minimally, else verify via the Task 4 live tier instead (do not build a bespoke probe if Task 4's un-gated scenario covers it — it does; treat this step as "compiles + page renders").
- [ ] **Step 5:** Touch the owning .kk files for changed .js payloads. Commit `git commit -am "ui/web: koka-owned wheel scrolling (both hosts); synthetic wheel injection"`.

### Task 4: un-gate the scroll tests

**Files:** Modify `test/ui/basic.kk` (scroll scenario into `shared-scenarios`), `test/ui/live/main.kk` (drop its web gate), `util/test-wasi.sh` (web live `uitest:pass:6` → `uitest:pass:7`; check the exact probe string near the web-live block).

- [ ] **Step 1:** Move `("scroll", scroll-scenario)` from the native-only append into `shared-scenarios` in basic.kk; remove the web gating in test/ui/live/main.kk (grep `test-backend` there).
- [ ] **Step 2:** Gates: headless basic 7/7 (unchanged count — scroll was already in headless main); native live 7/7; **web live now 7 checks**: build + run the web live tier exactly as util/test-wasi.sh's web block does (serve out-js, headless Chrome, title probe) and update the expected title count.
- [ ] **Step 3:** Full suite `./util/test-wasi.sh` — green (known kklib first-run flakes excepted; also note task #46's typing flake may fire once — rerun that check to confirm flake vs regression).
- [ ] **Step 4:** Commit `git commit -am "ui/test: scroll scenario runs on every tier (web scrolling is ours now)"`.

### Task 5: ledger + outline + task bookkeeping

**Files:** `docs/ui/design-notes.md` (entry 12: what landed, deltaMode table, deletions, watched regressions incl. scroll-feel + no-compositing measurement note), `docs/ui/paper-outline.md` (testing/eval sections: web scroll un-gated; one-scroll-model claim), task #48 → completed, #47 unblocked.

- [ ] **Step 1:** Write ledger entry 12 in the ledger's terse style; update the outline's claims ledger (one scroll model row) and anywhere that says web scrolling is browser-owned (grep both docs).
- [ ] **Step 2:** Commit `git commit -am "docs: ledger 12 -- web scroll takeover"`.

## Self-review notes
- Spec coverage: lowering (T2), shared bake/apply (T1), wheel listener + normalization + preventDefault (T3), metrics/scrollbars on web (T2), inject + un-gating + suite counts (T3/T4), deletions (T2/T3), both hosts (T3), ledger (T5). No escape hatch anywhere.
- Type consistency: `apply-wheel(t, x, y, dx, dy) : bool` used identically in T1 (native) and T3 (web pump); `bake-scroll`/`sync-scroll-metrics` shared names in T1/T2.
- The scroll-feel/compositing measurement is a ledger note (T5), not a hard gate — it needs human eyeballing.
