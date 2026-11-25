# Paper outline: "Effects All the Way Down: A Portable Reactive UI Framework in Koka"

Status: outline + claims ledger (2026-07-23). Target venue: ICFP (full paper;
fallback: experience report). Evidence sources: `docs/ui/design-notes.md`
(the design ledger, cited below as §N), `lib/ui/bench/readme.md`, the `ui`
branch itself, and upstream PRs #909/#910/#911/#913.

## Thesis

Reactive UI frameworks are effect systems implemented extralinguistically:
dependency tracking, identity, scheduling, cancellation, and portals are all
runtime machinery with rules the host language cannot check (hooks ordering,
"don't set state during render", manual keys, z-index arithmetic). In a
language with algebraic effects, implicit parameters, and Perceus reference
counting, the framework becomes a library and the invariants become types —
and the result is portable across native (Impeller), JS, and wasm hosts from
one source tree.

## Section outline

1. **Introduction.** The extralinguistic-machinery argument; contributions:
   (a) identity by implicit resolution (no hooks rule, no manual keys),
   (b) the unified view/scene model (portals as an effect; overlays,
   scrollbars, drag ghosts, windows are one concept),
   (c) A′ memoization: recorded-read invalidation with constraint-conditioned
   reuse, and the negative result that shaped it (continuations freeze
   `effect val` evidence),
   (d) in-place FBIP reconciliation of the retained tree,
   (e) threading: per-thread async loops and a batched backpressure
   protocol expressed at the library level (strands + channels) whose
   batch amortization beats per-item crossings on the same C transport,
   (f) testing by handler substitution: one script, three execution tiers,
   (g) evaluation incl. a Flutter twin.

2. **The framework by example.** Counter → todos. The effect rows and what
   each buys: `keytree` (identity), `uistate` (ephemeral state + tracked
   reads), `scene` (view emission), `async` (strands/channels). A view is
   `(model, key) -> <keytree,uistate,scene<msg>,ioc> widget<msg>`; smaller
   rows subsume, so pure views stay pure.

3. **Identity by implicits.** Leaves take `?key`; the compiler-supplied
   `?kk-file-line` makes each call site a distinct stable identity — no React
   positional-hooks rule, no key strings. Components take an explicit
   required `key : key` (minted by `here()`/`idx(i)`/`scope(name)`) whose
   *name* makes bodies derive by innermost implicit resolution. Keytrie ids:
   integer identities that survive rebuilds, zero per-frame key strings.
   Design-space narrative from probe 1 (§1, §1b, §1c): the rejected
   dot-implicit and val-rebind designs and why passthrough chains kill them;
   the dot-unpack compiler improvement the framework forced (PR #911).
   Also: `?bg`/`?fg` styling leaves, simple/widget overloading, effectful
   defaults. Because identity is a first-class key rather than a mounted
   instance, STATE LIFETIME decouples from mounting: retention is a policy
   on the key (`scope(name, keep = KeepAlive)` — Transient prunes on
   unmount, KeepAlive moves the subtree — cells, memo cache, dirt — to a
   cold `retained` list, out of layout/paint entirely, and remount by the
   same path finds everything intact; eviction is a handler knob, not API).
   Contrast: React ties state to the mounted element (retain = keep it
   mounted or lift it out); Flutter needs AutomaticKeepAliveClientMixin /
   PageStorage / IndexedStack; Vue's keep-alive caches whole instances at a
   wrapper site. Ours is per-identity, typed, and handler-swappable
   (spec: samples/ui/aprime README — keep policy, unmount-by-consumption).

4. **Everything is a view.** The scene effect: `overlay(...)`/`emit-view`
   emits a portal *inline from anywhere*; the app-owned scene handler
   composes all views at the root with relative z (Attached < Popover <
   Modal < Window). Scrollbars are auto-emitted views anchored to published
   scroll rects; the drag ghost is a top-layer view; native multi-window is
   the same concept with no API change. No portal component, no prop
   drilling, no z-index. Effect polymorphism keeps the API uninfected.

5. **A′ memoization** (technical core). `memo(build, ?key)` boundaries;
   uistate reads record (channel → innermost boundary) edges; writes collect
   readers; subtree-dirty bits propagate in the keytrie zipper; reuse
   requires ptr-eq *and* same-constraints (the relayout-boundary rule
   Flutter keeps internal, surfaced as a checkable condition). Paint epochs
   + hover-locality for repaint boundaries; the clock-subscription rule
   (deps only while an animation is unsettled). The keystone negative
   result (§8): a stored continuation freezes `effect val` evidence, so
   ambient state must be dynamic ops and re-execution must be top-down —
   this dictates the whole design. Motivating war stories: the repaint
   "rainbow" bugs, each traceable to a wrong effect operation (visible in
   types), invisible in signal frameworks.

6. **FBIP reconciliation.** The ltree is single-thread-owned; match-and-
   reconstruct compiles to in-place update (Perceus reuse; companion:
   copy-fbip PR #909). Bench methodology + the measurement-error correction
   note.

7. **Concurrency.** Async as a handler over single-shot continuations;
   cancellation as handler unwinding. The platform/render thread split
   (§6): main owns only Cocoa/GLFW; the whole app runs on a render thread;
   live re-layout during the modal resize drag. `bchannel`: batched
   backpressure written at the Koka library level over a minimal C
   xchannel transport — grants pooled per producer, no idle-flush (with a
   liveness argument). The interesting claim is NOT "Koka beats C" (Koka
   compiles to C); it is that the batching protocol — one mark-shared/
   mutex/uv-wakeup per batch instead of per item — is naturally expressed
   with strands and effects at the library level, and beats per-item use
   of the same transport 3×. Briefly: the Perceus thread-safety work that
   made cross-thread values sound (shared-refcount fixes, regression test
   `test/async/xthread-stress.kk`).
   wasi-threads in the browser: pthreads over a ~50-line worker shim.

8. **Testing as handler substitution.** The headless harness is the app
   runtime minus the platform: deterministic text metrics and clock are
   handler swaps. The live tier injects at the host fringe (same GLFW rings
   / real DOM events). One script runs headless-C, headless-JS, native-live,
   web-live. Four production bugs found by the framework itself (LField
   burst, LInput burst, web on-enter never wired, the -O1 thread race).

9. **Evaluation.** Flutter twin (CPU; re-run post-memo, add memory + frame
   times); memo on/off/pre (CPU, memory, tracking cost); reconcile
   allocation counts; bchannel throughput; profiles before/after (§7).

10. **Related work.** Adapton / incremental & demanded computation (A′ is
    close kin — must engage seriously), Elm, React/hooks, SolidJS/signals,
    Flutter internals (relayout/repaint boundaries), FRP (Fran/Yampa),
    Ur/Web, multitier FP, Perceus/FBIP papers.

11. **Limitations & future.** Manual memo boundaries; accessibility absent (designed, not built: default components emit default semantics through
    the effect stack into a sparse keytrie projection — int-map from stable
    key ids, parentage by key-path prefix — gated by an enable flag whose
    flip is a dirty storm; memo boundaries cache their semantics fragment
    exactly as they cache layout + display lists, making the third uniformly
    invalidated artifact; web lowers to ARIA. Note for the evaluation:
    Flutter builds semantics lazily on assistive-tech activation, so the
    twin numbers compare like with like);
    single-line text editing; wasi-web async tier (task #41); -O1 startup
    race (task #44) unless closed; component-embedding stability for memo
    (map-msg defeats ptr-eq); native out-of-window windows (OwnWindow)
    landed -- remaining: titled-window anchoring, cross-window drag.

## Claims ledger

**Measurement vintage:** every UI perf number below predates the RETENTION
commit (keytrie keep-alive, 2026-07-23, ledger §10), which changed the
identity hot path: `knode` grew three fields, a descend miss now scans
stale + retained lists, and every memo re-run does kt-open/kt-close work.
Expected impact is small (empty lists on non-retaining apps) but NOT
measured -- re-run before quoting: the Flutter twin round 2, the memo
on/off/pre CPU numbers, the memodemo -25%, and the identity-derivation
microbench (aprime keytrie-bench). The reconcile bench (ltree passes, no
identity minting in the hot loop) and the bchannel/threading numbers are
unaffected.

| Claim | Evidence | Status |
|---|---|---|
| Dependency tracking is free | memo-off ≈ pre-memo CPU (36% vs 37%), this session | measured, pre-retention |
| Memoization: 37%→20% CPU animating, −5MB | full-app run, this session | measured, pre-retention |
| Boundary re-records 2×/240 frames when quiescent | memodemo + debug traces | measured |
| Reconcile reuses in place: node cells 8.0M→400 allocs, −46% bytes, −25% time | `lib/ui/bench/readme.md` | measured (incl. correction note) |
| Flutter twin, post-memo: koka ≤ flutter in all 10 adjacent pairs (cool ~7% both; warm koka 10.3–11.3 vs flutter 12.4–13.7); was 4.8× behind pre-memo | flutter-twin/README.md round 2 (occlusion-controlled protocol) | measured 2026-07-23, PRE-retention build — re-run |
| batched backpressure 0.02s vs per-item xchannel use 0.07s vs naive protocol 3.6s (200k ints, same C transport) | memory/project_ui_threading; test/async/bchannel*.kk | measured |
| Threaded app mode works | `app(threads=Threaded)` verified ~110 renders/6s | measured; #44 residue at -O1 |
| Four cross-thread Perceus bugs, 0/30 repro after fix | test/async/xthread-stress.kk | measured |
| Portals from anywhere via scene effect, cross-backend | samples/ui/overlay self-test | implemented + tested |
| Identity without hooks rule or key strings | keytrie + probes 1/1b/1c; ledger §1 | implemented; needs worked-example prose |
| Continuations freeze `effect val` evidence | samples/ui/aprime research/4 | demonstrated (keystone experiment) |
| One script, three tiers; found 4 real bugs | util/test-wasi.sh 32/0; ledger entries 07-17/18 | measured |
| One scroll model on every backend (koka-owned web scrolling; scroll scenario on all tiers) | ledger §12; web live 7/7 | implemented + tested 2026-07-25 |
| Event-driven input: 0.0% idle CPU, 120fps ProMotion | ledger 07-17 arc | measured |
| Reuse condition = ptr-eq ∧ same-constraints is sound | code + traces only | **needs semi-formal statement + argument** |
| Unmounted-state retention as a per-key policy (tab state survives unmount) | ui/keytrie + ui/state; test/ui/retain.kk (9/9); ledger §10 | implemented + tested 2026-07-23 |
| Owner identity on every node + selector addressing (one identity system, no dual-tagging; keyed/Region removed) | owner:int32 everywhere; kt-find; ledger §14; suite green | implemented + tested 2026-07-26 |
| OwnWindow: native multi-window (`window(...)`, Panel chrome) | test/ui/windows.kk (headless + live); samples/ui/windows; ledger §11 | implemented + smoke/live-tested; remaining: titled anchoring, cross-window drag |
| Builder lists (lazy-column): windowed items + retention-machinery recycling | test/ui/lazy.kk 24/24 all tiers; ledger §13 | implemented + tested 2026-07-25 |
| transform3d: 4x4 projected-2D paint transform with ACCURATE (unprojected) hit-testing, in the same cut | ui/transform (mat4/unproject); ledger §15; samples/ui/gallery flip-card | implemented + tested 2026-07-26; native pixel-verify is a build+run smoke only (no screen-capture in this sandbox) |
| Images: native decode (stb_image) + identity-cached GPU textures freed by the SAME retention machinery as tabs/windows/lists | ui/image; ledger §10, §15; samples/ui/gallery image row | implemented + tested 2026-07-26; native-paths-only (no URL fetch, task #53 pending) + synchronous first-paint decode caveats stand |
| Async boundary (Suspense/FutureBuilder for Koka): one generation mechanism = retry + deps + cancellation-floor; `image` rebuilt on it (off-thread decode, on-thread upload, Sync kept); boundary reads free-ride ui/reactive's dep tracking under memo | ui/async (async-snapshot/future-boundary/async-pump); test/ui/async-boundary.kk; test/ui/live async-image(-web) scenarios; ledger §16 | implemented + tested 2026-07-27 (headless + native live + web live); jsweb-only gaps found+scoped OUT, not fixed: task #55 (reentrant fork never runs, so the general primitive is native-only for now) + task #56 (page()-scroll regression on the plain image row); stream-boundary/low-level async-boundary/restart-on/true-cancellation deferred |

## TODO before submission

1. ~~Re-run the Flutter twin post-memo~~ DONE 2026-07-23 (round 2 in
   flutter-twin/README.md). Residue: instrument/eyeball flutter's achieved
   presents/s (koka measured ~85/s) before quoting per-frame numbers; note
   the memo boundaries were a wash on this small demo — gap closed by the
   caching/frame-clock work; memo's wins are memodemo (−25%) + full app
   (37→20%).
2. **Write the memo invariants semi-formally** (drafts section 5): what is
   guaranteed, why recorded-read discipline + subtree dirt + the constraint
   condition ensure it; state the closed-row rule.
3. **Close or scope task #44** (-O1 startup race) — cannot claim
   thread-safety with it open; its deterministic repro makes it tractable.
4. Task #41 (wasi-web evloop) — close or scope wasi-web out of the test
   tier claims.
5. Related-work reading pass: Adapton/incremental computation (Hammer et
   al.), demanded computation, Flutter architecture docs, Solid reactivity.
6. Decide the threading material's home: one section here vs a standalone
   "Perceus meets threads" paper (thread-safety + bchannel could stand alone).
