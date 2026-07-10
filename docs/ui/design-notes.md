# lib/ui design ledger

One entry per design decision: what was chosen, the alternatives, and what
evidence would make us revisit. The framework is an experiment in what works
for *Koka* — entries record the idiom being probed, not just the feature.

## 1. Widget identity: trie ids via a `keytree` effect (probe 1)

**Decision.** `?key : int` — the id of a node in an identity trie mirroring the
widget tree (`ui/keytrie`). `child-key`/`scope`/`idx` derive a child node
through the ambient `keytree` effect (one lookup/insert in the parent's
children); segments compare with a `unsafe-ptr-eq` fast path (string literals
are stuck statics, so a literal segment is the same pointer every frame).
State cells, hover/press, scroll metrics key by the int id. The handler
(`with-keytree`) is installed once by `app`, owns a zipper over the trie
between frames (FBIP zipper: focus + contexts, unbalanced moves fine), and
node ids survive zipper rebuilds — the id is the identity, node values are
transient.

**Replaces.** Per-frame key-string concatenation (`?key ++ "/" ++ name`) and an
O(n) string-compared cell list.

**Kept as strings (deliberately).** `keyed()` reconciliation ids and
`anchored()` overlay anchors: these are app-*named*, not tree-derived —
semantic names the app chooses and matches up itself. Scroll-region rects
bridge into the string anchor namespace as `id.show`.

**Idioms probed.** Effects as ambient tree cursors (one effect per tree kind —
same-effect handlers can't be selected at a call site, so a future semantics
tree gets its own effect definition); implicits carrying capability-ish values
(`?key`); ptr-equality exploiting the runtime's stuck-literal representation.

**Cost observed.** `keytree` appears in every stateful component and app view
signature (`<keytree,ioc,theme>`). Plain widgets stay clean via effect
subsumption, but the effect is *visible* in a way strings were not. If this
grows tiresome: (a) fold key derivation into `ioc`-style builtin effects, or
(b) a pure alternative — keys as segment lists, trie only inside the store —
trading back some per-frame allocation for silent signatures.

**Revisit if.** Signature noise dominates feedback; or a use case needs
detached identity (keys created outside a handler); or FBIP measurements (once
the compiler reuse fixes land) show the zipper path-replay (`walk-to`) hot —
the id→path assoc list is O(n) and replay is O(depth); both have obvious
upgrades (int-map, parent pointers) not worth building until measured.

**Checkpoints.** `6d03ac2a9` (trie+effect standalone), `560c802d9` (wired
through ident/state/widget/app + all samples).

### 1b. Revision: identity is an explicit required `key` (checkpoint 3)

Explored and REJECTED two implicit-first designs for component identity:
- `.?key : child` dot-implicits (call-site mint via resolution default): the
  wrapper param remains an implicit candidate in its own body, so nested
  components pass through instead of re-minting; fixing it needs a "consumed"
  resolver rule (a language change we did not want to force). The annotation
  side of this landed upstream anyway (koka-lang/koka#911: `.?name : tp`
  unpacks via the type annotation + a real error message).
- `?key`/`?kk-file-line` + body rebind (`val key = component()`): any component
  DECLARING `?kk-file-line` becomes a passthrough link -- the whole tree sees
  the root call site. Capture-at-call-site only works inside call-site-resolved
  helpers. This is also the deep reason the old `?child-key` name existed.

**Decision**: stateful components take a REQUIRED `key : key` (abstract, named
`key` so the body derives from it by innermost resolution); callers mint with
`here()` / `idx(i)` / `scope(name)`. Zero resolver changes; forgetting is a
type error; helpers capture the call site safely; leaf widgets keep implicit
`?key`. Cost: one explicit argument per stateful component instance -- the
Flutter-style explicitness, with implicits making the helper zero-argument.

**Revisit if**: the explicit argument proves noisy in big apps (then reopen
consumed-dot-implicits with the #911 groundwork), or `memo` needs a different
minting discipline.

**Checkpoints**: `dd2f0cbb5` (compiler groundwork), `409751686` (library).

### 1c. No ambient root key (checkpoint 4: `3209ffc69`)

The `ui/key` root default let any keyless `here()`/leaf silently resolve to the
ROOT -- two keyless call sites would collide at top level, defeating the
forcing. Removed: the runtime supplies the root only at the view boundary
(`view(m, ?key = root-key)`), and every view-layer function that builds
interactive/stateful content declares `?key : key`. Identity is now provided
by a parent at every level, or it does not compile.

## 2. Reporting idioms: how a stateful leaf tells the app something

Probe: text input built with contrasting idioms, side by side in
samples/ui/todos (checkpoints `d865041ae` focus, `b7af668cf` fields).

**Groundwork**: focus moved from a backend tree-order index to widget identity
in ui/state (focused-key, live interaction.focused). The index-threading
machinery (count-inputs / find-input / hit-walk counter) deleted outright --
identity keys made a whole class of bookkeeping evaporate, and focus now
survives reorders by construction.

**(a) Controlled push** (`text-input`): value in the app model, one msg per
keystroke through the typed channel. Elm-classic. Right when the app reacts
per keystroke (filtering, validation-as-you-type). Cost: model + update carry
every transient keystroke; Threaded mode ships each to the worker.

**(b) Uncontrolled pull** (`field` + `act-msg`): value in ui/state under the
widget identity; keystrokes re-render but never reach the model. The app hears
exactly what it asked for: `on-enter` maps commit to a msg, and `act-msg`
computes a msg FROM ui/state at click time (read the fields, build one
message, clear them) -- the form-submit primitive. New pieces: HitMsgIoc,
OnValueDo (web), value baking (native). Right for forms; keeps the model
semantic. Gotcha: act-msg's child must not be clickable (inner target wins).

**(c) Channel push**: a commit callback `string -> ioc ()` subsumes it
(`fn(s) ch.emit-io(s)`); not built as a separate node -- if wanted, `field`
gains `on-commit : maybe<string -> ioc ()>`, two lines in drain-text. Channels
earn their keep for CROSS-STRAND streams (subs, threads), not leaf-to-app
reporting where (a)/(b) are simpler.

**VERDICT (Tim)**: no tradeoff to force -- both are in. Push (`text-input`)
when the app consumes keystrokes; pull (`field` + `act-msg`) for forms. The
ioc/msg boundary gives the clean click ladder: `on-click`(pure msg) /
`act`(ioc thunk) / `act-msg`(ioc-computed msg).

## 3. Animation (increment 1): the blinking caret

The first animation, driven exactly the way the state channel was designed
for: a runtime strand (`caret-blink`, forked in both app modes) toggles a
ui/state phase every 530ms while something is focused -- each toggle is a
transition, so drain-state re-renders -- and idles at a write-free 200ms poll
otherwise (no writes = no re-renders when unfocused). Typing and focus changes
snap the phase solid (standard caret behavior). The painter simply reads
`caret-visible()`.

Notes: the blink timer does not RESTART on a keystroke (the next toggle can
land early after an edit) -- acceptable; revisit on the clock if it bothers.

**Increment 2 (landed): the demand-driven frame clock + `animate`.**
`request-frame()` is Flutter-style self-healing demand: a builder with an
unsettled animation requests ONE frame per build; the anim-driver strand waits
~16ms, advances the clock via a transition (re-render), and the re-render
either re-requests (still moving) or goes quiet (settled OR unmounted -- no
release bookkeeping, no leaked demand). `animate(target, duration, easing)`
is a use-state cell {from, to, start}: retargeting mid-flight continues from
the CURRENT interpolated position (no jump). Easings are plain
`float64 -> float64` (linear/ease-in/ease-out/ease-in-out). Demo: the site
live-progress bar glides to its value; caret fix: never measure the empty
string (the shim's empty paragraph misplaces the caret), hint text and caret
coexist when focused-and-empty.

This per-frame re-render path is the FBIP measurement target once the
compiler reuse fixes land.

## 4. Event-driven input: the loop sleeps in GLFW (checkpoint `60f9d5b3a`)

The native pump sampled input on a 16ms uv timer (up to 16ms latency, 60Hz
idle wakeups). Replaced with the libuv EMBED pattern, built as a *generic*
std/async extension (Plan-B "extend libuv" groundwork): a host toolkit whose
event wait must own the thread's sleep installs an external waiter + wake;
the loop alternates uv_run(NOWAIT) with the host's wait (uv_backend_timeout
keeps timers on time); a watcher thread turns uv readiness from other
threads into a host wake (glfwPostEmptyEvent); a single-shot uv_async parks
the pump strand until the waiter reports input. Input now wakes the loop and
the pump instantly; an idle app burns 0.0% CPU.

Related timing work in the same arc: the anim-driver blocks on a frame-
request channel (its flag-poll raced drain-state's re-arm and slept 100ms
mid-animation) and ticks by REAL elapsed time (render cost counts); button
paints animate interaction SCALARS over live theme colors -- "animate the
dimension that changed, not the composed result" -- so theme crossfades flow
through buttons with zero lag.

## 5. Probe 4: ephemeral state as an EFFECT (checkpoint `071584508`)

ui/state's module globals became the `uistate` effect (ui/reactive, a leaf
below ui/widget): SEMANTIC ops (get-cell/set-cell, get-hover/set-focus, ...)
with the store as handler-local vars installed once by ui/app. The ops are
the interface -- the representation (assoc lists today) can become maps
without touching a caller. Per-app-instance state falls out (multi-window
prerequisite); threaded mode's "ui-state never crosses threads" is now
structural; ui/state keeps the typed user API unchanged on top.

The forcing discovery: DOM callbacks have NO effect evidence (they fire
outside every handler's dynamic extent), so handler-based state cannot be
touched from a raw event listener. That pushed web input into the same
architecture native already had -- listeners capture DATA (`web-ev`) into a
channel, a pump strand under the handlers dispatches. An effect-shaped
constraint produced the better design.

Still global (deliberately): the two runtime-wiring channel refs
(transitions, frame requests). Follow-ups: alias `react = <keytree,uistate>`
for signature ergonomics if the three-effect rows grate; live-resize
re-render (Cocoa modal loop; needs render-thread or evidence-swap design).

## 6. Platform/render thread split -- live resize (checkpoint `368bf0a59`)

The Cocoa modal resize loop blocks whichever thread owns GLFW, so the fix for
render-during-resize is structural: MAIN owns only the platform (window +
glfwWaitEvents, parked for the app's lifetime), and the WHOLE app -- uv loop,
strands, layout, paint, present -- runs on a RENDER thread. The key mechanism:
GLFW callbacks keep firing INSIDE the modal loop, and every callback wakes the
render thread directly (event sink -> uv_async_send on the parked pump
signal), so resizing re-lays-out and presents live, mid-drag. Constraints
discovered/encoded: uv loops must exist before Cocoa init (render spawns
first, handshake-released after the window is up); GLFW getters are main-only
(metrics cached by callbacks); AppKit teardown asserts off-main (main shuts
down after the platform loop exits); the ring buffers gained a mutex. The
embed loop (entry 4) remains the no-threads fallback. This is also Plan A/B
groundwork: per-view render trees on a thread that isn't hostage to Cocoa.

## 7. Profile: where the animating frame actually goes (2026-07-17)

Measured, not assumed (`sample` on the threads demo animating at 60Hz, render
thread self-time, 30s). Attributed self-samples split into three near-equal
thirds plus a small paint tail:

| bucket                    | share |
|---------------------------|-------|
| async-strand plumbing     | ~31%  |
| alloc / free / refcount   | ~27%  |
| effect + continuation     | ~26%  |
| Impeller glyph paint       | ~7.5% |
| number/format (fps `.show`)| ~2%  |

**What this refutes.** (1) Text *shaping* is NOT a bottleneck -- the metrics
cache (entry, uistate ops) + the shim's shaped-paragraph cache already erased
it; the ~7.5% that remains is Impeller re-rasterizing glyph vertices/atlas at
PAINT time, which no measure-cache touches. (2) The ephemeral-state var lists
are NOT the allocation churn: cherry-picking koka-lang/koka#716 (unique-local
`update`, in-place var mutation) + making `assoc-put` FBIP-friendly was a WASH
here (A/B within run-to-run noise, ~1.4s CPU/10s both). The lists hold a
handful of entries; the churn is the whole `widget`/`ltree` tree being rebuilt
and dropped EVERY frame, plus the prompt/compose/cont machinery of running each
frame through the nested handlers (async, interleave, uistate, keytree).

(#716 did surface a real bug: its JS `update` extern was `(#2({...#1}))` --
spreads the ref and discards the result. Correct is
`((#1).value = #2((#1).value))`. Fixed locally; upstream should too.)

**Where the leverage is, in order.** (a) Memoization / subtree reuse -- skip
rebuilding+re-laying-out unchanged subtrees; cuts alloc-churn, effect-machinery
AND the layout that feeds them at once (this is the retained-tree advantage the
Flutter twin showed: ~3.5% vs our ~8-13%). (b) A lighter per-frame re-render
path for the anim clock that does not round-trip the full async interleave +
transition channel every 16ms. (c) Glyph-paint cost is Impeller's and small --
leave it. FBIP-in-the-var-store is not worth pursuing until the tree rebuild is
memoized (then the stores may matter relatively).

## 8. Probe 5 (in design): memoization = tracked ops + subtree-dirty keys

Decision artifact: samples/ui/aprime (runnable console model + research/).
The keystone experiment (research/4): a stored continuation FREEZES
`effect val` evidence -- resumed after a theme change it replays the OLD
theme, while a `fun` op over live handler state reads fresh. Consequences:
(a) continuations do not solve ambient invalidation; (b) all changeable
ambient state must live behind dynamic ops over the root store (uistate) --
`with val` is for constants; (c) given (b), TOP-DOWN re-running needs no
continuations and keeps arbitrary mid-tree user handlers correct, because
the dirty spine re-installs them on the way down. Dirtiness is SUBTREE
dirtiness over the key tree (in lib/ui: the keytrie): a memo misses when its
key or ANY DESCENDANT key is dirty -- the grandchild-reads-theme-through-
clean-parent case forces this (a self-only check starves the grandchild).
Reads auto-track to the innermost memo identity; a cell write dirties
exactly its readers; cost per change is O(dirty spines). The CLOSED-ROW
rule types the escape hatch: a builder may be stored/re-run outside the
view pass only if its effect row is closed over framework effects (all
dynamic ops) -- animation-leaf splicing is the disciplined special case.
Awaiting hard-commit before the lib/ui integration.

## 9. Probe 5 landed: a-prime memoization (checkpoint `f33bce048`)

`memo(build, ?key)` boundaries with AUTO-tracked dependencies: uistate read
ops record (channel -> innermost boundary) edges, writes collect readers as
pending-dirty, the renderer flushes them into keytrie SUBTREE-dirty bits
(ascend propagates child dirt as part of normal zipper motion), and a hit
returns the cached widget pointer so reconcile reuses the laid-out subtree
via ptr-eq. Dirty storms (>64 readers, model messages, first frame) fall
back to plain full rebuild at the measured 2-4% floor -- so closure-captured
model state can never go stale. Builder rows are OPEN (theme et al fine:
build runs top-down in the view pass; only the RESULT is cached) -- the
closed-row rule is only for future out-of-pass capture.

Validated on samples/ui/memodemo: the 150-row boundary rebuilds 2x in 240
animated frames; animating CPU -25% relative. The bigger find: the demo
thrashed the 256-slot shaped-paragraph cache (300 strings, collision=
replace) -- HarfBuzz/ICU reshaping dominated the profile until the cache
grew to 4096, halving CPU in BOTH variants. Post-memo the frontier is
PAINT (full display-list re-record per frame): repaint boundaries -- the
Lmemo could cache its recorded display list exactly as it caches layout --
are the next probe. Known gap: map-msg over Memo rebuilds (correct, but
defeats ptr-eq); component embedding needs its own stability story.

## 10. Retention landed: keep-alive as a property of the key

The aprime keep-alive spec is now code (ui/keytrie + ui/state + ui/ident).
`keep` is declared where the identity is minted -- `scope("settings-tab",
keep = KeepAlive)` (also on `here`/`idx`); policy is fixed at first mint.
The knode grows `stale` (children of an OPEN rebuild not yet re-claimed) and
`retained` (kept-alive unmounted subtrees, cold: no widget references them,
reconcile and paint never see them). Unmount detection is by CONSUMPTION,
exactly as spec'd: `memo-run` brackets its build with `kt-open` (children ->
stale) and `kt-close` (whatever is still stale was not rebuilt = unmounted:
KeepAlive children move to `retained`, newest-first so a re-retention
shadows an older same-segment entry; Transient children prune and kt-close
returns every id in their subtrees). The renderer hands the pruned ids to
the new uistate `drop-ids`: cells, fields, scrolls, memo cache, and
dependency edges in BOTH directions (as reader via redges, as source via the
id-space channels) die with the identity. A later claiming descend that
finds its segment in `retained` is a REMOUNT: the whole subtree promotes
back with cells, memo cache, and dirt intact.

Decisions that needed care beyond the spec:
- The zipper context records which of the parent's three lists the focus
  rejoins on ascend (`kplace`): a CLAIMING descend (kt-child-id, i.e.
  identity minting during a build) always rejoins `children`; the
  re-rooting walks (mark-dirty et al) descend non-claiming and restore the
  child wherever it was found -- admin traffic never counts as a mount.
- Dirty propagation on ascend applies only to LIVE children. A retained
  subtree keeps its own dirty bit (it travels with the remount) but must
  not taint ancestors: an unmounted-but-dirty subtree would otherwise pin
  its old boundary into rebuilding every frame forever.
- Non-memo apps are untouched: nothing opens, `stale` stays empty, descend
  scans live children first exactly as before.

Costs/parked: a retained subtree with a live clock/channel subscription
still gets walked-to on every write (perf nit, not correctness); an older
same-segment retained entry shadowed by a newer one leaks until the pruning
knob (epoch LRU on the handler) exists; `kt-open`/`kt-close` at the ROOT
(so non-memo apps also unmount-detect) is deliberately not wired -- the
boundary is the unit of retention, per the spec.

Validated by test/ui/retain.kk (headless): three tabs behind one memo
boundary, KeepAlive counters survive unmount/remount cycles (A=2 across
three round-trips, two simultaneous retained panes), the Transient tab
resets every time. 9/9, and the pre-existing basic suite is unchanged.

## 11. OwnWindow landed: native multi-window (real OS windows + floating panels)

Windows stay "just the top z-band" of the view model: `window(key, content,
title, w, h, on-dismiss)` emits a Window-band view with `chrome = Titled`;
`overlay(..., chrome = Panel, target = Region(k))` is a borderless floating
non-activating panel that escapes the main window and follows its anchor.
Lifecycle is fully declarative -- emitted = open, not emitted = destroyed;
the native close button fires the view's `on-dismiss` (ignored when
Nothing); state follows the key-retention rules (§10), nothing
window-specific is retained. `view.anchor` became `maybe<anchoring>`:
InLayer defaults `Just(Anchoring())`, Titled requires `Nothing` (throws --
the reserved seam), Panel requires `Just`. InLayer views are size-capped at
the window and edge-pinned (clamp1 lo>hi guard + test).

Mechanics: `with-scene` returns `scene-out` (main composite + native-chrome
views; web backends flatten -- zero web change). The impeller host grew a
uniform window table (`imp_win g_wins[16]`, main = slot 0, caller ids
clamped, fail-safe lifecycle ops) with win-tagged event rings, and a
mutex-guarded render->main COMMAND RING (create/destroy/retitle/repos +
glfwPostEmptyEvent wake; drained after glfwWaitEvents and in the embed
poll) since Cocoa window ops are main-thread-only. One shared
ImpellerContext, per-window CAMetalLayer (imp_attach_layer shared with
init). The backend diffs emitted window views against `win-mount` records
per frame: open (async; request-render on success so idle apps paint the
new window), reconcile each window's OWN ltree at its size (take/swap FBIP
discipline per window), per-window repaint dl-caches, present per window;
chrome change on a stable key = close+reopen; dismiss is a rising-edge
latch (sticky close_requested would refire). Input routes by the event's
win tag (unknown tags drop -- close race); hover repaints the cursor's
window. Panel placement = main-window-origin() + place(...), repositioned
on change. Live tier: window trees ride the registered scene at synthetic
x-offsets (win-slot-w = 100000) so the unchanged tester API decodes
window + local coords; keyboard routes by last-clicked window VKEY
(slot-reuse-proof); `./test-live windows` is a second invocation
(different app type; live-scenarios hard-exits).

Parked: titled-window anchoring (throws); no synthetic close in the live
tier (GLFW limitation -- dismiss tested headless); text-into-window live
coverage needs a field in the windows test app; secondary-window resize
re-flows only on the next render cause; single focus/hover stores +
no cross-window drag (by design, spec §5/§7); IMP_MAX_WINDOWS=16;
128-byte title truncation; portals-inside-memo vanish on hit (pre-existing,
task #45 -- found by the Task 3 test). Validated: test/ui/windows.kk 13/13
headless, `./test-live windows` 7/7 live, samples/ui/windows demo
(inspector tear-off + tooltip panel), full suite green.

`window(key, content, title, w, h, on-dismiss)` (ui/view) and
`overlay(..., chrome = Panel, target = Region(...))` are the same `view<a>`
concept as an in-window overlay, differing only in `chrome`: `InLayer`
(default, composites into the main tree, unchanged), `Titled` (a real,
resizable OS window; `Nothing` anchoring only -- OS-placed), `Panel` (a
borderless, non-activating floating window that must have an anchoring and
follows its target). Declarative lifecycle: emitting the view each build is
"open", not emitting it is "close" (mirrors `window()`'s own doc comment);
the native close button dispatches the app's `on-dismiss` message the same
way a scrim click does for an in-window modal -- no separate close API.

Landed across the OwnWindow tasks:
- **Scene split** (`ui/view`): `with-scene` now returns `Scene-out(main,
  windows)`, partitioning emitted views by `chrome.is-in-layer`; `windows`
  keeps band order (band only matters for InLayer stacking, restored by
  `compose` on the web/wasi flatten path). `scene-out/flatten` degrades
  `windows` back to InLayer for backends with no real window concept
  (web/wasi): same app code, no branching in user apps.
- **Host layer** (`ui/api/impeller`): a window table keyed by the view's
  key (a native `id0`/handle plus the Koka-side FBIP tree and repaint
  cache live per-row), a command ring the render thread drains to issue
  `open-window`/`close-window`/`set-window-pos`/`window-alive` calls on the
  platform thread, and `window-close-requested` surfaced back for the
  declarative-dismiss dispatch. `Panel` is a borderless, non-activating
  Cocoa child-adjacent window that repositions every time
  `main-window-origin` moves (the "follows the main window" behavior).
- **Multi-window backend**: each open window gets its OWN FBIP ltree and
  its OWN repaint/display-list cache -- reconcile, layout and paint are
  per-window, not shared with the main scene. Input (pointer, key, scroll)
  routes by which native window last received host events; there is a
  single focus/hover store and no cross-window drag by design (drag state
  is anchored to one ltree).
- **Anchoring rules, enforced at scene-compose time** (`check-chrome`):
  `Titled` chrome with `Just` anchoring throws (`"titled-window anchoring
  is not supported yet"`) -- OS window placement is not yet wired to the
  anchor geometry, so a `window()` call must pass no anchoring; `Panel`
  with `Nothing` anchoring throws (a floating panel is meaningless
  unanchored). `InLayer` accepts either.
- **Live-tier coverage** (`test/ui/live`, `test/ui/windows.kk`): the
  windows live scenario runs a SEPARATE binary invocation
  (`./test-live windows`, native/impeller-only -- a deliberate no-op on
  jsweb) because the windows app and the basic app are different `msg`
  types and `live-scenarios` is monomorphic per call. Host events are
  routed to whichever real window (main or secondary) a target name
  resolves to, via an offset-tree lookup over the per-window trees. Window
  creation is a real async OS call on this tier (unlike headless, where
  `window()` mounts synchronously) -- the scenario budgets an extra
  `settle()` round after each open/close toggle for create -> reconcile ->
  present to land.
- **Sample**: `samples/ui/windows` -- a torn-off inspector window sharing
  the main window's model/msg (bump from either window), a `Panel` tooltip
  anchored to a keyed region that visibly escapes the main window's bounds
  and follows it when dragged.

Parked / known gaps (not blocking, tracked for follow-up):
- Titled-window anchoring throws rather than positioning the OS window
  relative to a region -- OS window placement from anchor geometry is
  unimplemented.
- No synthetic "close" injection exists in the live tier: the windows
  scenario closes via the app's own dismiss button, not a simulated OS
  close-box event.
- Real text-into-window live coverage is missing a field widget in
  `windows.kk`'s model to type into -- the scenario only proves the routed
  key doesn't crash or misroute, using Escape (which the app ignores).
- A secondary window's resize is only re-flowed on the NEXT render pass,
  not synchronously with the OS resize event.
- Single focus/hover stores mean no cross-window drag (by design, not a
  bug -- drag state lives in one ltree).
- `IMP_MAX_WINDOWS=16` is a fixed cap in the impeller backend (no dynamic
  growth).
- Window titles are truncated at 128 bytes on the native side.

## 12. Web scroll takeover: one scroll model everywhere

Web scrolling is koka-owned (no escape hatch -- reverting is a git
operation, per Tim): the overflow:auto lowering is GONE. LScroll lowers to
an overflow:hidden clip + inner content box shifted by translate3d along
the axis, using the same BAKED offset native paints with; `bake-scroll`,
`apply-wheel` (region-under-point, horizontal dx-with-dy-fallback, clamp,
write), and `sync-scroll-metrics` hoisted into ui/state as the single
home -- the backends cannot drift. A root wheel listener (non-passive,
preventDefault, deltaMode-normalized: line x16, page x innerHeight --
innerWidth for dx) posts EvWheel into the web pump, which runs the shared
apply path; browser momentum-phase wheel events ride the same listener, so
trackpad inertia is free on macOS. Metrics + scroll-region rects publish on
web, so the composer's AUTO scrollbar views (and manual/themed bars) now
render on web with zero composer change; the browser bar is gone. Sign
convention verified end-to-end both directions (the browser's deltaY is
negated into the GLFW-derived convention; the synthetic-injection double
negation cancels by construction). test-inject-scroll dispatches a real
WheelEvent. The scroll scenario runs on EVERY tier (web live = 7 checks,
expectation pinned in the suite).

The un-gating exposed a LATENT bug (present since overlays): a composited
scene layer lowers on web to a viewport-sized DIV that swallows
elementFromPoint and native focus for everything under it -- the moment
auto-scrollbars appeared on web, the layer covered the app and inputs
could never focus (deterministic typing/keys failures the suite caught;
initially misread as flake #46). Fix: Positioned layers carry a reserved
LKeyed("kk:layer") marker; the web lowering wraps them display:contents +
pointer-events:none and the DOM-native leaves (input, a, .ui-i) opt back
in via the injected CSS; each-anchor skips the reserved name (no
anchor-sig churn). Native walks unaffected. Debugging path worth
remembering: the live page mirrors console into <pre id="log">, and
instrumenting the BUILT bundle in out-js (no rebuild) localizes DOM-fringe
failures in minutes.

Scope/parked: wheel-first (desktop-complete); touch/fling physics for
mobile web, keyboard paging, rubber-band are follow-ups; find-in-page /
fragment scrolling into clipped content degrade (a11y design to pick up);
scroll-feel + no-compositor jank needs an eyeball pass on a long list
(the tick is one transform write by construction).

## 13. Builder lists landed: `lazy-column`, virtualized scrolling over the unified scroll model

`ui/lazy`'s `lazy-column` is the Flutter `ListView.builder` equivalent:
`item(i, key)` builds row `i` on demand, so a 100k- or infinite-row list
never builds more than the visible window. Window arithmetic: `vis =
ceil(viewport/item-extent) + 1` (one row of margin beyond the design doc's
literal `ceil(viewport/extent)`, harmless -- still bounded, still
count-independent), `first = max(0, floor(offset/extent) - cache)`, `n =
vis + 2*cache` clamped to `count` when bounded. A lead spacer of
`first*extent` and a trail spacer of `(total-first-n)*extent` stand in for
everything not materialized -- one `column([lead] ++ items ++ [trail])`
inside the SAME `scroll` region the windowing reads its offset from (the
wiring subtlety: windowing and `scroll` must resolve to the identical
region key -- see lazy.kk's header comment and the `?kk-file-line`
threading it requires). Zero new ltree node types: the only new widget is
`fixed(child, width, height)` (pins REPORTED extent regardless of what the
child measures), forced out of the design by the T1 review, not part of
the original plan. Infinite lists (`count = Nothing`) stay one page ahead
of the offset -- `total = first + n + vis` -- so the scrollbar thumb keeps
shrinking as you scroll, no `count` ever supplied.

Scrolled-out rows unmount through the SAME consumption-boundary machinery
§10 built for tabs: `kt-open`/`kt-close` bracket the item build, unclaimed
`idx(i)` identities are the unmounted set, `drop-ids` reaps their cells.
This is the retention system's THIRD client (tabs, windows/panels, now
lists) -- no new machinery, just another `kt-open`/`kt-close` boundary.
`keep` is UNIFORM PER LIST, stamped at first mint into every `idx(i)`
(a keytrie invariant: unmount policy is fixed where an identity is
created); it is not yet per-item. Nesting a `KeepAlive` scope inside a
`Transient` row does not survive scroll-out either -- pruning is
subtree-rooted at `idx(i)` itself, so the row's OWN policy decides
regardless of what a descendant declares. Designed, not built: `keep-of :
int -> keep` plus dynamic "last claim wins" retention, the Flutter
`updateKeepAlive` analog.

Two bugs this work surfaced and fixed, both geometry, neither identity:
- **Oversize-row geometry desync.** Before `fixed`, a row measuring taller
  than `item-extent` shifted every LATER row's position, because the lead/
  trail spacer math is computed from `item-extent` ALONE and assumed every
  row actually measured it. `fixed` makes the assumption true by
  construction: a tall/short child now overflows/underflows visually at
  its OWN row (no clip), corrupting nothing downstream. See the `oversize`
  scenario, test/ui/lazy-oversize.kk.
- **#50: a 4th concurrent lazy-column loses clicks on narrow panes.**
  Root-caused as click-loss by GEOMETRY, not identity (the reporter's
  keytrie-reroot suspicion was wrong; cell identity traced rock stable
  frame to frame). `each-anchor` reported a partly-overflowing row's
  button at its full UNCLIPPED rect while `hit`'s `LScroll` arm already
  clipped clicks to the viewport -- `find` said "here", `hit` said
  "nowhere near here" at the click's own coordinates, and the `use-state`
  write never fired. Fixed by threading a running clip rect through
  `each-anchor` (parity with `hit`'s existing clip, intersected at every
  `LScroll`, empty rects skipped) -- which in turn exposed that the
  headless test harness never called `bake-scroll` before hit-testing/
  anchoring the way the real backends do, so scrolled rows were addressed
  at their un-shifted absolute y. Both fixed; `narrow-click-scenario` (task
  #50) and the `moved`/`recycle` scenarios' now-viewport-relative present
  sets pin it. Full trail: task-50-report.md.

Measurement: the materialized window is INDEPENDENT of `count` -- the same
`n0 < 150` bound holds whether `count = Just(10000)` or `Nothing`, per
window-scenario in test/ui/lazy.kk (`window count is bounded (not the
whole 10k list)`). 24/24 in test/ui/lazy.kk, all tiers; samples/ui/lazy is
the eyeball (two 100k-row panes, KeepAlive vs Transient side by side, plus
a third infinite pane).

## 14. Owner identity everywhere + selector addressing (one identity system)

Every widget and ltree node carries `owner : int32` — the keytrie identity
in scope when it was built. Smart constructors (`text`/`box`/`column`/…)
gained implicit `?key : key` and stamp `?key.key-id`; id-minting
constructors (interactive/field/input/scroll/memo) stamp their own minted
id; `layout` copies widget owner → ltree owner. This FINISHES probe 1c: any
function that builds widgets declares `?key` or does not compile, so
identity is pervasive by construction rather than opt-in.

**Why STORED not derived (the decision that shaped it).** A cheaper design
derives a node's identity by walking to its nearest id-bearing ancestor at
query time. It is UNSOUND: addressing runs over the laid-out ltree, in the
backend/tester, with NO keytree handler (the trie maps id→path, not
ltree-node→id), and a stateless mint point (a plain `column` under
`idx(i)`) leaves no id-bearing ltree node to walk to. The ambient identity
is known only at widget-build time, under keytree, before layout — so it
must be captured there and flowed onto the ltree. Content-addressed ids
(`Named`/`Index`) keep their value across renders regardless of siblings
(the #50 property), so `owner` is stable. Cost: 4 bytes/node (int32, the
web-keytrie width); the bench fingerprint INCLUDES owner and reconcile
`check: ok` over 30 changing frames is positive proof owners never go stale
on FBIP reuse.

**Selector addressing.** `kt-find(selector)` (new keytree op) resolves a
path selector against the id→path table by EXACT-TAIL-MATCH: the rightmost
step is the target, earlier steps disambiguate as ancestors, gaps allowed
(`"todos row:3 bump"`, `"pane-a val"`, `"lines :5"`). The tester's
`find`/`click`/`texts` resolve `find-ids` → error on ambiguity (listing the
candidate paths) → `owner-rect`/`owner-texts` over the current scene ltree.
`owner-rect` clips to enclosing scroll viewports exactly as `hit` does (the
#50 discipline), so a scrolled-out target is Not-Found and a click never
misses. Anchoring: `target = Display | Scope(sel)` (Region removed),
resolved via the same path; `with-scene` split into `with-scene` +
`raw-scene/finish` (finish resolves Scope under keytree — forced by a
closed-keytree-vs-row-poly effect-inference wall). The native resettle
trigger signs the resolved Scope-rects of emitted views, so a
bare-`?key=scope(...)` anchor self-heals the same way the old string
registry did; auto-scrollbars emit only once their region rect resolves
(no first-frame corner-pin).

**Removed (pre-publication policy, no shims):** `keyed`, `anchored`,
`Keyed`/`LKeyed`, `Region`, the entire string anchor registry
(`publish-anchor-rect`/`all-anchor-rects`/`each-anchor`). The web
pointer-transparent scene-layer marker became a dedicated `LLayer` ctor
(LFlex in every walk + the display:contents/pointer-events:none style).
One identity system remains — no dual-tagging: a leaf is named by minting
(`?key = scope("count")`), a component by the key it already receives, a
row by its `idx(i)`. Migration was compiler-guided (missing-implicit and
exhaustive-match errors as the checklist); all tests + samples moved.

Parked (task #51): `?key = scope(name)` does not name an id-BEARING widget
(interactive/field/input/slider consume `?key` to mint their own child id),
so those need a thin wrapper to be selector-addressable — a usability trap
to resolve before the paper calls the API clean. This foundation is also
what a semantics/a11y tree, FLIP animation, and a devtools inspector would
consume (owner→geometry by identity) — not built, but now possible.

## 15. transform3d + images landed: 4x4 projected-2D, accurate hit, native decode

**transform3d.** `mat4` (`ui/transform`) is a plain row-major 4x4
(`m[r*4+c]`) with `identity`/`perspective(depth)`/`rotate-x/y/z`/
`translate3`/`scale3`/`(*)` (column-vector convention: `a*b` applies `b`
THEN `a`) — pure math, no widget/backend dependency. `transform3d(child,
m, ?key)` concats it onto the paint walk about the child's own center
(layout unchanged, paint-only), same shape as the existing `rotate`. Hit
lands ACCURATE, not approximate, in the SAME cut: `unproject` extracts the
z=0-plane 3x3 homography from `m` (rows/cols `{0,1,3}` — a z=0 point's
column-2 contribution is always zero), inverts it, and maps a screen click
back to the child's local `(x,y)`; `hit`'s `LTransform3d` arm is one
`unproject` call added to the existing walk, not a second walk.

**Idiom (a gotcha the gallery hit).** Interactive content must live INSIDE
`transform3d`, not in a clickable box AROUND it: transform3d is paint+hit-
only (layout unchanged), so an outer `box(transform3d(...), on-click)` hit-
tests the box's flat, UNTRANSFORMED footprint — and mid-turn a click on that
footprint's now-exposed background (where the rotated child no longer covers)
fires it. `transform3d(box(child, on-click), m)` gates the click through the
accurate unproject instead. (This is correct box semantics — a box owns its
full rect — not a transform3d bug; `test/ui/transform-hit.kk` already pins
that an off-quad-but-in-footprint click misses.)

**The transpose finding.** Both consumers want column-major: native's
`kk_imp_transform` (shim.c) and web's `css3d` (backend.kk) each transpose
`mat4.m` on the way out (`output[c*4+r] = m[r*4+c]`), independently but
identically-derived from their SDK headers. Task 6's gallery sample is the
pixel check: a flip-card (`transform3d(face, perspective(800.0) *
rotate-y(angle))`, `angle` eased 0↔pi on click) turning about its vertical
axis. **Outcome: the transpose is correct as landed, no fix needed** —
verified by hand, not just eyeball: driving the web build's DOM and
reading back the live `matrix3d(...)` string at `angle = pi` reproduces
the row-major `perspective() * rotate-y(pi)` product element-for-element
(down to the same `1.2246e-16`/`1.53e-19` float noise from `cos(pi)`'s
rounding), confirming `css3d`'s transpose reconstructs the intended
matrix in CSS's column-major reading — and native's transpose is the same
formula over the same row-major input, so it carries by construction. (A
real annotated screenshot of the native window was not obtainable in this
sandbox — no screen-capture permission — so native is a build+run smoke,
not a second independent pixel read; see Concerns.)

**Images.** `image(src, fit, width, height, ?key)` (`ui/image`'s
`image-fit = Contain | Cover | Fill | ImgNone`, re-exported through
`ui/widget`) lays out BEFORE pixels decode (width falls back to the
incoming constraint, height to a fixed default) so a slow/broken load
never blocks or reflows. Native (shim.c, vendored `stb_image.h`,
PNG+JPEG only) decodes+uploads a GPU texture, ONE per image OWNER,
identity-cached in a module-global `int32-map<img-state>` alongside the
scene trees — the same retention idiom §10 built for tabs/windows/lists:
`prune-images` walks live owners each frame and calls `texture-release`
on the ones that dropped out, so an unmounted image frees its GPU memory
without a second, image-specific unmount hook. Web lowers to a real
`<img>` (`object-fit` from `fit`, absolute-positioned like every other
leaf). **Caveat, load-bearing for the sample:** native decode is a LOCAL
PATH read (`stbi_load` on the string as a filesystem path) with NO URL
fetch — a `https://` src is a guaranteed decode failure there, painting
the neutral placeholder box, while the same src is a real picture on web
(the browser fetches it). samples/ui/gallery's URL row exists to make
that split visible, not to demonstrate loading it natively. **Caveat,
load-bearing for perf:** decode+upload is SYNCHRONOUS on first paint of
each distinct owner (a one-time per-image hitch on the render thread) —
task #53 tracks the worker-thread-decode/render-thread-upload split that
was judged too invasive for this cut (would need `async` threaded through
the whole recursive paint walk).

**Tier-1 boundary.** Both features are native+web only — `transform3d`
and `image` have no wasi/wasi-web story (Impeller-only 3x4 concat, a real
`<img>`/texture path); the headless/test-only tier stays untouched (no
`LTransform3d`/`LImage` arm needed there beyond structural walks like
`image-owners`). Task #52 (flutter_scene / cross-backend 3D beyond
projected-2D paint) and #53 (async image load) are the two open threads
this cut deliberately left for later.

samples/ui/gallery is the eyeball: a flip-card exercising accurate
transform3d hit-testing end to end (click anywhere on the turning card,
not just its flat footprint), a `fit` comparison row (Cover vs Contain
over the same source), and the web-only URL caveat made visible in the
UI text itself, not just a comment. Native smoke (`KOKA_IMP_FRAMES=90 ./app-native`, exit 0) is wired into
util/test-wasi.sh's sample loop; the `index.html` carries a `?drive`
self-check (matrix present, flip lands on "Back", `<img>` count) in the
same style as `samples/ui/threads`', but — unlike threads' — it is not
yet wired into the automated suite, only run manually for this ledger
entry (headless Chrome, DOM dump). Wiring it in is a small follow-up, not
done here to keep this task's suite delta to the native smoke line. One
more gap surfaced doing this: `web-ui/project.kk`'s `build-jsweb` stages
only the compiled module graph + `index.html`, no local-asset directory —
`samples/ui/gallery/assets/` had to be copied into `out-js/assets/` by
hand to see the local images on web at all. Not fixed here (out of this
task's file list); a real asset-staging step in `build-web-app` is a
follow-up, not a `ui/image` bug.

## 16. Async boundaries landed: `future-boundary`, `image` as its first customer

**The primitive.** `ui/async`'s `async-snapshot<a> = Pending | Done(a) |
Failed(exn)` is the shared contract with the (deferred) streaming
`stream-boundary`/`Active(latest)` variant — a future is exactly `Pending
-> Done|Failed`, never `Active`, so `future-boundary` (the 80% path
shipped now) carries no delivery channel or coalescing the stream
mechanism would need. **Shared CONTRACT, specialized MECHANISM** is the
rationale: future = fork-await-store-exit; stream = fork-drain-coalesce —
forcing future through the stream's shape would flash a spurious
`Active(v)` before `Done(v)` and pay for machinery it never uses. Per-key
phase (an `Async-entry(generation, raw-phase)`) lives in `ui/state`
alongside `use-state`'s cells, read at build time; the `Done`/`Failed`
payload is stored ERASED via the same `erase`/`unerase` existential
coercion `use-state` already uses. `future-boundary(run, ready,
placeholder, failed, min-load, ?key)` runs `run` ONCE per
identity+generation: a KICK writes `RPending` **synchronously** (not
through `ui/state`'s deferred transition channel — a rebuild racing the
deferred write would read `Nothing` again and double-kick) and emits ONE
`async-want` to a module-installed channel; a forked `async-pump` strand
(the app's twin of `drain-state`, idle until a boundary kicks) receives
each want, forks the `run` under `try`, holds `min-load` past a fast
resolve, and writes `RDone`/`RFailed` back through `ui/state`'s channel —
gated on the generation the want ran under still being current
(**stale-discard**). One mechanism — the generation — IS simultaneously
retry (`retry()` bumps it), deps (a future `restart-on` would bump it
too), and the cancellation FLOOR (a stale write is dropped even though
the strand that produced it isn't actually killed; true forking-
cancellation is a deferred optimization on top, not required for
correctness). `default-error` ships a message + a `Retry` button (`act`
running the `retry` thunk); `default-placeholder` is a neutral empty box.
A boundary's phase reads register with `ui/reactive` exactly like any
other tracked read, so a `future-boundary` embedded under a memoized
subtree participates in dependency tracking for free — the memo
invalidates on the phase's own write, not on a blanket "always re-render
this subtree" fallback; no boundary-specific memo code was needed. One
loose end this surfaced: `ui/state`'s several keyed stores (`use-state`,
scroll, now async-phase) are hand-duplicated near-identical machinery —
task #54 (a generic tracked store) would fold them into one.

**`image` as the first customer.** `image(source, fit, load, placeholder,
min-load, width, height, ?key)` replaces §15's synchronous-on-first-paint
native decode with a `future-boundary` over an `image-source` union
(`FromPath`/`FromBytes`/`FromPixels`) and an `image-load` switch
(`Async` default, `Sync` = §15's old inline-decode path verbatim, no
placeholder/min-load, kept for a caller that wants frame-1 pixels and
accepts the hitch). Native `Async`: `run` decodes OFF the render thread
via `compute` (`stbi_load`/`stbi_load_from_memory`; `FromPixels` skips
decode, it's already RGBA) — the frame clock keeps ticking during the
decode, which was the entire point of task #53 — then, back on the render
thread, uploads a GPU texture and caches it under the image's OWNER id
(the same `int32-map` retention idiom §10/§15 built for tabs/windows/
lists/textures); `ready` emits an `Image` leaf marked
`async-image-src` so the backend's paint hits the cache instead of
re-decoding. `min-load` is held INSIDE `run`, between decode and upload —
not via `future-boundary`'s own `min-load` param, which would hold
AFTER the texture already exists (unmounted-but-alive for the whole
window); holding first means no texture exists during the placeholder
phase, and upload -> cache -> ready-leaf-scheduled happens in one
synchronous step once decode returns (the one-sweep pin grace from
§15/#53 covers the residual gap). **UPDATE (final-review, Important 2
fixed):** that "never leaks a never-mounted texture" claim used to hold
only while renders kept coming — a late `run` that finishes AFTER its
boundary unmounted still calls `put-image-texture` (pins fresh), but
`settle-if-current` then finds no live phase entry and drops the write;
the dropped branch used to do nothing, so nothing asked for the render
`prune-images` needs, and in an otherwise-idle app the pin sat forever.
Fixed with two one-liners that make the invariant hold UNCONDITIONALLY:
`settle-if-current`'s drop branch now calls `request-render()` (so a
completed-but-dropped decode always schedules at least one sweep), and
`prune-images` itself now calls `request-render()` whenever it ages a
`PinFresh` pin to `PinAged` (so, once a grace period starts, it always
runs itself to completion — Fresh -> Aged -> released — with no
dependency on any OTHER render arriving from outside). `test/ui/live`'s
`async-idle-leak-scenario` pins this: the same "scrolled past during
decode" shape as `async-leak-scenario`, but with NO forced frame anywhere
in the scenario — it fails against the pre-fix code (the pin stays
elevated past baseline forever) and passes against the fix.

Async `image` re-decoding on a SOURCE CHANGE at a stable `?key` (Important
1, final-review): `future-boundary` alone has no source-dependency (its
phase is keyed on identity+generation only), and the `ready` leaf above
always draws the CONSTANT `async-image-src` marker — so, unfixed, an
async image whose `source` prop changes while `?key` stays fixed was a
silent no-op (shows the first picture forever; this is the async twin of
the sync-path stale-src bug a prior review already fixed for `image-for`,
reintroduced here on the async DEFAULT). Fixed with a minimal, targeted
`restart-on = source`: `async-image` computes a cheap comparable
`source-key` per source (`FromPath`'s path string; `FromBytes`'s byte
length; `FromPixels`'s `(w,h,length)`), remembers the key it last kicked
with in a `use-state-quiet` cell (quiet so the every-build comparison
itself never schedules a redundant re-render), and — only once the PRIOR
run has settled to `RDone`/`RFailed` (never while `RPending`, so an
in-flight decode is never interrupted) — bumps the generation and emits a
fresh want itself when the key has actually changed, exactly
`future-boundary`'s own `retry-fn` shape, just triggered by a source-key
mismatch instead of a click. `test/ui/live`'s `async-image-scenario` now
also swaps the ASYNC row's `FromPath` source at its stable `?key`
mid-scenario and asserts a real re-kick (the leaf drops back to
placeholder, then reaches ready at the new source, net texture count
unchanged — old released, new created). **This also corrects an
over-claim in the design doc's original caveat**, which scoped "changing
content at a stable `?key` requires a key change or `retry()`" to
`FromPixels` only: with this fix, async `FromPath`/`FromBytes` re-decode
automatically on a source change — no key change or explicit `retry()`
needed. What survives is a narrower same-length blind spot shared by
`FromPixels` and `FromBytes` (both fingerprint by buffer length, not a
content hash): two distinct buffers of the identical length won't be
told apart, so a swap between them at a stable `?key` still needs a key
change or `retry()`. `FromPath` (fingerprinted by its path string) has
no such gap. A real content hash is deferred.

Web `Async` does NOT reuse
`future-boundary`/`async-pump` — it is hand-rolled (`web-async-image`)
with the identical phase shape (`Async-entry`/`RPending`/`RDone`/
`RFailed`, `set-async`/`async-phase`, generation-bump retry) but a
different kick: a `probe` primitive installed by the web backend runs
SYNCHRONOUSLY from the build (no `async`, no channel), resolves the
source to a final src (the path as-is / a base64 data-url for `FromBytes`
/ a `<canvas>` + `putImageData` data-url for `FromPixels`), and wires
`onload`/`error` listeners that `post` an event through the web backend's
EXISTING `evch`/`pump-loop` — the same proven post-and-drain path every
other DOM event already uses. `pump-loop` (a single, always-running,
top-level strand) then flips the phase (holding `min-load` there is
safe, unlike inside a one-shot nested fork — see next paragraph); `ready`
draws a real `<img>` at the resolved src, which the browser paints from
its own cache immediately (the probe already loaded that exact src, no
second fetch). This split was NOT a style choice — see below.

**The finding: reentrant `fork` doesn't execute on jsweb (task #55).**
Building the gallery's general `future-boundary` demo (a plain `run` that
`wait`s then returns/throws, no image involved) surfaced a real,
previously-undiagnosed bug: on `--target=jsweb`, `async-pump`'s own `fork
fn() ... (w.run)() ...` — called REENTRANT from a strand that the SAME
top-level `forking` already forked, i.e. adding a new strand to an
already-running interleave from inside one of its own strands, not from
the `forking fn(fork) ...` body itself — never runs the forked closure's
body (not even its first statement) and eventually throws an uncaught
`TypeError` in `ui_async.mjs` (`Cannot read properties of undefined
(reading 'run')`) visible in the browser console. A minimal repro
(`std/async/interleave`'s `forking`, a plain channel, no `ui/async`
involved) reproduces it identically. Native's `async-pump` (the libuv
backend) is unaffected — `test/ui/live`'s `async-image-scenario` already
exercises the identical reentrant-fork shape and is green. This is
almost certainly WHY `web-async-image` was hand-rolled to bypass
`future-boundary`/`async-pump` rather than reuse it: the doc comment in
`ui/async.kk` blames DOM-listener resumption specifically ("a one-shot
continuation captured several fork levels deep... never got its turn
again"), but the true root cause is broader — reentrant `fork` itself is
broken on jsweb's `std/async/interleave`, independent of any DOM event.
Fix belongs in `std/async/interleave.kk` (task #55, not attempted here —
out of this task's scope and too deep to risk alongside a sample+ledger
task). **Consequence for the sample:** `samples/ui/gallery`'s two
`future-boundary` cards are gated `test-backend == "impeller"` (native-
only) — on jsweb they render one `body()` line explaining the gap instead
of crashing; the boundary primitive itself, `future-boundary`, `image`'s
Sync/native-Async paths, and the headless suite are all unaffected (none
of them hit reentrant `fork` the way this demo's bare `run` does — even
native `image`'s own `async-pump` fork isn't reentrant in the same sense,
it's the TOP-LEVEL `forking` body's direct fork, called once per want
from the strand `run-single`/`run-threaded` itself set up, never from
inside a previously-forked strand).

**A second, DISTINCT jsweb regression (task #56).** Independently, after
an unrelated concurrent commit (`page()`, in `ui/style/default/
components.kk`, now wraps its content in `scroll(...)` by default), the
gallery's plain async `image()` row (three `FromPath` images, no
`future-boundary` demo involved) stopped reliably settling all three
placeholders to real `<img>` tags on jsweb within a generous headless-
Chrome virtual-time budget (confirmed with the `future-boundary` cards
removed entirely, so it is not task #55 bleeding over) — before that
commit the same row settled cleanly. Not investigated further here (out
of this task's scope; jsweb gallery is a manual/eyeball check only, not
gated by `util/test-wasi.sh`'s automated suite — see below).

**Suite.** `future-boundary`'s headless coverage
(`test/ui/async-boundary.kk`) is in `util/test-wasi.sh`'s native `ui/test`
loop already (placeholder -> ready, a throwing run -> failed, fail-then-
succeed -> retry -> ready, `min-load` holding past a fast resolve, the
erased-value round-trip); `image`'s native-Async coverage lives in
`test/ui/live` (`async-image-scenario`, `async-leak-scenario`) and web's
in the same file's `async-image-web-scenario`. `samples/ui/gallery` is
unchanged in the automated suite (still the native
`KOKA_IMP_FRAMES=150 ./app-native` smoke, exit 0, in `util/test-wasi.sh`'s
sample loop) — its jsweb build/serve/headless-Chrome pass remains manual,
same as §15 left it; that manual pass is the one that surfaced both #55
and #56 above.

**Deferred (task #53's 20%, unchanged from the design doc):**
`stream-boundary`/`Active(latest)` + delivery-channel coalescing, the
low-level `async-boundary(run-with-yield, view, ?key)` builder (the
type/contract ships, its own yield-delivery mechanism does not),
`restart-on`/deps sugar, true forking-cancellation (killing the stale
strand, not just discarding its stale result), progress-union sugar,
blurhash/progressive image. Task #54 is closed by §17 below. Tasks #55 and
#56 are new, both jsweb-only, both surfaced by this task's gallery work
rather than by the primitive's own (native-clean) headless suite.

## 17. Dependency channels: derived, not hand-written (task #54)

The four keyed stores (cells / fields / scrolls / asyncs) share one integer
channel space tagged by slot. That space was hand-written as `id*4+k` and
was exactly FULL at four stores: a fifth would have aliased id+1's cell
channel — a boundary woken by a stranger's write, or worse, two stores'
edges indistinguishable. `keyed-chan(id, slot)` now derives its multiplier
from a `keyed-slots` list, so the space grows with the stores instead of
overflowing into the next id, and `drop-ids` walks the same list to tear
down edges (the two can no longer disagree).

The deeper point is that BOTH ways this breaks are silent. A getter that
forgets to `record` freezes a memoized subtree on stale state — that is
exactly the async-image-under-a-memo bug §16's async slot cost us — and a
setter that forgets to `invalidate` freezes it from the other side; neither
throws, and the app just quietly stops updating in one corner. So the
add-a-store checklist (slot, record, invalidate, drop) now lives at the one
place that defines the encoding, and `test/ui/state-channels.kk` pins the
invariant as a PROPERTY over the whole keyed cross-product (every store×id
read checked against every store×id write, 256 cases) rather than one case
per store — extend `stores` with a new slot and the matrix covers it
automatically. Failing-first verified against both hazards: a too-small
multiplier fails with `cell@8` aliased to `async@7`, and dropping `record`
from `get-async` fails all four "woken by its own write" cases.

Not done here, and deliberately: the stores are still four separate
`int32-map`s with four op pairs, not one generic keyed store parameterized
by slot. Folding them would need the value types erased into one map (the
`any` coercion the cell store already uses) and would cost the hot
`get-cell` path a closure per read; the encoding hazard — the part that
actually bit — is gone without paying that. If a fifth store lands, revisit.

## 18. `min-load` is a deadline, not a sleep (task #56)

The web image row stopped settling as a row: the three images appeared one
at a time, roughly 250ms apart, and clicks in between did nothing. Measured
in Chrome over CDP (real wall-clock, no virtual time): at 400ms one of three
had settled, at 700ms two, at 1200ms three.

The cause is the shape of the web settle path, not anything about images.
`pump-loop` is a SINGLE always-running strand — deliberately, since §16's
account of the jsweb deadlock rules out forking a one-shot strand per
settle — and it handles one event to completion before receiving the next.
`web-image-settle` sat in that loop doing `wait(min-load)` after each
onload. So the anti-flicker floor was paid N times for N images, serially:
they settled at min-load, 2·min-load, 3·min-load, and every click, wheel and
move event queued behind the whole sum. Native never showed this because
`async-pump` forks a strand per want, so its floors overlap.

The fix is to measure the floor from the KICK rather than from the onload:
the probe stamps `t0` and the settle calls the same `hold-since(t0, d)`
native already used. A batch kicked in one build then shares one deadline —
the first settle absorbs the floor, the rest are already past it — so N
images cost min-load once, and an image that loads after the floor has
elapsed blocks nothing at all. Same anti-flicker guarantee, no serialization.

Worth stating as a rule, because it outlives images: anything that runs on
`pump-loop` is on the input path. A duration that looks per-item there is
really per-item×N of dead input. Express such waits as deadlines against a
shared origin, or keep them off the pump.

`test/ui/web-image-settle.kk` pins it by driving settles the way pump-loop
does — strictly one after another, no forking — and asserting that three
sharing a kick cost about one floor rather than three. Failing-first
verified: the pre-fix code fails it at 602ms (200+200+200), and its
late-onload case at 201ms where the deadline is long past.

Not the cause, though the task's title guessed it was: the `page()` scroll
wrapper. Koka-owned scrolling only made the stall VISIBLE, by routing wheel
events through the same blocked pump the clicks were already stuck in.

## 19. The async boundary was never broken on web -- the compiler was (task #55)

`future-boundary` worked on native and did nothing on jsweb. The gallery
carried a "native-only for now" caption, and §16's account of `image`'s web
path is built entirely around avoiding it: `web-async-image` re-implements the
kick/pending/done/retry machinery by hand because the obvious design -- a
`run` that awaits an onload -- "deadlocked", showing up as later-forked
sibling wants never starting.

None of that was about async. `async-pump` is a tail-recursive supervisor:
receive a want, fork a strand to run it, recurse. The JS backend compiles tail
recursion into `{ tailcall: while(1) { ... } }` whose bindings are
function-scoped `var`s SHARED by every iteration, and it emits closures as
inline `function(){...}` capturing that scope BY REFERENCE. So the strand
forked in iteration N did not hold iteration N's want -- it held a live
reference to a `var` the loop was still reusing. By the time the scheduler ran
it, the next iteration had suspended at `receive` without assigning, and the
want read `undefined`. Every forked run died on the first field access, which
is why nothing ever appeared to start.

The C backend never had this and needs no pass to avoid it: it lambda-lifts
each closure into a struct and copies the captured values in at creation, so
the loop can reuse its locals freely. That is why `Backend/C/FromCore.hs` has
its own `tailCallArg` commented out as unnecessary, while the JS backend
carried one that fixed only the closures passed AS ARGUMENTS TO the recursive
call -- the narrow case -- and left every other escaping closure exposed. The
fix (`captureLoopLams`, Backend/JavaScript/FromCore.hs) applies that same
by-value copy to every lambda created inside a tail-call loop, which is the JS
spelling of what C does with its closure struct. Two exceptions, both about
reading a `var` before its assignment: a lambda applied on the spot needs no
copy, and a local `DefRec`'s own names must stay by reference inside the
group that defines them.

Worth keeping in view for the paper: this is the second time a "the web
backend can't do X" limitation turned out not to be about the web backend.
§18 was a serial pump, this one was codegen; in both cases the portable-
by-construction claim held and the divergence was underneath it. The honest
version of the claim is that portability is only as good as the weakest
backend's compiler, and that the way you find out is by running the same
program on both and diffing the behaviour -- not by reasoning about the
source, which was identical and correct throughout.

`test/jsgen/tailcall-capture.kk` pins it in the compiler's own suite (both a
loop-top-level binding and a pattern binder one block deeper); the gallery's
two boundary cards now run on every backend, retry included.

## 20. Deleting the escape hatch (task #58)

§19 fixed the compiler bug that made `future-boundary` do nothing on jsweb.
This is the cleanup that fix earned: web images were the one part of the
framework with a second, parallel implementation of the async machinery, and
it exists no longer.

`web-async-image` used to re-implement `future-boundary` by hand -- its own
kick, its own RPending/RDone/RFailed transitions, its own retry-by-generation,
its own failure UI -- because the obvious version was believed to deadlock.
The backend carried the other half: an `EvImageLoaded` variant threaded
through the input pump, and `web-image-settle` holding the anti-flicker floor
inside that pump, which §18 then had to convert into a deadline so a row of
images would not settle one at a time. Roughly sixty lines of mechanism, all
of it downstream of one wrong diagnosis.

The diagnosis is worth recording, because the evidence to overturn it was
sitting in the note itself. It blamed a DOM listener resuming a suspended
channel-receive "from outside any strand's own driver loop", and reported the
symptom as *later-forked sibling wants simply never starting*. But a
resumption problem stops something that started; wants that never START are a
different failure, and that is exactly what §19 turned out to be. The
mechanism was invented to explain a symptom it did not actually fit, and then
an architecture was built on it. What made it durable was that the workaround
WORKED -- it shipped, images loaded, and nothing forced a re-examination.

So `web-probe` now simply awaits its offscreen `<img>` and returns the src,
which makes it an ordinary `run`, and web images are a `future-boundary` like
native ones. Everything the hand-rolled path re-implemented comes back for
free, including things it never had: a source change at a stable key now
restarts the load on web too. §18's deadline is gone as well -- not because
the property stopped mattering, but because `async-pump` forks a strand per
want, so the floors overlap by construction rather than by arrangement.
`test/ui/web-image-settle.kk` follows the property down to `async-pump` and
still fails at 602ms if the pump is made to run wants inline.

The lesson for the paper is not "we deleted some code". It is that a
workaround is a hypothesis with a build system attached. This one was wrong
for months and invisible because it succeeded; the thing that exposed it was
running the identical program on two backends and refusing to accept that the
difference was inherent to the platform.

## 21. Why Tier-3 3D waits, and what it is actually blocked on (task #52)

The plan carried an open question: is true 3D (meshes, depth, lighting, glTF)
a matter of binding someone else's stable hardware abstraction, or of writing
a renderer? Neither, it turns out -- and the first answer this ledger gave was
wrong in a way worth keeping visible.

The HAL exists. `package:flutter_gpu` is a thin C++ shim in the engine --
`context`, `command_buffer`, `device_buffer`, `render_pass`,
`render_pipeline`, `shader_library`, `texture`, `surface`, a few thousand
lines of mostly marshalling -- exposing Impeller's INTERNAL C++ API to Dart.
The render passes, pipelines, depth attachments and vertex buffers are all
Impeller's, already written and already cross-backend. `flutter_scene` then
adds the scene graph, glTF import and materials on top. So the honest blocker
is not "3D does not exist here" and not "someone must write a renderer". It
is narrower: Impeller's standalone C ABI does not expose the HAL that
Impeller already has.

`impeller.h` is where that stops. It gives 2D display lists, surfaces wrapping
a Metal drawable / GL FBO / Vulkan swapchain, textures from CPU contents or an
adopted GL handle, `ImpellerContextGetVulkanInfo`, and real custom shaders via
`ImpellerColorSourceCreateFragmentProgramNew` (compiled fragment program +
sampler array + uniform blob). It gives no vertex or index buffers, no meshes,
no depth or stencil, no pipelines, no offscreen render targets. We pin the
stable engine SDK, so the obvious question is whether master has moved --
it has not: master's `impeller.h` is byte-identical to the one we vendor.

Building ON flutter_gpu or flutter_scene is still not open to us, for a reason
that has nothing to do with their complexity: they are Dart, reachable only
through the Dart VM and the Flutter engine, and flutter_gpu has not shipped to
stable. Linking them is not linking a library, it is embedding a runtime. They
are worth referencing as the design that got this right; they are not
something we can sit on top of.

So Tier-3 splits cleanly. Meshes and glTF wait on a C ABI over Impeller's
existing HAL -- upstream work, not ours, and a real contribution if anyone
does it. Everything reachable through fragment programs and textures does not
wait at all: custom shaders with uniforms and samplers, and texture-driven
effects of the Material-ripple kind, are available through the C API we
already bind. That is the scope we are taking.

The part worth carrying into the paper is what flutter_scene does about
portability. On native it rides flutter_gpu; on web, where flutter_gpu does
not exist, it ships its OWN WebGL2 backend as a drop-in. The most mature
cross-backend 3D package in this ecosystem does not get portability from one
abstraction -- it writes a second renderer and presents the seam as an
implementation detail. That belongs next to our own claim, which covers 2D and
stops there on purpose.

## 22. The docs site's pages are data (task #62, rollout step 1)

`samples/ui/site` now declares its pages as `doc-page`/`doc-section` values
(pages.kk) and derives everything navigational from that one list: the
sidebar (grouped by Diátaxis quadrant), the route type (`Home | Page(slug)`),
the on-this-page rail, previous/next, and every cross-page anchor -- section
headings self-anchor by their derived slug, so a title IS an address. The
reusable blocks (`api-entry`, `demo-panel`, `note`, `see-also`, `doc-link`)
carry the code-beside-live-demo pattern; the reference page's Text section is
the first real use. A headless smoke suite drives the real shell: every page
mounted, every derived slug resolved, plus a cross-page anchor check.

Building it caught a real framework bug: the keytree registry retains ids for
unmounted widgets, and `resolve-anchor` consumed a pending anchor on the
first registry match without checking the tree -- so revisiting a page could
silently swallow a later cross-page anchor to it. Resolution now filters to
ids present in the laid-out tree (312c08b9c; anchor-scroll pins it with a
visit/return/request/navigate scenario that read the swallowed-anchor rest
position before the fix).

A verification lesson worth keeping: three of this step's browser "failures"
were the harness, not the site. `find()` on duplicated text measured the toc
rail instead of the heading; a deep link that "overshot" was in fact
clamping to max offset exactly as specified; and an "inert" rail entry was
laid out past the content column's right edge -- clipped invisible by the
scroll, while `getBoundingClientRect` still reported its position, so the
probe clicked a spot Koka's hit walk correctly refuses. That last one is the
step's one real open polish item: the rail row overflows instead of
wrapping (shell-spec territory, with responsive layout).

## 23. A scroll inside a scroll must shrink-wrap its unbounded axis

The docs site found the next framework bug within a day of shipping:
tutorial, how-to, and reference pages scrolled into an apparently infinite
void. `code-block` is a *horizontal* scroll, and it sits inside each page's
*vertical* scroll. `Scroll` layout set its viewport to whatever the parent
offered -- but a vertical scroll lays out its child with unbounded height
(the 1e7 sentinel), so a nested horizontal scroll's viewport height clamped
to ten million pixels, and the page's scroll extent went with it. Pages
without code blocks (home, explanation) were fine, which is what localized
it.

The fix is two-part, and the second part is the lesson. First: in an axis
the parent leaves unbounded, a scroll viewport shrink-wraps to its child
(scrolling along an unbounded axis is meaningless anyway). Second: the
first version of that fix tested `max-h >= unbounded-w` -- equality-ish
against the sentinel -- and still failed on the site, because `code-block`
pads its box, and padding subtracts from constraints on the way down:
the nested scroll sees `1e7 - 28`, unbounded in spirit, no longer the
sentinel. "Unbounded" is therefore a *threshold* (`is-unbounded`, >= 1e6),
not a value to compare against; the `Image` leaf's identical guard is
converted too. test/ui/nested-scroll.kk pins the padded-box shape
specifically -- the rect-only variant of the test passed while the site
still broke.

## 24. The windows suite segfault was a compiler bug (cctx paths lost in ifaces)

test/ui/windows.kk crashed at -O1 (fine at -O0) inside `kk_cctx_copy`,
reached from `with-scene`'s `partition` under multi-shot effect resumption.
Root cause was in the compiler, not lib/ui: `AnalysisCCtx`/`CTail` stamp the
constructor-context path (`conCtxPath`) on the Con OCCURRENCE's repr, and
that stamp was never serialized into `.kki` interfaces -- cross-module
inlining/specialization of any `ctx` code rebuilt the constructors with the
path lost, so a SHARED context copy (multi-shot resume) walked garbage.
Fixed by serializing the stamp (`@cpath("field")` before the constructor in
iface core, Core/Pretty + Core/Parse); regression test
test/optc/cctx-context-path.kk (15-line repro: `partition` + a handler that
resumes twice, -O1). Note for future suite gates: the spec harness caches
std ifaces under `.koka/v3.2.7-test` (--no-buildhash) -- clear it after
compiler changes that alter iface content, or stale ifaces mask the fix.

## 25. `demo-panel`'s live half rendered off-screen -- `intrinsic-width` was the missing piece

Every `demo-panel` on the docs site (code beside its live result) had its
live half clipped past the page's right edge -- not a new regression, the
original `text` reference entry from rollout step 1 had it too, just never
caught by browser verification. Root cause: `code-block` is a horizontal
`scroll`, and a `scroll` offered a *bounded* (but non-tight, non-unbounded)
main-axis constraint reports the FULL width its parent offers, rather than
shrinking to its own content -- correct for a scroll's usual job (fill
available space, e.g. the page's own content scroll) but wrong as a rigid
sibling in `demo-panel`'s row, where it left no room for `live` and pushed
it out past the viewport.

The framework already has the right primitive for this: `intrinsic-width`
probes a child's natural size with an unbounded constraint before laying it
out tight at that measured size (Flutter's IntrinsicWidth). Wrapping
`code-block` in it inside `demo-panel` fixes it without touching `Scroll`
itself, which is working as designed. test/ui/intrinsic-scroll-row.kk pins
the mechanism directly (bare scroll claims the row's full width; wrapped in
`intrinsic-width` it shrinks to content and the sibling follows
immediately) -- note the test wraps its root in a vertical scroll to match
real usage: without one, the row's own cross-axis constraint is the bounded
window height rather than unbounded, which inflates the horizontal scroll's
HEIGHT to fill it and produces a misleading result specific to a bare root.

A gotcha worth keeping: `git stash pop` during this investigation applied
an *unrelated* old stash from earlier in the session (WIP on an unrelated
branch of work) instead of a no-op, causing a spurious merge conflict --
`git stash` silently does nothing when there's nothing tracked-and-dirty to
stash (an edit to an as-yet-uncommitted new file doesn't count), so a later
`pop` reaches for whatever stash *is* on top, which may be someone else's
work-in-progress from much earlier in a long session.

Residual, real, deferred to Task 4's own review (content sizing, not a
framework issue): even after this fix, two of Task 4's new demos still
overflow slightly -- a row+spacer demo wrapped in `fixed(width = Just(200.0))`
and a stack demo wrapped in `fixed(width = Just(120.0))` are wider than the
actual reference-widgets column leaves room for once their code sample is
accounted for. The `fixed` wrapping was only ever cosmetic tidiness; the fix
is almost certainly to drop it and let each demo shrink-wrap to its own
content instead of an arbitrary chosen width.
