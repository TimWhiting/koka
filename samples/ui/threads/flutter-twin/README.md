# Flutter twin of samples/ui/threads

The same demo as the Koka app one directory up -- an fps meter that reads
"parked" until something animates, a bouncing bar (500ms easeInOut), and a
Compute button running fib(38) off the UI thread -- built with Flutter, which
uses the SAME renderer (Impeller). Same demo, same renderer, different
framework: the comparison isolates the framework layer.

Build/run (needs a Flutter SDK):

    flutter create --platforms=macos .
    flutter run -d macos --release
    # auto-start the animation (for headless measurement):
    flutter build macos --release --dart-define=AUTOSTART=true

## Measurements, round 2 (2026-07-23, post-memoization arc)

> VINTAGE: these numbers were taken on the PRE-retention build. The
> keytrie keep-alive commit (same day, ledger §10) grew the identity hot
> path (three knode fields, stale/retained miss scans, kt-open/kt-close
> per memo re-run); expected cost on a non-retaining app is near zero but
> is not yet measured -- re-run this protocol before quoting.

Same machine, ProMotion display (adaptive, up to 120Hz). Protocol change
that MATTERS: macOS throttles occluded/non-frontmost windows (and Flutter
additionally reacts to occlusion), which made round-1-style runs bimodal
(flutter animating read anywhere from 4.6% to 16.8% depending on what had
focus during the 10s sample). All numbers below force the measured app
FRONTMOST via System Events before sampling, alternate the two apps
back-to-back to cancel thermal drift, and report cputime deltas over 10s
after a 6s warmup. Koka autostarts with `./app-native --spin`; flutter with
`--dart-define=AUTOSTART=true`.

| metric (frontmost)   | koka lib/ui (memo) | flutter            |
|----------------------|--------------------|--------------------|
| idle CPU             | 0.1%               | 0.0%               |
| animating CPU (cool) | 6.5 / 6.9 / 7.8%   | 7.2 / 8.1 / 7.8%   |
| animating CPU (warm) | 10.3 / 11.3%       | 12.4 / 13.7%       |
| animating RSS        | 102 MB             | 105–114 MB         |
| presents/s           | ~85 measured       | not instrumented (read its on-screen meter) |

Reading: in EVERY adjacent pair across the session (10 pairs, cool and
warm), koka ≤ flutter -- parity when cool, ~15-20% cheaper when warm. In
round 1 (2026-07-17, 60Hz, below) flutter was ~4.8x cheaper; the gap was
closed by the post-profile library work: text-metrics + shaped-paragraph
caches, the frame-clock fixes (no echo frames, batched drains), and the
present-path cleanups. An A/B on THIS demo (memo boundaries vs none,
tightly interleaved: 10.3 vs 10.45% mean) shows the `memo` boundaries
themselves are a WASH here -- the static chrome is tiny; memo's measured
wins are on memo-shaped apps (samples/ui/memodemo's 150-row list: -25%
animating CPU; the full sample app: 37%->20%). Caveat to close: koka
presents ~85/s (its frame loop sleeps a full interval then renders);
flutter's achieved rate on this display was not instrumented -- eyeball
both fps meters before quoting per-frame numbers.

## Measurements, round 1 (2026-07-17, 60Hz display, pre-memoization)

cputime deltas over 10s, single window visible (NOT occlusion-controlled --
see above); koka = clang -O2, flutter = release; both apps pace to the
display, ~60 presents/s:

| metric              | koka lib/ui          | flutter              |
|---------------------|----------------------|----------------------|
| idle CPU            | 0.2%                 | 0.5%                 |
| idle RSS            | 103 MB               | 102 MB               |
| animating CPU       | 16.7%                | 3.5%                 |
| animating RSS       | 104 MB               | 117 MB               |
| app size            | 4.3 MB + 10.9 MB impeller + 55 KB host = ~15.3 MB | 37.8 MB bundle |

Reading (round 1): at-rest parity (both demand-driven, ~0%). Animating,
Flutter was ~5x cheaper: it rebuilds only dirty widgets against a RETAINED
render tree and repaints damaged layers, while koka lib/ui then rebuilt the
whole widget tree, re-laid-out, re-shaped every paragraph and re-recorded
the full display list EVERY frame. Koka wins footprint in both rounds:
~2.5x smaller on disk, less RSS while animating.

## Scope note: widget fidelity

Flutter's Material widgets are also FAR deeper trees than ours: a single
`ElevatedButton` composes ink ripples (InkWell splash/highlight), elevation
overlays, focus/hover overlays, Semantics, Material, and layout wrappers --
dozens of elements where our `primary-button` is a handful of nodes with a
scalar hover/press animation. Little of that fidelity is exercised by this
demo (no button interaction during the animating measurement), but the
per-widget work the two frameworks do is not equivalent, and a fidelity-
matched comparison would need our components to grow ripple-class visuals.
Read the CPU parity as "same demo at each framework's native fidelity",
not "same work".

## Scope note: accessibility

The frameworks are not architecturally equivalent: Flutter carries a
semantics (accessibility) pipeline and lib/ui has none. But Flutter builds
its semantics tree LAZILY -- only once the embedder reports assistive tech
active (`SemanticsBinding.ensureSemantics`) -- and no assistive tech was
running during these measurements, so the round-2 numbers compare like with
like at runtime. The planned lib/ui design mirrors Flutter's strategy:
default components emit default semantics through the effect stack into a
SPARSE projection of the keytrie (an int-map from stable key ids; parentage
by key-path prefix), gated by an enable flag whose flip dirties the whole
app (the existing dirty-storm mechanism); memo boundaries cache their
semantics fragment exactly as they cache layout and display lists. Web can
lower semantics to ARIA on the DOM it already owns.
