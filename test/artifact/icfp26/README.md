# ICFP 2026 Paper Artifact: HMCFA: A Precise and Practical Big-Step Control Flow Analysis for Effect Handlers

[dockerhub]: https://hub.docker.com/repository/docker/timwhiting/icfp26-hmcfa/general
[Zenodo]:    https://zenodo.org/records/TODO

> **Naming note:** The analysis is called HMCFA in the paper (H = Handler/delimiter sensitivity).
> Internal scripts and the Lean proof use the earlier working name DMCFA; the names refer to the
> same system and can be treated as synonyms throughout.

# Getting Started

We provide a Docker image based on Ubuntu 24.04 (for both `x64` and `arm64`).
The image includes a pre-built Koka compiler, the mechanized Lean 4 proof with
compiled mathlib, pre-cached benchmark results, and all figure-generation scripts.
For convenience we also uploaded the image to [dockerhub]:

```
> docker pull timwhiting/icfp26-hmcfa:1.0-x64
> docker run -it timwhiting/icfp26-hmcfa:1.0-x64
```

or on macOS Apple silicon:

```
> docker pull timwhiting/icfp26-hmcfa:1.0-arm64
> docker run -it timwhiting/icfp26-hmcfa:1.0-arm64
```

When using the [Zenodo] provided `tar.gz` files, use `docker load`:

```
> gunzip icfp26-hmcfa-1.0-x64.tar.gz
> docker load -i icfp26-hmcfa-1.0-x64.tar
> docker run -it timwhiting/icfp26-hmcfa:1.0-x64
```

Once inside the container, the working directory is `/root/koka` (the Koka repository root).


## Local Installation

Install [Stack](https://docs.haskellstack.org/en/stable/),
[elan](https://github.com/leanprover/elan), and Python 3 (with pip), then:

```
> git clone --recursive https://github.com/koka-lang/koka -b final-cfa koka
> cd koka
> stack build
> stack exec koka -- util/link-std.kk
> pip3 install matplotlib numpy pandas scipy seaborn
> cd lean && lake build   # compiles the Lean proof; takes ~30–60 min first time
> cd ..
```


# Artifact Contents

| Path | Description |
|---|---|
| `lean/` | Lean 4 mechanized proofs |
| `benchmarks/results-cached/` | Pre-cached benchmark JSON results (reference data) |
| `benchmarks/plot_utils.py` | Shared metric computation utilities |
| `benchmarks/plot_violin_rir.py` | Generates Figure violin-rir |
| `benchmarks/plot_categorical_metrics.py` | Generates Figure rir-combined |
| `benchmarks/plot_dmcfa_sweep.py` | Generates Figure sweep-combined |
| `benchmarks/plot_expert_tradeoff_metrics.py` | Generates Figure tradeoff |
| `benchmarks/validate.py` | Validates new results against reference data |
| `run-benchmarks.kk` | Koka script to re-run all benchmarks (several hours) |

All scripts are run from the **Koka repository root** (`/root/koka` in Docker).


# Step 1 — Verify the Lean Proof

The `lean/` directory contains approximately 18k lines of Lean 4 (roughly 3k definitions + 15k proof lines) mechanizing the correctness of HMCFA. The proof depends on Mathlib;
in Docker this is already compiled.

```
> cd lean && lake build
```

Expected output (last line):

```
Build completed successfully (N jobs)
```

There should be no errors and no uses of `sorry`. The proof does use three
axioms (declared in `Dmcfa/Lemmas.lean`), all of which are standard
assumptions about well-formed programs:

| Axiom | Statement | Justification |
|---|---|---|
| `exists_fresh` | For any concrete store `σ`, there exists a `VAddr` (`Nat`) with `σ a = none` | Any finitely-supported store over an infinite domain leaves fresh addresses available. Used in `Completeness.lean` and `TimestampedSoundness.lean` when allocating fresh concrete addresses. |
| `barendregt_fresh_env` | For any environment `ρ` and binder variable `x`, `ρ x = none` | Barendregt convention: bound variable names are chosen fresh with respect to the current environment |
| `barendregt_var_ne` | Any two distinct binder variables `x y` satisfy `x ≠ y` | Barendregt convention: all binders in a term are given unique names |

These axioms are not `sorry`s — they express well-known, semantically justified
conventions that hold for any program in α-normal form.


## Proof Architecture

The proof proceeds through a chain of four semantics, connected by pairwise
soundness and completeness theorems. The diagram below (also included as
[`lean/equivalence-diagram.pdf`](../../../lean/equivalence-diagram.pdf)) illustrates the structure:

```
B&P            Concrete        Fresh-Guarded     Timestamped      Abstract
(substitution) (env/store)     (proof device)    (paper)          (finite)
    ⇓_bp           ⇓_eval          ⇓^κτf_eval        ⇓^κτ_eval       ⇓̂^κτ_eval
    ←——————————————→   ←—————————————————→   ←——————————————→   ————————→
     sound/complete      sound/complete         sound/complete    soundness
      ~700+600 loc        ~4k+1.2k loc           ~70+2.4k loc     ~600 loc
       +~1.3k shared       +~0.5k shared          +~3.2k shared
```

**B&P (bind-and-plug)** is a standard substitution-based big-step semantics used
as a specification. **Concrete** is the environment/store big-step semantics
formalised in the paper. **Fresh-Guarded** is an intermediate proof device that
adds freshness side-conditions to timestamps, making it easier to lift results
to the paper's **Timestamped** semantics. The final step abstracts the timestamped
semantics into the finite **Abstract** domain used by HMCFA.

The key top-level theorems are:

| Theorem | File | Statement |
|---|---|---|
| `soundness` | `Soundness.lean` | Concrete eval → B&P eval |
| `completeness_open'` | `Completeness.lean` | B&P eval → Concrete eval |
| `simulation` | `FreshnessSimulation.lean` | Concrete → Fresh-Guarded (freshness invariant) |
| `naive_to_strict_from_empty` | `NaiveToFresh.lean` | Address Freshness (Theorem 3 of paper) |
| `fresh_to_concrete` | `TimestampedSoundness.lean` | Fresh-Guarded → Timestamped (soundness) |
| `completeness_combined` | `TimestampedCompleteness.lean` | Timestamped → Fresh-Guarded (completeness) |


## File Map

| File | Role | ~Lines |
|---|---|---|
| `Syntax.lean`, `BPSyntax.lean` | ANF and B&P syntax definitions | ~300 + ~750 |
| `Semantics.lean`, `BPSemantics.lean` | Concrete and B&P operational semantics | ~450 + ~175 |
| `Components.lean`, `Lemmas.lean` | Store/env/continuation components & lemmas | ~100 + ~1200 |
| `Equivalence.lean`, `Correspondence.lean` | B&P ↔ Concrete term and value equivalences | ~160 + ~460 |
| `Soundness.lean` | Concrete → B&P soundness | ~620 |
| `Completeness.lean` | B&P → Concrete completeness | ~670 |
| `FreshSemantics.lean`, `FreshnessLemmas.lean` | Fresh-Guarded semantics and supporting lemmas | ~450 + ~1100 |
| `FreshnessSimulation.lean` | Concrete → Fresh-Guarded simulation (largest file) | ~2400 |
| `NaiveToFresh.lean`, `FreshToNaive.lean` | Bridge lemmas between naive/fresh-guarded | ~110 + ~70 |
| `TimestampedComponents.lean`, `NaiveSemantics.lean` | Timestamped semantics components | ~360 + ~370 |
| `TimestampedSoundness.lean` | Fresh-Guarded → Timestamped soundness | ~1200 |
| `TimestampedCompleteness.lean` | Timestamped → Fresh-Guarded completeness | ~3900 |
| `TimeOrder.lean`, `TmkPreservation.lean` | Timestamp ordering and preservation lemmas | ~1250 + ~170 |
| `AbstractComponents.lean`, `AbstractSemantics.lean` | Abstract domain definitions | ~110 + ~165 |
| `Abstraction.lean` | Timestamped → Abstract soundness | ~625 |
| `UniqueLabels.lean` | Label uniqueness supporting lemmas | ~710 |


# Step 2 — Regenerate Paper Figures (~1 minute)

All four figure scripts write PNGs to `benchmarks/images/`. They automatically
load from `benchmarks/results/` (your freshly run benchmarks) if that directory
has data, and otherwise fall back to `benchmarks/results-cached/` (the reference
data) with a notice. Run Step 3 first for true reproducibility; or run these
directly to see the reference figures from our runs.

```
> python3 benchmarks/plot_violin_rir.py
> python3 benchmarks/plot_categorical_metrics.py
> python3 benchmarks/plot_dmcfa_sweep.py
> python3 benchmarks/plot_expert_tradeoff_metrics.py
```

Output files:

| File | Paper figure |
|---|---|
| `benchmarks/images/plot_violin_rir.png` | Figure violin-rir |
| `benchmarks/images/plot_categorical_combined.png` | Figure rir-combined |
| `benchmarks/images/plot_dmcfa_sweep_combined_rir.png` | Figure sweep-combined |
| `benchmarks/images/plot_expert_tradeoff_combined_time.png` | Figure tradeoff |


## Expected Figures

> **Reproducibility:** Figures violin-rir, rir-combined, and sweep-combined are
> computed purely from precision metrics and are fully deterministic — when
> generated from the same benchmark data (Step 2 using cached results, or
> Step 3 + Step 2 after a fresh run) the underlying values will be **identical**
> to the paper figures. Minor rendering differences (font hinting, DPI, platform
> quirks) may cause slight visual variation, but the shapes, relative heights,
> and all numerical values will match. The tradeoff figure is the only exception
> where data values may also differ, as its x-axis is analysis time.

**Figure violin-rir** (`plot_violin_rir.png`) — Two violin plots (Value RIR
left, Continuation RIR right) showing per-benchmark RIR distributions for five
configurations (1-kCFA, 2-kCFA, H(1,0), H(1,1), H(1,2)). The white diamond
marks the shifted geometric mean.

**Figure rir-combined** (`plot_categorical_combined.png`) — Grouped bar chart of
RIR (shifted geometric mean) broken down by benchmark category (Micro-Suite,
Koka-Samples, Koka-Gen, All >300 states), with value precision on the left and
continuation precision on the right. Red numbers above a bar indicate timeouts
excluded from that aggregate.

**Figure sweep-combined** (`plot_dmcfa_sweep_combined_rir.png`) — Line plots of
RIR (shifted geometric mean over benchmarks with >300 0-CFA states) as m sweeps
0→2 for each fixed h. Small numbers along the bottom indicate timeout counts
excluded from that point's aggregate.

**Figure tradeoff** (`plot_expert_tradeoff_combined_time.png`) — Precision-cost
scatter plot comparing 1-kCFA (×) against H(1,1) (•) per benchmark, with
analysis time on the x-axis (log scale) and RIR on the y-axis.
Green = win-win; blue = trade-off (more precise but slower); red = regression;
gray = similar precision.

> **Note on the tradeoff figure:** The x-axis shows analysis time in seconds,
> which depends on the reviewer's CPU. The RIR values on the y-axis are
> deterministic and will match exactly. The horizontal positions of benchmarks
> will shift with machine speed. The color classification (green/blue/red/gray)
> is unlikely to change for most benchmarks, but may for a few where the timing
> ratio is close to the classification boundary.


# Step 3 — Run the Full Benchmarks (Optional, Several Hours)

The complete benchmark suite covers ~100 programs across three categories
(Micro-Suite, Koka-Samples, Koka-Gen) under nine H(h,m) configurations plus
k-CFA baselines. On a MacBook Pro M3 Max this takes several hours.

```
> stack run koka -- -e run-benchmarks.kk
```

Results are written to `benchmarks/results/`. Afterwards, re-run Step 4 to
validate that your results match the reference data, and re-run Step 2 to
regenerate the figures from your own runs.


# Step 4 — Validate Benchmark Results (~1 minute)

Run this after Step 3 to confirm that your analysis output matches the reference
data generated on a MacBook Pro M3 Max.

```
> python3 benchmarks/validate.py
```

**Expected output:** all files report `PASS`. A `WARN` on `isTimeout` means the
timeout status differs — this is expected on machines faster or slower than the
reference M3 Max; the precision metrics are still compared and must match. A
`FAIL` indicates a substantive discrepancy in the analysis output.

If `benchmarks/results/` is empty (Step 3 has not been run), the script reports
all files as `MISSING` and exits without error.
