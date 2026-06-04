# ICFP 2026 Artifact: HMCFA — A Precise and Practical Big-Step Control Flow Analysis for Effect Handlers

[dockerhub]: https://hub.docker.com/repository/docker/whitim/icfp26-hmcfa/general
[Zenodo]:    https://doi.org/10.5281/zenodo.20517722


> **Naming note:** The analysis is called HMCFA in the paper (H = Handler/delimiter sensitivity).
> Internal scripts and the Lean proof use the earlier working name DMCFA; the names refer to the same system and can be treated as synonyms throughout.


# Getting Started

We provide a Docker image based on Ubuntu 24.04 (for both `x64` and `arm64`).
The image includes a pre-built Koka compiler, the mechanized Lean 4 proof with compiled Mathlib, pre-cached benchmark results, and all figure-generation scripts.

Pull from [Docker Hub][dockerhub]:

```
> docker pull whitim/icfp26-hmcfa:1.0-x64      # x86-64 (Linux, Windows, Intel Mac)
> docker pull whitim/icfp26-hmcfa:1.0-arm64    # arm64 (Apple silicon)
> docker run -it whitim/icfp26-hmcfa:1.0-arm64
```

Or load from the [Zenodo] archive:

```
> gunzip icfp26-hmcfa-1.0-x64.tar.gz
> docker load -i icfp26-hmcfa-1.0-x64.tar
> docker run -it whitim/icfp26-hmcfa:1.0-x64
```

Once inside, the working directory is `/root/koka`.


## Quick Test (~2 minutes)

Run these inside the container to confirm the artifact is working before investing time in the full steps:

```
# 1. Verify the Lean proof compiles (uses pre-compiled Mathlib; should be instant)
> cd lean && lake build && cd ..

# 2. Run a single benchmark with the HMCFA analysis
> stack run koka -- -l analysis/benchmarks/suite/basic.kk --dmcfar --sensitivity='(1,1)'

# 3. Confirm the result matches the reference data
> python3 benchmarks/validate.py
```

Expected output of step 3:

```
Results: 1111 files checked
  PASS   : 5
  MISSING: 1106  (not yet generated on your machine)
Validation passed.
```

The 5 PASSes correspond to the 5 example programs in `suite/basic`.


## Local Installation

Install [Stack](https://docs.haskellstack.org/en/stable/), [elan](https://github.com/leanprover/elan), and Python 3 (with pip), then:

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
| `src/Core/FlowAnalysis/Full/` | Haskell implementation of HMCFA (~6.7k lines across DMCFAR, DMCFA, KCFA) |
| `lean/` | Lean 4 mechanized proofs |
| `benchmarks/results-cached/` | Pre-cached benchmark JSON results (reference data) |
| `benchmarks/plot_utils.py` | Shared metric computation utilities |
| `benchmarks/plot_violin_rir.py` | Generates Figure violin-rir |
| `benchmarks/plot_categorical_metrics.py` | Generates Figure rir-combined |
| `benchmarks/plot_dmcfa_sweep.py` | Generates Figure sweep-combined |
| `benchmarks/plot_expert_tradeoff_metrics.py` | Generates Figure tradeoff |
| `benchmarks/validate.py` | Validates fresh results against reference data |
| `run-benchmarks.kk` | Koka script to re-run all benchmarks (several hours) |

All scripts are run from the **Koka repository root** (`/root/koka` in Docker).


# Step 1 — Verify the Lean Proof

The `lean/` directory contains approximately 18k lines of Lean 4 (roughly 3k definitions + 15k proof lines) mechanizing the correctness of HMCFA.
In Docker, Mathlib is already compiled and this step takes only a few seconds.

```
> cd lean && lake build && cd ..
```

Expected output (last line):

```
Build completed successfully (N jobs)
```

There should be no errors and no uses of `sorry`.
The proof uses three axioms (declared in `DMCFA/Lemmas.lean`), all standard assumptions about well-formed programs:

| Axiom | Statement | Justification |
|---|---|---|
| `exists_fresh` | For any concrete store `σ`, there exists a `VAddr` (`Nat`) with `σ a = none` | Any finitely-supported store over an infinite domain leaves fresh addresses available. Used in `Completeness.lean` and `TimestampedSoundness.lean` when allocating fresh concrete addresses. |
| `barendregt_fresh_env` | For any environment `ρ` and binder variable `x`, `ρ x = none` | Barendregt convention: bound variables are chosen fresh with respect to the current environment. |
| `barendregt_var_ne` | Any two distinct binder variables `x y` satisfy `x ≠ y` | Barendregt convention: all binders in a term are given unique names. |

These axioms hold for any program in α-normal form.


## Proof Architecture

The proof proceeds through a chain of four semantics connected by pairwise soundness and completeness theorems.
The diagram below (also included as [`lean/equivalence-diagram.pdf`](../../../lean/equivalence-diagram.pdf)) illustrates the structure:

```
B&P            Concrete        Fresh-Guarded     Timestamped      Abstract
(substitution) (env/store)     (proof device)    (paper)          (finite)
    ⇓_bp           ⇓_eval          ⇓^κτf_eval        ⇓^κτ_eval       ⇓̂^κτ_eval
    ←——————————————→   ←—————————————————→   ←——————————————→   ————————→
     sound/complete      sound/complete         sound/complete    soundness
      ~700+600 loc        ~4k+1.2k loc           ~70+2.4k loc     ~600 loc
       +~1.3k shared       +~0.5k shared          +~3.2k shared
```

**B&P (Bauer and Pretnar)** is a standard substitution-based big-step semantics used as a specification.
**Concrete** is the environment/store big-step semantics formalised in the paper.
**Fresh-Guarded** is an intermediate proof device that adds freshness side-conditions to timestamps, making it easier to lift results to the paper's **Timestamped** semantics.
The final step abstracts the timestamped semantics into the finite **Abstract** domain used by HMCFA.

Key top-level theorems:

| Theorem | File | Statement |
|---|---|---|
| `soundness` | `Soundness.lean` | Concrete eval → B&P eval |
| `completeness_open'` | `Completeness.lean` | B&P eval → Concrete eval |
| `simulation` | `FreshnessSimulation.lean` | Concrete → Fresh-Guarded (freshness invariant) |
| `naive_to_strict_from_empty` | `TimestampedToFresh.lean` | Address Freshness (Theorem 3 of paper) |
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
| `TimestampedToFresh.lean`, `FreshToTimestamped.lean` | Bridge lemmas between timestamped/fresh-guarded | ~110 + ~70 |
| `TimestampedComponents.lean`, `TimestampedSemantics.lean` | Timestamped semantics components | ~360 + ~370 |
| `TimestampedSoundness.lean` | Fresh-Guarded → Timestamped soundness | ~1200 |
| `TimestampedCompleteness.lean` | Timestamped → Fresh-Guarded completeness | ~3900 |
| `TimeOrder.lean`, `TmkPreservation.lean` | Timestamp ordering and preservation lemmas | ~1250 + ~170 |
| `AbstractComponents.lean`, `AbstractSemantics.lean` | Abstract domain definitions | ~110 + ~165 |
| `Abstraction.lean` | Timestamped → Abstract soundness | ~625 |
| `UniqueLabels.lean` | Label uniqueness supporting lemmas | ~710 |


# Step 2 — Regenerate Paper Figures (~1 minute)

Run the four plotting scripts from inside the container:

```
> python3 benchmarks/plot_violin_rir.py
> python3 benchmarks/plot_categorical_metrics.py
> python3 benchmarks/plot_dmcfa_sweep.py
> python3 benchmarks/plot_expert_tradeoff_metrics.py
```

Output PNGs are written to `benchmarks/images/`.
The scripts automatically load from `benchmarks/results/` if you have run Step 3; otherwise they fall back to `benchmarks/results-cached/` (the reference data from our runs) with a notice.

| Output file | Paper figure |
|---|---|
| `benchmarks/images/plot_violin_rir.png` | Figure violin-rir |
| `benchmarks/images/plot_categorical_combined.png` | Figure rir-combined |
| `benchmarks/images/plot_dmcfa_sweep_combined_rir.png` | Figure sweep-combined |
| `benchmarks/images/plot_expert_tradeoff_combined_time.png` | Figure tradeoff |


## Copying Figures Out of the Container

To inspect the figures on your host machine, start the container with a name, run the plotting scripts, then copy and remove:

```
> docker run -it --name icfp26 whitim/icfp26-hmcfa:1.0-arm64
# ... run the plotting scripts inside, then exit ...
> docker cp icfp26:/root/koka/benchmarks/images ./icfp26-images
> docker rm icfp26
```

Or mount a host directory so figures appear on your host directly:

```
> docker run -it -v $(pwd)/icfp26-images:/root/koka/benchmarks/images whitim/icfp26-hmcfa:1.0-arm64
```


## Expected Figures

> **Reproducibility:** Figures violin-rir, rir-combined, and sweep-combined are computed purely from precision metrics and are fully deterministic — when generated from the same benchmark data the underlying values will be **identical** to the paper figures (modulo timeouts).
> Minor rendering differences (font hinting, DPI, platform quirks) may cause slight visual variation, but shapes, relative heights, and all numerical values will match (modulo timeouts).
> The tradeoff figure is the only exception where data values may also differ, as its x-axis is analysis time.

**Figure violin-rir** (`plot_violin_rir.png`) — Two violin plots (Value RIR left, Continuation RIR right) showing per-benchmark RIR distributions for five configurations (1-kCFA, 2-kCFA, H(1,0), H(1,1), H(1,2)).
The white diamond marks the shifted geometric mean.

**Figure rir-combined** (`plot_categorical_combined.png`) — Grouped bar chart of RIR (shifted geometric mean) broken down by benchmark category (Micro-Suite, Koka-Samples, Koka-Gen, All >300 states), with value precision on the left and continuation precision on the right.
Red numbers above a bar indicate timeouts excluded from that aggregate (timeouts could potentially change depending on your hardware).

**Figure sweep-combined** (`plot_dmcfa_sweep_combined_rir.png`) — Line plots of RIR (shifted geometric mean over benchmarks with >300 0-CFA states) as m sweeps 0→2 for each fixed h.
Small numbers along the bottom indicate timeout counts excluded from that point's aggregate.

**Figure tradeoff** (`plot_expert_tradeoff_combined_time.png`) — Precision-cost scatter plot comparing 1-kCFA (×) against H(1,1) (•) per benchmark, with analysis time on the x-axis (log scale) and RIR on the y-axis.
Green = win-win; blue = trade-off (more precise but slower); red = regression; gray = similar precision.

> **Note on the tradeoff figure:** The x-axis shows analysis time in seconds, which depends on the reviewer's CPU.
> The RIR values on the y-axis are deterministic and will match exactly.
> The horizontal positions of benchmarks will shift with machine speed.
> The color classification (green/blue/red/gray) is unlikely to change for most benchmarks, but may for a few where the timing ratio is close to the classification boundary.


# Step 3 — Run the Full Benchmarks (Optional, Several Hours)

The complete suite covers ~100 programs across three categories (Micro-Suite, Koka-Samples, Koka-Gen) under nine H(h,m) configurations plus k-CFA baselines.
On a MacBook Pro M3 Max this takes several hours.

```
> stack run koka -- -e run-benchmarks.kk
```

Results are written to `benchmarks/results/`.
Afterwards, run Step 4 to validate and re-run Step 2 to regenerate the figures from your own data.


# Step 4 — Validate Benchmark Results (~1 minute)

Run after Step 3 to confirm your results match the reference data (generated on a MacBook Pro M3 Max):

```
> python3 benchmarks/validate.py
```

**Expected output:** all files report `PASS`.
A `WARN` on `isTimeout` means the timeout status differs — expected on machines faster or slower than the reference M3 Max; the precision metrics are still compared and must match.
A `FAIL` indicates a substantive discrepancy in the analysis output.

If `benchmarks/results/` is empty (Step 3 not yet run), the script reports all files as `MISSING` and exits cleanly.
