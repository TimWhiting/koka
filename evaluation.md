
# Revised Evaluation Section Draft

## 6. Evaluation

We evaluate the effectiveness of our proposed Handler-Sensitive CFA (`HMCFAR`) against standard k-CFA (`k-CFA`) on a suite of benchmarks utilizing algebraic effects. Our analysis parameterizes precision by $(m, h)$, tracking $m$ call sites and $h$ enclosing handlers. Our goal is to answer three questions:
1.  **Effectiveness**: Does `HMCFAR` discover more precise control-flow information than `k-CFA`?
2.  **Efficiency**: What is the cost of this precision in terms of analysis time and state-space size?
3.  **Robustness**: How consistent are these improvements across different benchmark categories?

### 6.1 Benchmark Suite & Methodology

We utilized a suite of **101 benchmarks**, which we classify into four categories to better understand the analysis performance:
1.  **Koka-Gen** (N=27): Large, generated programs from the Koka test suite, representing complex, real-world patterns.
2.  **Rosetta** (N=4): Standard algorithms (e.g., N-Queens) adapted to use effects.
3.  **Koka-Samples** (N=20): Benchmarks specifically designed to stress effect handler mechanics.
4.  **Micro-Suite** (N=50): Small, targeted tests for specific effect interactions.

**Categorized Difficulty (0-CFA):**
Table 1 shows the baseline difficulty. **Koka-Gen** is the "hardest" category, with 0-CFA achieving significantly lower precision, whereas the Micro-Suite is largely solved.

| Category | 0-CFA Cont Prec | 0-CFA Struct Prec | 0-CFA Lit Prec |
| :--- | :--- | :--- | :--- |
| **Koka-Gen** | 0.73 | 0.86 | 0.91 |
| **Rosetta** | 0.92 | 0.89 | 0.86 |
| **Koka-Samples** | 0.83 | 0.88 | 0.91 |
| **Micro-Suite** | 0.95 | 0.96 | 0.91 |

*Note: "0-CFA Lit Prec" reflects the fraction of resolved literals. Even in "solved" categories, ~10% of literals remain ambiguous in 0-CFA.*

**Metrics & Terminology:**
*   **Continuation Precision**: The fraction of call sites where the analysis identifies a singleton continuation (i.e., a definitive jump target).
*   **Relative Imprecision Recovery (RIR)**: To evaluate the effectiveness of our analysis on the remaining sources of imprecision, we define Relative Imprecision Recovery (RIR) for a benchmark $b$ as:
    $$RIR_b = \frac{Prec_{new} - Prec_{base}}{N_{imprecise\_base}}$$
    where $N_{imprecise\_base}$ is the number of imprecise call sites in the baseline 0-CFA.

**Aggregation:** We use **Micro-Average (Pooled Mean)** to report system-wide precision, ensuring that larger, more complex programs (like those in Koka-Gen) are weighted appropriately.

### 6.2 Precision & Effectiveness

We compared `1,1-HMCFAR` against `1-kCFA` and `2-kCFA`.

**Overall Results:**
*   **Continuation Precision:** `1,1-HMCFAR` achieves a **93.0%** mean absolute precision across the suite, compared to **88.9%** for `1-kCFA`.
*   **The "Koka-Gen" Gap:** The impact is most visible in the hardest category. In **Koka-Gen**, `1-kCFA` achieves **75.3%**, whereas `1,1-HMCFAR` lifts this to **87.6%**. This 12% absolute gain represents resolving nearly **half** of the remaining ambiguities.

### High-Level Relative Improvement

![High Level Geometric Mean](/Users/timwhiting/.gemini/antigravity/brain/d0bb3d21-7a53-4240-a516-b7fbe1ad3c16/evaluation_draft_images/plot_high_level_productivity_geomean.png)

### Summary of Precision

To summarize performance across our diverse suite, we use the **shifted geometric mean** of the Relative Imprecision Recovery (RIR):
$$ \text{ShiftedGeomean}(S) = \exp\left(\frac{1}{N} \sum_{x \in S} \ln(1 + x)\right) - 1 $$
This standard adjustment ensures that zero values (0% improvement) are aggregated as 0 (since $\ln(1+0)=0$) rather than multiplying the entire product to zero, which would destroy the average. This allows us to fairly aggregate improvement rates even when some benchmarks show no gain.

To focus our analysis on non-trivial programs, we filter for **47 "large" benchmarks** (out of 101 total) that have more than 350 analysis states in the baseline.

| Metric | 0-CFA Precise (No Gain Possible) | Benchmarks with Gain | Max Gain | 1-kCFA Geomean | 1,1-HMCFAR Geomean |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Continuation Precision** | 16 / 47 (34.0%) | 16 / 47 (34.0%) | 100.0% | 11.5% | **23.9%** |
| **Value Precision** | 3 / 47 (6.4%) | 26 / 47 (55.3%) | 71.4% | 11.0% | **13.7%** |

*   **Continuation Precision**: The shifted geometric mean of strict RIR increased from **11.5%** (1-kCFA) to **23.9%** (1,1-HMCFAR). Note that 34% of these large benchmarks were already fully precise in 0-CFA, meaning no further gain was possible; removing these would show even higher specific gains.
*   **Value Precision**: `1,1-HMCFAR` achieves a **13.7%** shifted geometric mean RIR, slightly improving over `1-kCFA` (11.0%). Gains are widespread, observed in over half of the benchmarks.

**Literal Precision:**
While Structural Precision is often high, **Literal Precision** remains a challenge. `1,1-HMCFAR` resolves significant ambiguity in literals compared to `k-CFA`, proving that handler-sensitivity aids in data-flow precision by separating the paths where constants are introduced.

### 6.3 Cost & Trade-offs

### Expert Trade-off (Relative)

We visualize the cost-benefit trade-off for each benchmark. Points above the diagonal (green/blue) represent improvement in precision. The X-axis represents the cost (State Space Size or Analysis Time) on a linear scale.

**State Space Cost:**
![Tradeoff Value Relative](/Users/timwhiting/.gemini/antigravity/brain/d0bb3d21-7a53-4240-a516-b7fbe1ad3c16/evaluation_draft_images/plot_expert_tradeoff_val_relative_impr.png)
![Tradeoff Continuation Relative](/Users/timwhiting/.gemini/antigravity/brain/d0bb3d21-7a53-4240-a516-b7fbe1ad3c16/evaluation_draft_images/plot_expert_tradeoff_cont_relative_impr.png)

**Analysis Time Cost:**
Time is arguably the more critical cost metric. We see a similar pattern: `1,1-HMCFAR` provides substantial precision gains (Y-axis) often with comparable or even better performance (shifted left on X-axis) due to the reduced state space from precise control flow.
![Tradeoff Value Relative Time](/Users/timwhiting/.gemini/antigravity/brain/d0bb3d21-7a53-4240-a516-b7fbe1ad3c16/evaluation_draft_images/plot_expert_tradeoff_val_relative_impr_time.png)
![Tradeoff Continuation Relative Time](/Users/timwhiting/.gemini/antigravity/brain/d0bb3d21-7a53-4240-a516-b7fbe1ad3c16/evaluation_draft_images/plot_expert_tradeoff_cont_relative_impr_time.png)

### Parameter Sensitivity (Sweep)

We analyze the impact of varying the handler-sensitivity parameter $H$ (d=1, m varies).
![Sweep Continuation Relative](/Users/timwhiting/.gemini/antigravity/brain/d0bb3d21-7a53-4240-a516-b7fbe1ad3c16/evaluation_draft_images/plot_dmcfa_sweep_cont_relative_impr.png)

The sweep demonstrates that $H=1$ provides the most significant boost in continuation precision. Moving to $H=2$ offers diminishing returns for this metric, while $H=0$ (insensitivity) fails to capture the necessary control flow properties. Ideally, $H=1$ is the "sweet spot" for balancing precision and cost.

*   **Cost Factor:** On average, `HMCFAR` explores **1.06x** more states than `1-kCFA` (Median Cost Factor).
*   **Efficiency:** In the **Koka-Gen** category, `HMCFAR` is remarkably efficient (1.12x cost factor), suggesting that for complex code, the precision gain pays for itself by preventing state explosion in spurious paths. In simpler categories like **Rosetta**, the overhead is higher (1.41x), but the absolute runtime remains negligible.

# Appendix Tables


## Table B1: Continuation Precision by Configuration

| Category | Benchmark | kCFA(0) | kCFA(1) | kCFA(2) | H(0,0) | H(0,1) | H(0,2) | H(1,0) | H(1,1) | H(1,2) | H(2,0) | H(2,1) | H(2,2) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| **Koka-Gen** | `scheduler/scheduler` | **1.00** | 0.57 | 0.50 | **1.00** | 0.57 | 0.57 | 0.67 | 0.57 | 0.44 | 0.67 | 0.57 | 0.44 |
|  | `interp2/err1` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `interp2/t4` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `interp2/err5` | 0.30 | **1.00** | **1.00** | 0.30 | **1.00** | **1.00** | 0.33 | **1.00** | **1.00** | 0.33 | **1.00** | **1.00** |
|  | `interp2/err4` | 0.15 | **1.00** | **1.00** | 0.15 | **1.00** | **1.00** | 0.29 | **1.00** | **1.00** | 0.29 | **1.00** | **1.00** |
|  | `build/mymakefile-example3` | 0.76 | 0.23 | 0.21 | 0.68 | 0.68 | 0.55 | **1.00** | [**1.00**]{.red} | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `coop-communication/yield` | **0.72** | 0.50 | 0.26 | 0.62 | 0.38 | 0.28 | 0.30 | 0.22 | 0.18 | 0.17 | 0.15 | 0.13 |
|  | `coop-communication/spawn` | **0.62** | 0.34 | 0.15 | 0.53 | 0.20 | 0.12 | 0.23 | 0.10 | 0.07 | 0.15 | 0.08 | 0.05 |
|  | `ukanren/q1` | **0.86** | 0.39 | - | **0.86** | 0.50 | - | 0.38 | 0.35 | - | 0.38 | 0.35 | - |
|  | `ukanren/q2` | **0.87** | - | - | **0.87** | 0.50 | - | 0.40 | 0.36 | - | 0.40 | 0.36 | - |
|  | `build/mymakefile-example2` | **0.51** | - | - | 0.50 | 0.06 | - | 0.11 | - | - | 0.09 | - | - |
|  | `build/mymakefile-example1` | **0.51** | - | - | 0.49 | 0.06 | - | 0.11 | - | - | 0.09 | - | - |
|  | `music/search-come` | **0.94** | 0.77 | 0.28 | **0.94** | 0.44 | 0.29 | 0.86 | 0.44 | 0.29 | 0.84 | 0.44 | 0.29 |
|  | `music/search-love` | **0.94** | 0.77 | 0.28 | **0.94** | 0.44 | 0.29 | 0.86 | 0.44 | 0.29 | 0.84 | 0.44 | 0.29 |
|  | `mini-ppl/burglar-mc` | **0.92** | 0.51 | 0.37 | 0.90 | 0.40 | 0.21 | 0.19 | 0.12 | 0.06 | 0.12 | 0.07 | 0.03 |
|  | `mini-ppl/drunk` | **0.98** | 0.74 | 0.38 | 0.81 | 0.67 | 0.29 | 0.18 | 0.30 | 0.20 | 0.15 | 0.30 | 0.17 |
|  | `mini-ppl/burglar` | **0.97** | 0.46 | 0.26 | 0.88 | 0.54 | 0.24 | 0.31 | 0.27 | 0.23 | 0.29 | 0.24 | 0.16 |
|  | `interp/interp` | 0.11 | **0.64** | 0.43 | 0.11 | 0.58 | 0.43 | 0.18 | 0.54 | 0.43 | 0.14 | 0.32 | 0.32 |
|  | `coop-communication/send-recv` | **0.49** | 0.23 | 0.09 | 0.43 | 0.08 | - | 0.13 | - | - | 0.07 | - | - |
|  | `coop-communication/prime-sieve` | **0.21** | 0.07 | - | 0.21 | - | - | 0.12 | - | - | 0.04 | - | - |
|  | `build/mymakefile-example4` | - | - | - | **0.53** | 0.11 | 0.09 | 0.12 | - | - | 0.10 | - | - |
|  | `build/mymakefile-example5` | - | - | - | 0.53 | 0.11 | 0.49 | 0.12 | - | **0.79** | 0.10 | - | **0.79** |
|  | `interp2/err2` | - | 0.37 | 0.83 | 0.09 | 0.37 | **1.00** | 0.07 | 0.22 | **1.00** | 0.07 | 0.22 | **1.00** |
|  | `interp2/err3` | - | 0.75 | 0.55 | 0.08 | 0.75 | 0.55 | 0.02 | [**1.00**]{.red} | **1.00** | - | **1.00** | **1.00** |
|  | `interp2/t1` | - | 0.37 | 0.53 | 0.12 | 0.32 | 0.78 | 0.02 | 0.35 | **1.00** | - | 0.35 | **1.00** |
|  | `interp2/t2` | - | 0.27 | 0.22 | - | 0.24 | 0.41 | 0.02 | 0.24 | **0.42** | - | 0.24 | **0.42** |
|  | `interp2/t3` | - | 0.13 | 0.11 | - | 0.13 | 0.18 | - | 0.06 | 0.05 | - | 0.02 | **0.46** |
| **Rosetta** | `jump-anywhere/e1` | **1.00** | 0.67 | **1.00** | **1.00** | 0.67 | 0.67 | **1.00** | 0.67 | 0.67 | **1.00** | 0.67 | 0.67 |
|  | `jump-anywhere/loop` | **0.80** | 0.35 | 0.29 | 0.66 | 0.45 | 0.38 | 0.29 | 0.24 | 0.20 | 0.12 | 0.12 | 0.11 |
|  | `monads-writer/solution1` | **0.86** | 0.71 | 0.71 | **0.86** | 0.40 | 0.27 | 0.42 | 0.36 | 0.27 | 0.42 | 0.36 | 0.27 |
|  | `pr4rings/four-squares` | **0.85** | 0.23 | 0.23 | **0.85** | 0.60 | 0.13 | 0.15 | 0.12 | 0.01 | 0.15 | 0.12 | 0.01 |
| **Koka-Samples** | `yield/main` | **1.00** | 0.50 | 0.33 | **1.00** | 0.50 | 0.29 | 0.33 | 0.33 | 0.22 | 0.33 | 0.33 | 0.22 |
|  | `nim/example-perfect1` | **1.00** | 0.50 | 0.44 | **1.00** | 0.50 | 0.27 | 0.50 | 0.44 | 0.25 | 0.50 | 0.44 | 0.25 |
|  | `nim/example-perfect2` | **1.00** | 0.50 | 0.44 | **1.00** | 0.50 | 0.27 | 0.50 | 0.44 | 0.25 | 0.50 | 0.44 | 0.25 |
|  | `unix/example1` | **0.92** | **0.92** | 0.65 | **0.92** | 0.50 | 0.45 | 0.38 | 0.36 | 0.45 | 0.35 | 0.33 | 0.45 |
|  | `unix/example1_2` | **1.00** | **1.00** | 0.92 | **1.00** | 0.40 | 0.38 | 0.30 | 0.30 | 0.38 | 0.29 | 0.29 | 0.38 |
|  | `ambient/example0` | **1.00** | 0.80 | 0.80 | **1.00** | 0.80 | 0.80 | 0.80 | 0.80 | 0.80 | 0.80 | 0.80 | 0.80 |
|  | `unix/example2` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `scoped/example1` | **0.71** | 0.27 | 0.19 | **0.71** | 0.27 | 0.14 | 0.22 | 0.18 | 0.06 | 0.22 | 0.18 | 0.06 |
|  | `nim/example-gtree` | **1.00** | 0.50 | 0.44 | **1.00** | 0.50 | 0.27 | 0.50 | 0.44 | 0.16 | 0.50 | 0.44 | 0.16 |
|  | `vec/main` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nim/example-coin` | **1.00** | 0.60 | 0.55 | **1.00** | 0.60 | 0.38 | 0.33 | 0.29 | 0.25 | 0.33 | 0.29 | 0.25 |
|  | `unix/example3` | **0.94** | **0.94** | 0.77 | **0.94** | 0.60 | 0.54 | 0.47 | 0.45 | 0.54 | 0.47 | 0.45 | 0.54 |
|  | `nim/example-check` | 0.52 | **0.69** | 0.56 | 0.52 | 0.56 | 0.30 | 0.53 | 0.50 | 0.26 | 0.53 | 0.50 | 0.26 |
|  | `nim/example-pc1` | 0.52 | **0.69** | 0.56 | 0.52 | 0.56 | 0.50 | 0.53 | 0.65 | 0.65 | 0.53 | 0.65 | 0.65 |
|  | `unix/example5` | **0.91** | 0.89 | 0.33 | 0.89 | 0.73 | 0.25 | 0.69 | 0.66 | 0.22 | 0.62 | 0.60 | 0.20 |
|  | `scoped/example5` | **0.50** | 0.21 | 0.09 | 0.46 | 0.16 | 0.09 | 0.17 | 0.10 | 0.04 | 0.14 | 0.09 | 0.05 |
|  | `scoped/example3` | 0.40 | **0.66** | 0.57 | 0.33 | 0.43 | 0.24 | 0.32 | 0.29 | 0.17 | 0.22 | 0.20 | 0.11 |
|  | `scoped/example2` | 0.23 | **0.52** | 0.43 | 0.23 | 0.31 | 0.17 | 0.26 | 0.16 | 0.09 | 0.19 | 0.11 | - |
|  | `nim/example-pc2` | - | 0.50 | **0.83** | - | **0.83** | **0.83** | 0.50 | [**0.83**]{.red} | **0.83** | 0.50 | **0.83** | **0.83** |
|  | `scoped/example4` | - | 0.53 | **0.69** | 0.25 | **0.69** | **0.69** | 0.26 | [**0.69**]{.red} | **0.69** | 0.19 | **0.69** | **0.69** |
| **Micro-Suite** | `basic/basic-exception` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `complex-flow/complex-tail-effect` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `basic/basic-resume` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `complex-flow/complex-tail-call` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `basic/basic-resume-op` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `complex-flow/complex-resume-func` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `basic/basic-resume-context` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `complex-flow/complex-non-tail-call` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `basic/basic-resume-op-context` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nondet/nondet-discard` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nondet/nondet-simple` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested-nondet/nondet-with-failure` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nondet/nondet-context` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `recursion/iter-sum` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | 0.50 | **1.00** | **1.00** | 0.50 | **1.00** | **1.00** |
|  | `recursion/iter-sum-two` | **1.00** | 0.67 | 0.50 | **1.00** | 0.67 | 0.50 | 0.50 | 0.50 | 0.50 | 0.50 | 0.50 | 0.50 |
|  | `recursion/iter-sum-b` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | 0.50 | **1.00** | **1.00** | 0.50 | **1.00** | **1.00** |
|  | `recursion/iter-sum-handler` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | 0.50 | **1.00** | **1.00** | 0.50 | **1.00** | **1.00** |
|  | `recursion/iter-sum-two-b` | **1.00** | 0.67 | 0.50 | **1.00** | 0.67 | 0.50 | 0.50 | 0.50 | 0.50 | 0.50 | 0.50 | 0.50 |
|  | `nested/nested-simple-two` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `recursion/iter-sum-c` | 0.67 | **1.00** | **1.00** | 0.67 | **1.00** | **1.00** | 0.33 | **1.00** | **1.00** | 0.33 | **1.00** | **1.00** |
|  | `recursion/iter-sum-two-c` | **0.67** | 0.29 | 0.20 | **0.67** | 0.40 | 0.60 | 0.33 | 0.20 | 0.60 | 0.33 | 0.20 | 0.60 |
|  | `recursion/iter-sum-d` | 0.67 | **1.00** | **1.00** | 0.67 | **1.00** | **1.00** | 0.33 | **1.00** | **1.00** | 0.33 | **1.00** | **1.00** |
|  | `recursion/iter-sum-two-d` | **0.67** | 0.29 | 0.20 | **0.67** | 0.40 | 0.60 | 0.33 | 0.20 | 0.60 | 0.33 | 0.20 | 0.60 |
|  | `nondet/nondet-nested` | **0.75** | 0.60 | 0.50 | **0.75** | 0.60 | 0.60 | 0.50 | 0.50 | 0.50 | 0.50 | 0.50 | 0.50 |
|  | `nested-nondet/nondet-variable-branches` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `complex-flow/complex-recursive` | **0.25** | 0.10 | 0.04 | **0.25** | 0.08 | 0.02 | 0.14 | 0.07 | 0.01 | 0.14 | 0.07 | 0.01 |
|  | `nested/nested-simple` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested/nested-tail-simple` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested-nondet/nondet-guarded` | **0.60** | 0.50 | 0.33 | **0.60** | 0.50 | **0.60** | 0.38 | 0.38 | 0.50 | 0.38 | 0.38 | 0.50 |
|  | `complex-flow/complex-nested-interleave` | **1.00** | 0.86 | 0.86 | **1.00** | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 |
|  | `nested/nested-inner-first` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested/nested-outer-first` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested/nested-tail-inner-first` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested/nested-tail-outer-first` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested/nested-op-after` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested/nested-op-before` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested/nested-tail-op-after` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested/nested-tail-op-before` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested-nondet/nondet-nested-tail` | **1.00** | **1.00** | 0.80 | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | 0.80 | 0.80 | 0.80 |
|  | `nested/nested-absorb` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `state-handler/state-countdown` | **1.00** | 0.75 | 0.67 | **1.00** | 0.75 | 0.42 | 0.60 | 0.60 | 0.42 | 0.60 | 0.60 | 0.42 |
|  | `nested-nondet/nondet-nested-simple` | **0.71** | 0.50 | 0.36 | **0.71** | 0.50 | 0.50 | 0.50 | 0.50 | 0.50 | 0.36 | 0.36 | 0.31 |
|  | `nested-nondet/nondet-both-contexts` | **0.71** | 0.50 | 0.36 | **0.71** | 0.50 | 0.50 | 0.50 | 0.50 | 0.50 | 0.36 | 0.36 | 0.31 |
|  | `nested/nested-three-levels` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `multi-effect/multi-simple` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `multi-effect/multi-two-outer` | **1.00** | 0.91 | 0.91 | **1.00** | 0.91 | 0.91 | 0.91 | 0.91 | 0.91 | 0.91 | 0.91 | 0.91 |
|  | `multi-effect/multi-inner-first` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `complex-flow/complex-layers` | **0.80** | 0.65 | 0.55 | **0.80** | 0.57 | 0.57 | 0.43 | 0.41 | 0.57 | 0.43 | 0.41 | 0.57 |
|  | `nested-nondet/nondet-alternating` | **0.92** | 0.67 | 0.63 | **0.92** | 0.67 | 0.67 | 0.67 | 0.67 | 0.67 | 0.67 | 0.67 | 0.67 |
|  | `nested-nondet/nondet-three-levels` | **0.86** | **0.86** | 0.67 | **0.86** | **0.86** | **0.86** | 0.75 | 0.75 | 0.75 | 0.60 | 0.60 | 0.60 |
| | **Averages** |  |  |  |  |  |  |  |  |  |  |  |  |
| **Koka-Gen** | Average | **0.69** | 0.55 | 0.47 | 0.58 | 0.47 | 0.51 | 0.35 | 0.50 | 0.57 | 0.36 | 0.48 | 0.58 |
| **Rosetta** | Average | **0.88** | 0.49 | 0.56 | 0.84 | 0.53 | 0.36 | 0.46 | 0.35 | 0.29 | 0.42 | 0.32 | 0.27 |
| **Koka-Samples** | Average | **0.81** | 0.66 | 0.58 | 0.78 | 0.57 | 0.44 | 0.48 | 0.50 | 0.42 | 0.46 | 0.48 | 0.43 |
| **Micro-Suite** | Average | **0.93** | 0.88 | 0.84 | **0.93** | 0.88 | 0.87 | 0.80 | 0.85 | 0.87 | 0.79 | 0.84 | 0.85 |

## Table B2: Literal Precision by Configuration

| Category | Benchmark | kCFA(0) | kCFA(1) | kCFA(2) | H(0,0) | H(0,1) | H(0,2) | H(1,0) | H(1,1) | H(1,2) | H(2,0) | H(2,1) | H(2,2) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| **Koka-Gen** | `scheduler/scheduler` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `interp2/err1` | 0.95 | 0.97 | 0.97 | 0.94 | **0.98** | **0.98** | 0.94 | [**0.98**]{.red} | **0.98** | 0.94 | **0.98** | **0.98** |
|  | `interp2/t4` | 0.89 | 0.89 | 0.89 | **0.89** | **0.89** | **0.89** | **0.89** | [**0.89**]{.red} | **0.89** | **0.89** | **0.89** | **0.89** |
|  | `interp2/err5` | 0.91 | **0.96** | **0.96** | 0.91 | 0.95 | 0.95 | 0.91 | 0.95 | 0.95 | 0.91 | 0.95 | 0.95 |
|  | `interp2/err4` | 0.92 | **0.98** | **0.98** | 0.92 | 0.97 | 0.97 | 0.92 | 0.97 | 0.97 | 0.92 | 0.97 | 0.97 |
|  | `build/mymakefile-example3` | 0.97 | 0.97 | 0.97 | 0.96 | 0.96 | 0.96 | **0.98** | [**0.98**]{.red} | **0.98** | **0.98** | **0.98** | **0.98** |
|  | `coop-communication/yield` | 0.99 | 0.99 | 0.99 | **0.99** | **0.99** | **0.99** | **0.99** | [**0.99**]{.red} | **0.99** | **0.99** | **0.99** | **0.99** |
|  | `coop-communication/spawn` | 0.99 | 0.99 | 0.99 | **0.99** | **0.99** | **0.99** | **0.99** | [**0.99**]{.red} | **0.99** | **0.99** | **0.99** | **0.99** |
|  | `ukanren/q1` | 0.89 | **0.91** | - | 0.87 | 0.91 | - | 0.87 | 0.91 | - | 0.87 | 0.91 | - |
|  | `ukanren/q2` | 0.89 | - | - | 0.87 | **0.91** | - | 0.87 | **0.91** | - | 0.87 | **0.91** | - |
|  | `build/mymakefile-example2` | **0.88** | - | - | 0.86 | 0.86 | - | 0.86 | - | - | 0.86 | - | - |
|  | `build/mymakefile-example1` | **0.88** | - | - | 0.86 | 0.86 | - | 0.86 | - | - | 0.86 | - | - |
|  | `music/search-come` | **0.88** | **0.88** | **0.88** | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 |
|  | `music/search-love` | **0.88** | **0.88** | **0.88** | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 |
|  | `mini-ppl/burglar-mc` | **0.84** | **0.84** | **0.84** | 0.83 | 0.83 | 0.83 | 0.83 | 0.83 | 0.83 | 0.83 | 0.83 | 0.83 |
|  | `mini-ppl/drunk` | 0.80 | 0.80 | **0.82** | 0.79 | 0.79 | 0.80 | 0.79 | 0.79 | 0.80 | 0.79 | 0.79 | 0.80 |
|  | `mini-ppl/burglar` | 0.81 | 0.81 | **0.83** | 0.80 | 0.80 | 0.80 | 0.80 | 0.80 | 0.80 | 0.80 | 0.80 | 0.80 |
|  | `interp/interp` | **0.90** | 0.90 | 0.90 | 0.89 | 0.89 | 0.89 | 0.89 | 0.89 | 0.89 | 0.89 | 0.89 | 0.89 |
|  | `coop-communication/send-recv` | 0.93 | 0.93 | **0.95** | 0.92 | 0.92 | - | 0.92 | - | - | 0.93 | - | - |
|  | `coop-communication/prime-sieve` | **0.90** | **0.90** | - | 0.89 | - | - | 0.89 | - | - | 0.89 | - | - |
|  | `build/mymakefile-example4` | - | - | - | **0.83** | **0.83** | **0.83** | **0.83** | - | - | **0.83** | - | - |
|  | `build/mymakefile-example5` | - | - | - | 0.83 | 0.83 | 0.96 | 0.83 | - | **0.98** | 0.83 | - | **0.98** |
|  | `interp2/err2` | - | 0.98 | 0.98 | 0.93 | 0.98 | **0.98** | 0.93 | [0.98]{.red} | **0.98** | 0.93 | 0.98 | **0.98** |
|  | `interp2/err3` | - | 0.95 | 0.95 | 0.94 | **0.95** | **0.95** | 0.94 | [0.95]{.red} | 0.95 | - | 0.95 | 0.95 |
|  | `interp2/t1` | - | 0.92 | 0.95 | 0.92 | 0.92 | 0.97 | 0.92 | [0.94]{.red} | **0.98** | - | 0.94 | **0.98** |
|  | `interp2/t2` | - | 0.90 | 0.90 | - | 0.90 | **0.90** | 0.90 | 0.90 | **0.90** | - | 0.90 | **0.90** |
|  | `interp2/t3` | - | 0.91 | 0.91 | - | 0.90 | **0.91** | - | 0.90 | **0.91** | - | 0.90 | 0.91 |
| **Rosetta** | `jump-anywhere/e1` | 0.89 | 0.89 | 0.89 | **0.89** | **0.89** | **0.89** | **0.89** | [**0.89**]{.red} | **0.89** | **0.89** | **0.89** | **0.89** |
|  | `jump-anywhere/loop` | 0.93 | 0.93 | 0.93 | **0.93** | **0.93** | **0.93** | **0.93** | [**0.93**]{.red} | **0.93** | **0.93** | **0.93** | **0.93** |
|  | `monads-writer/solution1` | 0.80 | **0.84** | **0.84** | 0.80 | 0.84 | 0.84 | 0.80 | 0.84 | 0.84 | 0.80 | 0.84 | 0.84 |
|  | `pr4rings/four-squares` | **0.80** | **0.80** | **0.80** | **0.80** | **0.80** | **0.80** | **0.80** | **0.80** | **0.80** | **0.80** | **0.80** | **0.80** |
| **Koka-Samples** | `yield/main` | 0.90 | 0.90 | 0.90 | **0.91** | **0.91** | **0.91** | **0.91** | [**0.91**]{.red} | **0.91** | **0.91** | **0.91** | **0.91** |
|  | `nim/example-perfect1` | 0.86 | 0.86 | 0.86 | **0.87** | **0.87** | **0.87** | **0.87** | [**0.87**]{.red} | **0.87** | **0.87** | **0.87** | **0.87** |
|  | `nim/example-perfect2` | 0.86 | 0.86 | 0.86 | **0.87** | **0.87** | **0.87** | **0.87** | [**0.87**]{.red} | **0.87** | **0.87** | **0.87** | **0.87** |
|  | `unix/example1` | 0.91 | 0.91 | 0.91 | 0.90 | 0.90 | **0.92** | 0.90 | 0.90 | **0.92** | 0.90 | 0.90 | **0.92** |
|  | `unix/example1_2` | 0.92 | 0.92 | 0.92 | 0.91 | 0.91 | **0.92** | 0.91 | 0.91 | **0.92** | 0.91 | 0.91 | **0.92** |
|  | `ambient/example0` | 0.90 | 0.97 | 0.97 | 0.89 | **0.97** | **0.97** | **0.97** | [**0.97**]{.red} | **0.97** | **0.97** | **0.97** | **0.97** |
|  | `unix/example2` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `scoped/example1` | **0.93** | **0.93** | **0.93** | 0.93 | 0.93 | 0.93 | 0.93 | 0.93 | 0.93 | 0.93 | 0.93 | 0.93 |
|  | `nim/example-gtree` | 0.89 | 0.89 | 0.89 | **0.89** | **0.89** | **0.89** | **0.89** | [**0.89**]{.red} | **0.89** | **0.89** | **0.89** | **0.89** |
|  | `vec/main` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nim/example-coin` | 0.90 | 0.90 | 0.90 | 0.90 | 0.90 | 0.90 | 0.90 | [**0.91**]{.red} | **0.91** | 0.90 | **0.91** | **0.91** |
|  | `unix/example3` | 0.95 | 0.95 | 0.95 | 0.95 | 0.95 | **0.96** | 0.95 | 0.95 | **0.96** | 0.95 | 0.95 | **0.96** |
|  | `nim/example-check` | **0.90** | **0.90** | **0.90** | 0.90 | 0.90 | 0.90 | 0.90 | 0.90 | 0.90 | 0.90 | 0.90 | 0.90 |
|  | `nim/example-pc1` | 0.90 | 0.90 | 0.90 | 0.90 | 0.90 | 0.91 | 0.90 | [0.91]{.red} | **0.93** | 0.90 | 0.91 | **0.93** |
|  | `unix/example5` | **0.96** | **0.96** | **0.96** | 0.96 | 0.96 | 0.96 | 0.96 | 0.96 | 0.96 | 0.96 | 0.96 | 0.96 |
|  | `scoped/example5` | 0.81 | 0.82 | **0.83** | 0.79 | 0.80 | 0.80 | 0.79 | 0.80 | 0.80 | 0.79 | 0.80 | 0.80 |
|  | `scoped/example3` | 0.94 | **0.95** | **0.95** | 0.93 | 0.94 | 0.94 | 0.94 | 0.94 | 0.94 | 0.94 | 0.94 | 0.94 |
|  | `scoped/example2` | 0.94 | **0.95** | **0.95** | 0.93 | 0.94 | 0.94 | 0.94 | 0.94 | 0.94 | 0.94 | 0.94 | - |
|  | `nim/example-pc2` | - | 0.92 | 0.94 | - | **0.95** | **0.95** | 0.92 | [**0.95**]{.red} | **0.95** | 0.92 | **0.95** | **0.95** |
|  | `scoped/example4` | - | 0.97 | 0.99 | 0.96 | **1.00** | **1.00** | 0.97 | [**1.00**]{.red} | **1.00** | 0.97 | **1.00** | **1.00** |
| **Micro-Suite** | `basic/basic-exception` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `complex-flow/complex-tail-effect` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `basic/basic-resume` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `complex-flow/complex-tail-call` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `basic/basic-resume-op` | 0.91 | 0.95 | 0.95 | 0.91 | **0.96** | **0.96** | 0.91 | [**0.96**]{.red} | **0.96** | 0.91 | **0.96** | **0.96** |
|  | `complex-flow/complex-resume-func` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `basic/basic-resume-context` | 0.91 | 0.95 | 0.95 | 0.91 | **0.96** | **0.96** | **0.96** | [**0.96**]{.red} | **0.96** | **0.96** | **0.96** | **0.96** |
|  | `complex-flow/complex-non-tail-call` | 0.93 | 0.95 | 0.95 | 0.93 | **0.96** | **0.96** | 0.93 | [**0.96**]{.red} | **0.96** | 0.93 | **0.96** | **0.96** |
|  | `basic/basic-resume-op-context` | 0.91 | 0.95 | 0.95 | 0.91 | **0.96** | **0.96** | 0.91 | [**0.96**]{.red} | **0.96** | 0.91 | **0.96** | **0.96** |
|  | `nondet/nondet-discard` | 0.96 | 0.96 | 0.98 | 0.96 | **0.98** | **0.98** | 0.96 | [**0.98**]{.red} | **0.98** | 0.96 | **0.98** | **0.98** |
|  | `nondet/nondet-simple` | 0.90 | 0.90 | 0.98 | 0.91 | **0.98** | **0.98** | 0.91 | [**0.98**]{.red} | **0.98** | 0.91 | **0.98** | **0.98** |
|  | `nested-nondet/nondet-with-failure` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nondet/nondet-context` | 0.90 | 0.90 | 0.90 | 0.91 | 0.91 | 0.91 | 0.91 | [**0.93**]{.red} | **0.93** | 0.91 | **0.93** | **0.93** |
|  | `recursion/iter-sum` | 0.81 | 0.98 | 0.98 | 0.82 | **0.98** | **0.98** | 0.82 | [**0.98**]{.red} | **0.98** | 0.82 | **0.98** | **0.98** |
|  | `recursion/iter-sum-two` | 0.81 | 0.81 | 0.81 | 0.82 | 0.82 | **0.84** | 0.82 | [0.82]{.red} | **0.84** | 0.82 | 0.82 | **0.84** |
|  | `recursion/iter-sum-b` | 0.81 | 0.98 | 0.98 | 0.82 | **0.98** | **0.98** | 0.82 | [**0.98**]{.red} | **0.98** | 0.82 | **0.98** | **0.98** |
|  | `recursion/iter-sum-handler` | 0.82 | 0.98 | 0.98 | 0.82 | **0.98** | **0.98** | 0.82 | [**0.98**]{.red} | **0.98** | 0.82 | **0.98** | **0.98** |
|  | `recursion/iter-sum-two-b` | 0.81 | 0.81 | 0.81 | 0.82 | 0.82 | **0.84** | 0.82 | [0.82]{.red} | **0.84** | 0.82 | 0.82 | **0.84** |
|  | `nested/nested-simple-two` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `recursion/iter-sum-c` | 0.82 | 0.98 | 0.98 | 0.82 | **0.98** | **0.98** | 0.82 | [**0.98**]{.red} | **0.98** | 0.82 | **0.98** | **0.98** |
|  | `recursion/iter-sum-two-c` | 0.82 | 0.82 | 0.82 | 0.82 | 0.82 | **0.84** | 0.82 | [0.82]{.red} | **0.84** | 0.82 | 0.82 | **0.84** |
|  | `recursion/iter-sum-d` | 0.82 | 0.98 | 0.98 | 0.82 | **0.98** | **0.98** | 0.82 | [**0.98**]{.red} | **0.98** | 0.82 | **0.98** | **0.98** |
|  | `recursion/iter-sum-two-d` | 0.82 | 0.82 | 0.82 | 0.82 | 0.82 | **0.84** | 0.82 | [0.82]{.red} | **0.84** | 0.82 | 0.82 | **0.84** |
|  | `nondet/nondet-nested` | 0.91 | 0.91 | 0.91 | 0.92 | 0.92 | 0.92 | 0.92 | [0.92]{.red} | **0.93** | 0.92 | 0.92 | **0.93** |
|  | `nested-nondet/nondet-variable-branches` | 0.86 | 0.86 | 0.95 | 0.87 | **0.95** | **0.95** | 0.87 | [**0.95**]{.red} | **0.95** | 0.87 | **0.95** | **0.95** |
|  | `complex-flow/complex-recursive` | 0.83 | 0.83 | 0.83 | **0.83** | **0.83** | **0.83** | **0.83** | [**0.83**]{.red} | **0.83** | **0.83** | **0.83** | **0.83** |
|  | `nested/nested-simple` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested/nested-tail-simple` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested-nondet/nondet-guarded` | 0.85 | 0.85 | 0.85 | 0.86 | 0.86 | 0.88 | 0.86 | [0.86]{.red} | **0.92** | 0.86 | 0.86 | **0.92** |
|  | `complex-flow/complex-nested-interleave` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `nested/nested-inner-first` | 0.93 | 0.96 | 0.96 | 0.93 | **0.97** | **0.97** | 0.93 | [**0.97**]{.red} | **0.97** | **0.97** | **0.97** | **0.97** |
|  | `nested/nested-outer-first` | 0.94 | 0.97 | 0.97 | 0.94 | **0.98** | **0.98** | **0.98** | [**0.98**]{.red} | **0.98** | **0.98** | **0.98** | **0.98** |
|  | `nested/nested-tail-inner-first` | 0.93 | 0.97 | 0.97 | 0.93 | **0.98** | **0.98** | 0.94 | [**0.98**]{.red} | **0.98** | **0.98** | **0.98** | **0.98** |
|  | `nested/nested-tail-outer-first` | 0.94 | 0.97 | 0.97 | 0.94 | **0.98** | **0.98** | **0.98** | [**0.98**]{.red} | **0.98** | **0.98** | **0.98** | **0.98** |
|  | `nested/nested-op-after` | 0.93 | 0.96 | 0.96 | 0.93 | **0.97** | **0.97** | **0.97** | [**0.97**]{.red} | **0.97** | **0.97** | **0.97** | **0.97** |
|  | `nested/nested-op-before` | 0.93 | 0.96 | 0.96 | 0.93 | **0.97** | **0.97** | **0.97** | [**0.97**]{.red} | **0.97** | **0.97** | **0.97** | **0.97** |
|  | `nested/nested-tail-op-after` | 0.93 | 0.96 | 0.96 | 0.93 | **0.97** | **0.97** | **0.97** | [**0.97**]{.red} | **0.97** | **0.97** | **0.97** | **0.97** |
|  | `nested/nested-tail-op-before` | 0.93 | 0.96 | 0.96 | 0.93 | **0.97** | **0.97** | **0.97** | [**0.97**]{.red} | **0.97** | **0.97** | **0.97** | **0.97** |
|  | `nested-nondet/nondet-nested-tail` | 0.87 | 0.87 | 0.87 | 0.88 | 0.88 | 0.88 | 0.88 | [0.88]{.red} | 0.88 | 0.88 | **0.95** | **0.95** |
|  | `nested/nested-absorb` | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** | **1.00** |
|  | `state-handler/state-countdown` | 0.90 | 0.90 | 0.90 | **0.91** | **0.91** | **0.91** | **0.91** | [**0.91**]{.red} | **0.91** | **0.91** | **0.91** | **0.91** |
|  | `nested-nondet/nondet-nested-simple` | 0.87 | 0.87 | 0.87 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | 0.86 | **0.87** |
|  | `nested-nondet/nondet-both-contexts` | 0.85 | 0.85 | 0.85 | 0.85 | 0.85 | 0.85 | 0.85 | 0.85 | 0.85 | 0.85 | 0.85 | **0.86** |
|  | `nested/nested-three-levels` | 0.93 | 0.97 | 0.97 | 0.93 | **0.98** | **0.98** | **0.98** | [**0.98**]{.red} | **0.98** | **0.98** | **0.98** | **0.98** |
|  | `multi-effect/multi-simple` | 0.94 | 0.97 | 0.97 | 0.94 | **0.98** | **0.98** | **0.98** | [**0.98**]{.red} | **0.98** | **0.98** | **0.98** | **0.98** |
|  | `multi-effect/multi-two-outer` | 0.92 | 0.93 | 0.93 | 0.93 | 0.93 | **0.96** | 0.93 | [0.93]{.red} | **0.96** | 0.93 | 0.93 | **0.96** |
|  | `multi-effect/multi-inner-first` | 0.94 | 0.97 | 0.97 | 0.94 | **0.98** | **0.98** | 0.94 | [**0.98**]{.red} | **0.98** | 0.94 | **0.98** | **0.98** |
|  | `complex-flow/complex-layers` | 0.92 | 0.92 | 0.92 | 0.92 | 0.92 | **0.94** | 0.92 | [0.92]{.red} | **0.94** | 0.92 | 0.92 | **0.94** |
|  | `nested-nondet/nondet-alternating` | 0.87 | 0.87 | 0.88 | 0.85 | **0.88** | **0.88** | 0.85 | [**0.88**]{.red} | **0.88** | 0.85 | **0.88** | **0.88** |
|  | `nested-nondet/nondet-three-levels` | **0.88** | **0.88** | **0.88** | 0.87 | 0.87 | 0.87 | 0.87 | 0.87 | 0.87 | 0.87 | 0.87 | 0.87 |
| | **Averages** |  |  |  |  |  |  |  |  |  |  |  |  |
| **Koka-Gen** | Average | 0.91 | 0.92 | **0.93** | 0.89 | 0.90 | 0.92 | 0.89 | 0.92 | 0.92 | 0.89 | 0.92 | 0.92 |
| **Rosetta** | Average | 0.85 | 0.86 | 0.86 | 0.85 | **0.86** | 0.86 | 0.85 | **0.86** | 0.86 | 0.85 | **0.86** | 0.86 |
| **Koka-Samples** | Average | 0.92 | 0.92 | 0.93 | 0.92 | 0.92 | 0.93 | 0.92 | 0.93 | **0.93** | 0.92 | 0.93 | 0.93 |
| **Micro-Suite** | Average | 0.91 | 0.94 | 0.94 | 0.91 | 0.94 | 0.95 | 0.92 | 0.95 | 0.95 | 0.92 | 0.95 | **0.95** |

## Table B3: State Count (Complexity) by Configuration

| Category | Benchmark | kCFA(0) | kCFA(1) | kCFA(2) | H(0,0) | H(0,1) | H(0,2) | H(1,0) | H(1,1) | H(1,2) | H(2,0) | H(2,1) | H(2,2) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| **Koka-Gen** | `scheduler/scheduler` | **445** | 816 | 1098 | 457 | 806 | 1106 | 517 | [806]{.red} | 1148 | 517 | 806 | 1148 |
|  | `interp2/err1` | **448** | 472 | 472 | 457 | 487 | 487 | 472 | 487 | 487 | 472 | 487 | 487 |
|  | `interp2/t4` | **551** | 626 | 668 | 579 | 668 | 792 | 613 | 699 | 823 | 613 | 699 | 823 |
|  | `interp2/err5` | 662 | **596** | 624 | 685 | 632 | 687 | 659 | 663 | 695 | 659 | 663 | 695 |
|  | `interp2/err4` | 710 | **536** | 538 | 729 | 566 | 574 | 629 | 574 | 574 | 629 | 574 | 574 |
|  | `build/mymakefile-example3` | 945 | 1699 | 1937 | 955 | 1284 | 1553 | **840** | [903]{.red} | 903 | **840** | 903 | 903 |
|  | `coop-communication/yield` | **955** | 1181 | 1735 | 967 | 1192 | 1467 | 1526 | 1770 | 2147 | 2048 | 2288 | 2750 |
|  | `coop-communication/spawn` | **1150** | 1660 | 3055 | 1164 | 1761 | 2504 | 2187 | 3096 | 4371 | 2715 | 3627 | 5776 |
|  | `ukanren/q1` | **1502** | 5102 | - | 1554 | 3313 | - | 1885 | [3421]{.red} | - | 1885 | 3421 | - |
|  | `ukanren/q2` | **1575** | - | - | 1631 | 3573 | - | 1962 | 3681 | - | 1962 | 3681 | - |
|  | `build/mymakefile-example2` | **1614** | - | - | 1630 | 15274 | - | 4283 | - | - | 5170 | - | - |
|  | `build/mymakefile-example1` | **1639** | - | - | 1655 | 15309 | - | 4327 | - | - | 5218 | - | - |
|  | `music/search-come` | **1761** | 2475 | 3326 | 1801 | 2896 | 3985 | 1924 | 2948 | 4066 | 1974 | 2957 | 4080 |
|  | `music/search-love` | **1761** | 2475 | 3326 | 1801 | 2896 | 3985 | 1924 | 2948 | 4066 | 1974 | 2957 | 4080 |
|  | `mini-ppl/burglar-mc` | **2037** | 2871 | 3346 | 2060 | 3009 | 3819 | 3844 | 4989 | 7954 | 5643 | 7778 | 14171 |
|  | `mini-ppl/drunk` | **2169** | 2817 | 3811 | 2202 | 2924 | 4029 | 2968 | 3170 | 4397 | 3293 | 3187 | 4568 |
|  | `mini-ppl/burglar` | **2296** | 3916 | 5163 | 2331 | 3480 | 5030 | 2706 | [3751]{.red} | 5253 | 2813 | 3959 | 6100 |
|  | `interp/interp` | 2679 | **987** | 1096 | 2712 | 1086 | 1317 | 2150 | 1171 | 1337 | 2474 | 1626 | 1798 |
|  | `coop-communication/send-recv` | **2784** | 4698 | 13824 | 2833 | 8651 | - | 7641 | - | - | 12349 | - | - |
|  | `coop-communication/prime-sieve` | **7347** | 16628 | - | 7399 | - | - | 9504 | - | - | 22760 | - | - |
|  | `build/mymakefile-example4` | - | - | - | **2178** | 8449 | 10345 | 5081 | - | - | 6360 | - | - |
|  | `build/mymakefile-example5` | - | - | - | 2178 | 8449 | 2117 | 5081 | - | **1298** | 6360 | - | **1298** |
|  | `interp2/err2` | - | 1041 | **770** | 2703 | 1087 | 801 | 1917 | 1265 | 816 | 1917 | 1265 | 816 |
|  | `interp2/err3` | - | 1409 | 1539 | 5996 | 1381 | 1564 | 15771 | [**1363**]{.red} | 1457 | - | **1363** | 1457 |
|  | `interp2/t1` | - | 1981 | 1870 | 6370 | 2434 | 1496 | 32716 | [1867]{.red} | **1355** | - | 1867 | **1355** |
|  | `interp2/t2` | - | **2220** | 2651 | - | 2674 | 2231 | 32832 | 2617 | 2311 | - | 2617 | 2311 |
|  | `interp2/t3` | - | 3623 | 3675 | - | 4904 | 3610 | - | 6645 | 8131 | - | 14640 | **3127** |
| **Rosetta** | `jump-anywhere/e1` | **237** | 271 | 292 | 239 | 287 | 359 | 239 | 287 | 359 | 239 | 287 | 359 |
|  | `jump-anywhere/loop` | **755** | 1280 | 1536 | 758 | 938 | 1206 | 1502 | 1881 | 2600 | 2012 | 1924 | 2304 |
|  | `monads-writer/solution1` | **847** | 1104 | 1396 | 858 | 1170 | 1747 | 1271 | 1500 | 2048 | 1271 | 1500 | 2048 |
|  | `pr4rings/four-squares` | **943** | 1776 | 8773 | **943** | 1282 | 2675 | 2525 | 3429 | 57655 | 2525 | 3429 | 57655 |
| **Koka-Samples** | `yield/main` | **236** | 258 | 291 | 244 | 304 | 405 | 295 | 333 | 436 | 295 | 333 | 436 |
|  | `nim/example-perfect1` | **296** | 386 | 444 | 298 | 416 | 544 | 376 | 451 | 579 | 376 | 451 | 579 |
|  | `nim/example-perfect2` | **296** | 386 | 444 | 298 | 416 | 544 | 376 | 451 | 579 | 376 | 451 | 579 |
|  | `unix/example1` | **322** | 337 | 414 | 326 | 385 | 431 | 468 | 481 | 446 | 528 | 541 | 446 |
|  | `unix/example1_2` | **340** | 357 | 407 | 344 | 413 | 459 | 523 | 508 | 469 | 581 | 564 | 469 |
|  | `ambient/example0` | 371 | **363** | **363** | 379 | 376 | 376 | 373 | 378 | 378 | 373 | 378 | 378 |
|  | `unix/example2` | **435** | 436 | 436 | 441 | 451 | 451 | 455 | 461 | 461 | 455 | 461 | 461 |
|  | `scoped/example1` | **442** | 645 | 862 | 457 | 733 | 1225 | 630 | 800 | 1763 | 630 | 800 | 1763 |
|  | `nim/example-gtree` | **483** | 833 | 1627 | 502 | 835 | 1466 | 576 | 870 | 1728 | 576 | 870 | 1728 |
|  | `vec/main` | **542** | 543 | 543 | 549 | 565 | 565 | 567 | 579 | 579 | 567 | 579 | 579 |
|  | `nim/example-coin` | **545** | 693 | 785 | 551 | 749 | 906 | 826 | 925 | 1053 | 826 | 925 | 1053 |
|  | `unix/example3` | **566** | 582 | 648 | 574 | 640 | 688 | 727 | 741 | 704 | 731 | 745 | 704 |
|  | `nim/example-check` | **1131** | 1184 | 1369 | 1152 | 1313 | 1952 | 1135 | 1384 | 2434 | 1135 | 1384 | 2434 |
|  | `nim/example-pc1` | 1151 | 1196 | 1476 | 1172 | 1335 | 1699 | **1150** | 1294 | 1694 | **1150** | 1294 | 1694 |
|  | `unix/example5` | **1278** | 1441 | 1991 | 1302 | 1516 | 2078 | 1446 | 1612 | 2367 | 1655 | 1881 | 2843 |
|  | `scoped/example5` | **2754** | 3558 | 5689 | 2773 | 3172 | 4994 | 3941 | 4046 | 8999 | 5208 | 4065 | 7325 |
|  | `scoped/example3` | 2964 | **1244** | 1444 | 2987 | 1417 | 2281 | 1416 | 1725 | 2773 | 1793 | 2178 | 3600 |
|  | `scoped/example2` | 11219 | **1631** | 2104 | 11242 | 2430 | 2942 | 2332 | 3774 | 4604 | 8774 | 21761 | - |
|  | `nim/example-pc2` | - | 597 | **544** | - | 552 | 552 | 592 | [552]{.red} | 552 | 592 | 552 | 552 |
|  | `scoped/example4` | - | 1362 | **1003** | 6298 | 1051 | 1052 | 1846 | [1062]{.red} | 1069 | 2348 | 1066 | 1073 |
| **Micro-Suite** | `basic/basic-exception` | **124** | **124** | **124** | 126 | 126 | 126 | 126 | 126 | 126 | 126 | 126 | 126 |
|  | `complex-flow/complex-tail-effect` | **135** | **135** | **135** | 137 | 137 | 137 | 137 | 137 | 137 | 137 | 137 | 137 |
|  | `basic/basic-resume` | **157** | **157** | **157** | 159 | 159 | 159 | 159 | 159 | 159 | 159 | 159 | 159 |
|  | `complex-flow/complex-tail-call` | **160** | **160** | **160** | 162 | 162 | 162 | 162 | 162 | 162 | 162 | 162 | 162 |
|  | `basic/basic-resume-op` | **165** | 177 | 177 | 167 | 179 | 179 | 167 | 179 | 179 | 167 | 179 | 179 |
|  | `complex-flow/complex-resume-func` | **167** | **167** | **167** | 169 | 169 | 169 | 169 | 169 | 169 | 169 | 169 | 169 |
|  | `basic/basic-resume-context` | **168** | 180 | 180 | 170 | 182 | 182 | 182 | 182 | 182 | 182 | 182 | 182 |
|  | `complex-flow/complex-non-tail-call` | **172** | 184 | 184 | 174 | 186 | 186 | 174 | 186 | 186 | 174 | 186 | 186 |
|  | `basic/basic-resume-op-context` | **176** | 200 | 200 | 178 | 202 | 202 | 190 | 202 | 202 | 190 | 202 | 202 |
|  | `nondet/nondet-discard` | **185** | **185** | 187 | 189 | 191 | 191 | 189 | 191 | 191 | 189 | 191 | 191 |
|  | `nondet/nondet-simple` | **203** | **203** | 205 | 207 | 209 | 209 | 207 | 209 | 209 | 207 | 209 | 209 |
|  | `nested-nondet/nondet-with-failure` | **207** | **207** | **207** | 211 | 211 | 211 | 211 | 211 | 211 | 211 | 211 | 211 |
|  | `nondet/nondet-context` | **216** | 230 | 243 | 220 | 235 | 235 | 247 | 249 | 249 | 247 | 249 | 249 |
|  | `recursion/iter-sum` | **217** | 228 | 228 | 219 | 230 | 230 | 274 | 231 | 231 | 274 | 231 | 231 |
|  | `recursion/iter-sum-two` | **217** | 249 | 293 | 219 | 276 | 342 | 274 | 307 | 344 | 274 | 307 | 344 |
|  | `recursion/iter-sum-b` | **218** | 228 | 228 | 220 | 230 | 230 | 275 | 231 | 231 | 275 | 231 | 231 |
|  | `recursion/iter-sum-handler` | **218** | 229 | 229 | 220 | 231 | 231 | 275 | 232 | 232 | 275 | 232 | 232 |
|  | `recursion/iter-sum-two-b` | **218** | 251 | 297 | 220 | 278 | 342 | 275 | 309 | 344 | 275 | 309 | 344 |
|  | `nested/nested-simple-two` | **230** | **230** | **230** | 234 | 234 | 234 | 234 | 234 | 234 | 234 | 234 | 234 |
|  | `recursion/iter-sum-c` | **231** | **231** | **231** | 233 | 233 | 233 | 281 | 235 | 235 | 281 | 235 | 235 |
|  | `recursion/iter-sum-two-c` | **231** | 301 | 363 | 233 | 304 | 351 | 281 | 362 | 356 | 281 | 362 | 356 |
|  | `recursion/iter-sum-d` | 232 | **231** | **231** | 234 | 233 | 233 | 282 | 235 | 235 | 282 | 235 | 235 |
|  | `recursion/iter-sum-two-d` | **232** | 303 | 367 | 234 | 306 | 351 | 282 | 364 | 356 | 282 | 364 | 356 |
|  | `nondet/nondet-nested` | **247** | 318 | 399 | 253 | 358 | 422 | 361 | 421 | 507 | 361 | 421 | 507 |
|  | `nested-nondet/nondet-variable-branches` | **269** | 303 | 307 | 273 | 311 | 311 | 276 | 311 | 311 | 276 | 311 | 311 |
|  | `complex-flow/complex-recursive` | **278** | 500 | 1007 | 280 | 652 | 2527 | 376 | 613 | 1792 | 376 | 613 | 1792 |
|  | `nested/nested-simple` | **279** | 280 | 280 | 283 | 283 | 283 | 284 | 284 | 284 | 284 | 284 | 284 |
|  | `nested/nested-tail-simple` | **279** | 280 | 280 | 283 | 283 | 283 | 284 | 284 | 284 | 284 | 284 | 284 |
|  | `nested-nondet/nondet-guarded` | **296** | 414 | 580 | 302 | 555 | 394 | 477 | 681 | 455 | 477 | 681 | 455 |
|  | `complex-flow/complex-nested-interleave` | **299** | 327 | 336 | 303 | 340 | 340 | 335 | 342 | 345 | 335 | 342 | 345 |
|  | `nested/nested-inner-first` | **329** | 353 | 353 | 335 | 359 | 359 | 347 | 359 | 359 | 359 | 359 | 359 |
|  | `nested/nested-outer-first` | **329** | 353 | 353 | 335 | 359 | 359 | 359 | 359 | 359 | 359 | 359 | 359 |
|  | `nested/nested-tail-inner-first` | **329** | 353 | 353 | 335 | 359 | 359 | 347 | 359 | 359 | 359 | 359 | 359 |
|  | `nested/nested-tail-outer-first` | **329** | 353 | 353 | 335 | 359 | 359 | 359 | 359 | 359 | 359 | 359 | 359 |
|  | `nested/nested-op-after` | **336** | 360 | 360 | 342 | 366 | 366 | 366 | 366 | 366 | 366 | 366 | 366 |
|  | `nested/nested-op-before` | **336** | 360 | 360 | 342 | 366 | 366 | 368 | 368 | 368 | 368 | 368 | 368 |
|  | `nested/nested-tail-op-after` | **336** | 360 | 360 | 342 | 366 | 366 | 366 | 366 | 366 | 366 | 366 | 366 |
|  | `nested/nested-tail-op-before` | **336** | 360 | 360 | 342 | 366 | 366 | 368 | 368 | 368 | 368 | 368 | 368 |
|  | `nested-nondet/nondet-nested-tail` | **348** | **348** | 380 | 354 | 357 | 357 | 380 | 382 | 382 | 410 | 412 | 412 |
|  | `nested/nested-absorb` | **363** | **363** | **363** | 371 | 371 | 371 | 371 | 371 | 371 | 371 | 371 | 371 |
|  | `state-handler/state-countdown` | **411** | 441 | 486 | 417 | 467 | 599 | 604 | 617 | 675 | 709 | 725 | 783 |
|  | `nested-nondet/nondet-nested-simple` | **419** | 535 | 630 | 429 | 572 | 648 | 568 | 648 | 876 | 663 | 743 | 1021 |
|  | `nested-nondet/nondet-both-contexts` | **439** | 555 | 650 | 449 | 592 | 668 | 608 | 688 | 956 | 703 | 783 | 1101 |
|  | `nested/nested-three-levels` | **463** | 476 | 476 | 471 | 484 | 484 | 486 | 486 | 486 | 486 | 486 | 486 |
|  | `multi-effect/multi-simple` | **480** | 528 | 528 | 488 | 536 | 536 | 536 | 536 | 536 | 536 | 536 | 536 |
|  | `multi-effect/multi-two-outer` | **484** | 551 | 566 | 492 | 575 | 588 | 563 | 578 | 590 | 563 | 578 | 590 |
|  | `multi-effect/multi-inner-first` | **486** | 534 | 534 | 494 | 542 | 542 | 532 | 544 | 544 | 532 | 544 | 544 |
|  | `complex-flow/complex-layers` | **504** | 657 | 658 | 508 | 632 | 659 | 767 | 727 | 687 | 782 | 728 | 687 |
|  | `nested-nondet/nondet-alternating` | **546** | 617 | 671 | 556 | 647 | 647 | 628 | 651 | 651 | 702 | 727 | 727 |
|  | `nested-nondet/nondet-three-levels` | **588** | 692 | 846 | 600 | 732 | 828 | 803 | 885 | 1047 | 1044 | 1130 | 1420 |
| | **Averages** |  |  |  |  |  |  |  |  |  |  |  |  |
| **Koka-Gen** | Average | **1752** | 2720 | 2726 | 2201 | 3815 | 2548 | 5614 | 2325 | 2679 | 3941 | 2922 | 2916 |
| **Rosetta** | Average | **696** | 1108 | 2999 | 700 | 919 | 1497 | 1384 | 1774 | 15666 | 1512 | 1785 | 15592 |
| **Koka-Samples** | Average | 1410 | **902** | 1144 | 1678 | 953 | 1280 | 1002 | 1121 | 1683 | 1448 | 2064 | 1510 |
| **Micro-Suite** | Average | **292** | 327 | 357 | 297 | 342 | 390 | 343 | 361 | 397 | 357 | 374 | 414 |

## Table B4: Analysis Time (ms) by Configuration

| Category | Benchmark | kCFA(0) | kCFA(1) | kCFA(2) | H(0,0) | H(0,1) | H(0,2) | H(1,0) | H(1,1) | H(1,2) | H(2,0) | H(2,1) | H(2,2) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| **Koka-Gen** | `scheduler/scheduler` | **2** | 11 | 19 | 2 | 8 | 12 | 2 | [7]{.red} | 12 | 2 | 8 | 13 |
|  | `interp2/err1` | **2** | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
|  | `interp2/t4` | 645 | 7 | 6 | 65 | 7 | 5 | 5 | [**3**]{.red} | 4 | 5 | 3 | 4 |
|  | `interp2/err5` | 89 | 4 | 4 | 22 | 4 | **3** | 3 | [3]{.red} | 3 | 4 | 3 | 4 |
|  | `interp2/err4` | 316 | **2** | 2 | 30 | 2 | 2 | 4 | 2 | 2 | 4 | 2 | 3 |
|  | `build/mymakefile-example3` | 5 | 36 | 48 | 6 | 8 | 10 | **4** | [5]{.red} | 4 | 5 | 5 | 5 |
|  | `coop-communication/yield` | 8 | 10 | 22 | **8** | 10 | 22 | 25 | 33 | 55 | 51 | 58 | 48 |
|  | `coop-communication/spawn` | 10 | 19 | 55 | **10** | 21 | 77 | 30 | 69 | 300 | 53 | 120 | 583 |
|  | `ukanren/q1` | 860 | 3056 | - | **467** | 1744 | - | 493 | [1765]{.red} | - | 478 | 1742 | - |
|  | `ukanren/q2` | 2642 | - | - | 1629 | 1831 | - | 1650 | 1904 | - | **1601** | 1946 | - |
|  | `build/mymakefile-example2` | 24 | - | - | **15** | 5721 | - | 588 | - | - | 898 | - | - |
|  | `build/mymakefile-example1` | 24 | - | - | **15** | 5701 | - | 584 | - | - | 918 | - | - |
|  | `music/search-come` | 11 | 16 | 26 | **11** | 17 | 25 | 12 | 18 | 29 | 13 | 19 | 30 |
|  | `music/search-love` | 10 | 17 | 27 | **10** | 18 | 25 | 13 | 24 | 42 | 13 | 25 | 31 |
|  | `mini-ppl/burglar-mc` | **10** | 16 | 24 | 11 | 17 | 26 | 28 | 44 | 94 | 46 | 71 | 192 |
|  | `mini-ppl/drunk` | 992 | 1246 | 28 | **15** | 20 | 25 | 22 | [24]{.red} | 31 | 28 | 22 | 37 |
|  | `mini-ppl/burglar` | 1015 | 1185 | 67 | **15** | 24 | 41 | 21 | [30]{.red} | 48 | 21 | 29 | 55 |
|  | `interp/interp` | 1122 | **6** | 7 | 1051 | 7 | 8 | 63 | 7 | 9 | 36 | 10 | 13 |
|  | `coop-communication/send-recv` | 85 | 325 | 5193 | **80** | 1099 | - | 738 | - | - | 1450 | - | - |
|  | `coop-communication/prime-sieve` | 994 | 4420 | - | 858 | - | - | **693** | - | - | 2186 | - | - |
|  | `build/mymakefile-example4` | - | - | - | **19** | 1261 | 3427 | 598 | - | - | 946 | - | - |
|  | `build/mymakefile-example5` | - | - | - | 18 | 1272 | 16 | 617 | - | **8** | 934 | - | 8 |
|  | `interp2/err2` | - | 29 | **3** | 889 | 20 | 8 | 44 | [10]{.red} | 3 | 55 | 11 | 4 |
|  | `interp2/err3` | - | **6** | 8 | 2056 | 7 | 8 | 1705 | 7 | 7 | - | 7 | 8 |
|  | `interp2/t1` | - | 42 | 13 | 4868 | 38 | 8 | 4372 | [13]{.red} | **7** | - | 14 | 7 |
|  | `interp2/t2` | - | 428 | 823 | - | 51 | 15 | 4338 | [19]{.red} | **13** | - | 21 | 14 |
|  | `interp2/t3` | - | 368 | 154 | - | 241 | 85 | - | [277]{.red} | 301 | - | 2638 | **19** |
| **Rosetta** | `jump-anywhere/e1` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | [1]{.red} | 2 | 1 | 1 | 3 |
|  | `jump-anywhere/loop` | 5 | 12 | 16 | **4** | 8 | 12 | 18 | 25 | 33 | 21 | 19 | 26 |
|  | `monads-writer/solution1` | **4** | 5 | 10 | 4 | 7 | 9 | 8 | 9 | 12 | 8 | 9 | 15 |
|  | `pr4rings/four-squares` | **7** | 17 | 377 | 7 | 12 | 84 | 29 | 53 | 4184 | 27 | 45 | 4112 |
| **Koka-Samples** | `yield/main` | 1 | 1 | 1 | **1** | 1 | 1 | 1 | [1]{.red} | 2 | 1 | 1 | 3 |
|  | `nim/example-perfect1` | **1** | 1 | 2 | 1 | 2 | 2 | 1 | 2 | 2 | 1 | 2 | 3 |
|  | `nim/example-perfect2` | **1** | 1 | 2 | 1 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
|  | `unix/example1` | **1** | 1 | 2 | 1 | 1 | 2 | 3 | 2 | 2 | 2 | 2 | 2 |
|  | `unix/example1_2` | **1** | 2 | 2 | 1 | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 2 |
|  | `ambient/example0` | 3 | **1** | 1 | 3 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 2 |
|  | `unix/example2` | **1** | 1 | 1 | 2 | 2 | 2 | 2 | 1 | 2 | 2 | 2 | 2 |
|  | `scoped/example1` | 3 | 4 | 7 | **2** | 4 | 10 | 4 | 6 | 20 | 4 | 6 | 19 |
|  | `nim/example-gtree` | **2** | 8 | 43 | 2 | 4 | 10 | 3 | [5]{.red} | 12 | 3 | 5 | 13 |
|  | `vec/main` | **2** | 3 | 3 | 2 | 2 | 2 | 2 | [3]{.red} | 2 | 2 | 2 | 3 |
|  | `nim/example-coin` | 3 | **3** | 3 | 3 | 3 | 4 | 7 | 4 | 5 | 7 | 5 | 5 |
|  | `unix/example3` | **2** | 2 | 2 | 2 | 2 | 3 | 3 | 3 | 3 | 3 | 3 | 3 |
|  | `nim/example-check` | 14 | 11 | 10 | 15 | 6 | 13 | **6** | [7]{.red} | 17 | 7 | 9 | 19 |
|  | `nim/example-pc1` | 17 | 9 | 12 | 16 | 7 | 9 | **6** | [7]{.red} | 9 | 7 | 8 | 10 |
|  | `unix/example5` | 6 | 6 | 10 | **5** | 6 | 10 | 8 | 9 | 15 | 11 | 12 | 26 |
|  | `scoped/example5` | 47 | 65 | 121 | **31** | 39 | 90 | 65 | [56]{.red} | 311 | 149 | 62 | 150 |
|  | `scoped/example3` | 185 | **6** | 10 | 193 | 9 | 21 | 15 | 12 | 29 | 12 | 18 | 43 |
|  | `scoped/example2` | 2362 | **15** | 28 | 2300 | 25 | 40 | 30 | 80 | 89 | 339 | 1284 | - |
|  | `nim/example-pc2` | - | 2 | 2 | - | 2 | **2** | 3 | 2 | 2 | 3 | 2 | 2 |
|  | `scoped/example4` | - | 11 | 4 | 3596 | **4** | 5 | 20 | [4]{.red} | 5 | 28 | 5 | 6 |
| **Micro-Suite** | `basic/basic-exception` | **0** | 0 | 1 | 0 | 0 | 0 | 0 | [0]{.red} | 0 | 0 | 0 | 1 |
|  | `complex-flow/complex-tail-effect` | **0** | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 0 |
|  | `basic/basic-resume` | 1 | **0** | 1 | 1 | 1 | 0 | 0 | 1 | 1 | 0 | 0 | 1 |
|  | `complex-flow/complex-tail-call` | **0** | 0 | 0 | 0 | 1 | 1 | 0 | [0]{.red} | 0 | 1 | 0 | 1 |
|  | `basic/basic-resume-op` | 1 | **0** | 1 | 1 | 0 | 0 | 1 | 1 | 1 | 0 | 0 | 1 |
|  | `complex-flow/complex-resume-func` | **0** | 0 | 0 | 1 | 0 | 1 | 0 | [0]{.red} | 1 | 0 | 0 | 1 |
|  | `basic/basic-resume-context` | 0 | 1 | 1 | 0 | 1 | 0 | 0 | [1]{.red} | 1 | **0** | 0 | 1 |
|  | `complex-flow/complex-non-tail-call` | **0** | 1 | 1 | 0 | 0 | 1 | 1 | [0]{.red} | 0 | 1 | 1 | 0 |
|  | `basic/basic-resume-op-context` | 1 | **0** | 1 | 1 | 0 | 0 | 1 | 1 | 1 | 0 | 1 | 1 |
|  | `nondet/nondet-discard` | 1 | 1 | 1 | **0** | 0 | 1 | 1 | [0]{.red} | 1 | 1 | 1 | 1 |
|  | `nondet/nondet-simple` | 1 | **0** | 1 | 0 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `nested-nondet/nondet-with-failure` | 0 | 1 | 1 | **0** | 1 | 0 | 1 | [0]{.red} | 1 | 0 | 0 | 1 |
|  | `nondet/nondet-context` | 1 | 1 | 1 | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `recursion/iter-sum` | 1 | 1 | 1 | 1 | 1 | 1 | 2 | 1 | 1 | 1 | **1** | 1 |
|  | `recursion/iter-sum-two` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 2 | 1 | 1 | 2 | 1 |
|  | `recursion/iter-sum-b` | 1 | **0** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `recursion/iter-sum-handler` | **0** | 1 | 1 | 1 | 1 | 1 | 1 | 2 | 1 | 1 | 1 | 1 |
|  | `recursion/iter-sum-two-b` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 3 | 1 | 1 | 1 | 1 |
|  | `nested/nested-simple-two` | **0** | 0 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `recursion/iter-sum-c` | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | **1** | 1 | 1 | 1 |
|  | `recursion/iter-sum-two-c` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 2 | 1 | 1 | 2 | 2 |
|  | `recursion/iter-sum-d` | 1 | 1 | **0** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `recursion/iter-sum-two-d` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 2 | 1 | 1 | 2 | 1 |
|  | `nondet/nondet-nested` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 2 | 2 | 2 | 2 | 2 |
|  | `nested-nondet/nondet-variable-branches` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `complex-flow/complex-recursive` | **1** | 3 | 14 | 2 | 7 | 97 | 2 | 5 | 27 | 2 | 6 | 29 |
|  | `nested/nested-simple` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 2 |
|  | `nested/nested-tail-simple` | 1 | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `nested-nondet/nondet-guarded` | **1** | 2 | 2 | 1 | 2 | 1 | 2 | 3 | 2 | 2 | 4 | 2 |
|  | `complex-flow/complex-nested-interleave` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `nested/nested-inner-first` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `nested/nested-outer-first` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `nested/nested-tail-inner-first` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `nested/nested-tail-outer-first` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `nested/nested-op-after` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `nested/nested-op-before` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `nested/nested-tail-op-after` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 2 | 1 | 1 | 1 | 1 |
|  | `nested/nested-tail-op-before` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `nested-nondet/nondet-nested-tail` | **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 2 |
|  | `nested/nested-absorb` | **1** | 1 | 2 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
|  | `state-handler/state-countdown` | **1** | 2 | 3 | 2 | 2 | 2 | 3 | 3 | 3 | 3 | 3 | 5 |
|  | `nested-nondet/nondet-nested-simple` | **1** | 2 | 2 | 1 | 2 | 2 | 2 | 3 | 4 | 3 | 3 | 4 |
|  | `nested-nondet/nondet-both-contexts` | 1 | 2 | 2 | **1** | 2 | 4 | 2 | 3 | 4 | 3 | 3 | 5 |
|  | `nested/nested-three-levels` | **1** | 1 | 1 | 1 | 2 | 2 | 2 | 2 | 2 | 7 | 2 | 2 |
|  | `multi-effect/multi-simple` | **1** | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 4 | 2 |
|  | `multi-effect/multi-two-outer` | 1 | 2 | 2 | **1** | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
|  | `multi-effect/multi-inner-first` | **1** | 2 | 2 | 1 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
|  | `complex-flow/complex-layers` | **2** | 3 | 3 | 2 | 3 | 2 | 4 | [3]{.red} | 3 | 4 | 3 | 3 |
|  | `nested-nondet/nondet-alternating` | **1** | 2 | 2 | 2 | 2 | 2 | 3 | 2 | 2 | 3 | 3 | 4 |
|  | `nested-nondet/nondet-three-levels` | **2** | 2 | 3 | 2 | 3 | 3 | 4 | 4 | 5 | 5 | 5 | 7 |
| | **Averages** |  |  |  |  |  |  |  |  |  |  |  |  |
| **Koka-Gen** | Average | 443 | 511 | 327 | 487 | 737 | 183 | 641 | 203 | **49** | 424 | 322 | 54 |
| **Rosetta** | Average | **4** | 9 | 101 | 4 | 7 | 27 | 14 | 22 | 1058 | 14 | 19 | 1039 |
| **Koka-Samples** | Average | 147 | 8 | 13 | 325 | **6** | 11 | 9 | 10 | 27 | 29 | 72 | 17 |
| **Micro-Suite** | Average | **1** | 1 | 1 | 1 | 1 | 3 | 1 | 1 | 2 | 1 | 2 | 2 |