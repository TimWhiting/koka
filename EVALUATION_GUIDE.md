# Evaluation Guide: Handler-Sensitive CFA Analysis

This guide documents the methodology, metrics, and key results for the evaluation of `1,1-HMCFAR` vs `k-CFA`.

## 1. Methodology & Metrics

We evaluate precision using two primary approaches: **Absolute Precision** (how resolved is the program?) and **Relative Imprecision Recovery (RIR)** (how much ambiguity did we remove compared to the baseline?).

### A. Metrics

1.  **Absolute Continuation Precision**:
    *   Fraction of call sites with a **singleton** continuation (i.e., a single known jump target).
    *   Goal: 100%.
2.  **Absolute Value Precision**:
    *   Fraction of variables resolving to a **singleton** value or **optimized away** (dead code).
3.  **Relative Imprecision Recovery (RIR)**:
    *   Measures improvement relative to the *baseline's imprecision*.
    *   Formula: $RIR = \frac{\text{Prec}_{new} - \text{Prec}_{base}}{N_{imprecise\_base}}$
    *   **Strict RIR**: The denominator is strictly the count of imprecise items in the baseline (0-CFA). This prevents inflating scores by including simple, already-solved terms.
4.  **Shifted Geometric Mean**:
    *   Used to aggregate RIR across benchmarks.
    *   Formula: $\exp\left(\frac{1}{N} \sum \ln(1 + x)\right) - 1$
    *   Handles $0\%$ improvement values correctly without zeroing out the entire average.

### B. Benchmark Filtering

To provide a fair and meaningful analysis, we filter benchmarks for specific summary tables:

*   **Full Suite (N=101)**: Used for category-based breakdowns (Micro, Koka-Gen, etc.) to show breadth.
*   **Complex Subset (N=58)**:
    *   **Criteria**: Baseline (0-CFA) State Count > 300.
    *   **Reasoning**: Small benchmarks are often trivial or fully solved by 0-CFA. This filter isolates "hard" problems where advanced analysis is actually needed.
    *   **Usage**: The "Summary of Precision" table and Shifted Geomean statistics use this subset.

---

## 2. Key Results Summary

### A. Precision (N=58 Complex Benchmarks)

We compare `1,1-HMCFAR` against `1-kCFA`.

| Metric | 1-kCFA Shifted Geomean | 1,1-HMCFAR Shifted Geomean | Notes |
| :--- | :--- | :--- | :--- |
| **Continuation RIR** | 12.6% | **25.1%** | HMCFAR **doubles** the effectiveness in resolving control flow ambiguity. |
| **Value RIR** | 17.0% | **19.5%** | HMCFAR provides a consistent edge in data flow precision as well. |

### B. The "Koka-Gen" Gap

On the hardest category, **Koka-Gen** (large generated programs), the difference is most pronounced:
*   **1-kCFA** Absolute Continuation Precision: **75.3%**
*   **1,1-HMCFAR** Absolute Continuation Precision: **87.6%**
*   **Impact**:Resolves nearly **half** of the control-flow ambiguity that `1-kCFA` fails to handle.

### C. Cost & Scalability

*   **State Space**: `1,1-HMCFAR` visits **1.06x** more states than `1-kCFA` (Median).
*   **Efficiency**: On Koka-Gen, the cost factor is only **1.12x**, indicating highly efficient analysis of complex structures. The precision gain pays for itself by pruning spurious paths.

---

## 3. Visualizations

The evaluation generates several plots in `benchmarks/new_analysis/`:

1.  **High-Level Metric (Bar/Scatter)**: Shows average precision across categories.
2.  **Expert Trade-off (Scatter)**:
    *   **X-Axis**: Cost (Time or States).
    *   **Y-Axis**: Relative Improvement (RIR).
    *   **Interpretation**: Points in the top-left (high gain, low cost) are ideal. HMCFAR dominates the upper (high precision) region.
3.  **Pareto Frontier (Line)**:
    *   Shows the trade-off curve for specific benchmarks as we vary parameters ($m=0,1,2$).
4.  **Parameter Sweep (Heatmap/Panel)**:
    *   Demonstrates that $H=1$ (Handler Sensitivity) is the "sweet spot" for precision key.

## 4. Reproducing Results

To run the full analysis and generate all tables/plots:

```bash
python benchmarks/new_analysis.py
```

This script will:
1.  Load cached analysis results.
2.  Apply the filters (N=58).
3.  Compute Strict RIR and Shifted Geomeans.
4.  Output CSV tables and PNG plots to `benchmarks/new_analysis/`.
