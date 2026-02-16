
# Evaluation {#evaluation}

We evaluate our analysis along two dimensions: precision and scalability.
Specifically, we structure our evaluation to answer three key questions:
1.  **High-Level Efficacy:** Does our approach solve complex benchmarks that standard baselines cannot?
2.  **Trade-off Analysis:** How does our branched history approach (HMCFA) compare to traditional linear history (k-CFA) in terms of cost and precision?
3.  **Parameter Sensitivity:** How do the call ($m$) and handler ($h$) sensitivity parameters impact analysis performance?

## 1. High-Level Efficacy

To assess the practical value of our approach, we compare our $(h,m)$-CFA with Rebinding (HMCFAR) against a flow-insensitive baseline (0-CFA) and context-sensitive baselines (1-kCFA, 2-kCFA).
We focus our comparison on "complex" benchmarks where the 0-CFA baseline fails to achieve perfect precision (< 99%), filtering out trivial cases.

Figure 1 shows the **Productivity** (Average Relative Improvement over 0-CFA) for these simple-to-complex benchmarks.
*   **Value Precision:** 1,2-HMCFAR achieves the highest average improvement (**6.9%**), outperforming 1-kCFA (**5.8%**) and 2-kCFA (**6.7%**).
*   **Continuation Precision:** 1,2-HMCFAR demonstrates a massive advantage with **32.3%** average improvement compared to 1-kCFA (**23.4%**).

**Discussion:** The new data confirms that HMCFAR (specifically with $m \ge 1$) provides robust improvement across the benchmark suite.

### Part 2: Absolute Precision (Median)
While productivity shows relative gains, absolute precision reveals typical performance.

![Median Absolut![High Level Productivity (Mean)](plot_high_level_productivity_mean.png)_median.png)

Figure 2 shows the **Median Absolute Precision** across complex benchmarks.
*   **Continuation Precision:** 1,2-HMCFAR achieves a perfect **100% median precision**, solving the majority of benchmarks completely. In contrast, 1-kCFA achieves only **85%**, and 0-CFA drops to **69%**.
*   **Value Precision:** HMCFAR also leads in value precision with **91%**, compared to **87%** for 1-kCFA.

### Part 3: Expert Trade-off Analysis: Linear vs. Branched History

For analysis experts, we compare k-CFA (linear history) and HMCFAR (branched history) across two dimensions: State Space and Analysis Time.

### Cost-Precision Trade-off (States)

![Cost-Precision Tradeoff](/Users/timwhiting/.gemini/antigravity/brain/d0bb3d21-7a53-4240-a516-b7fbe1ad3c16/plot_expert_tradeoff_productivity.png)

Figure 2 illustrates the trade-off between state space size and precision. Detailed cost/benefit analysis is encoded in the colors:
*   **Green (Win-Win):** HMCFAR improves precision **AND** reduces state space.
*   **Blue (Trade-off):** HMCFAR improves precision but explores more states.
*   **Red (Regression):** HMCFAR has worse precision.

We see that for many benchmarks, HMCFAR achieves higher precision (Green/Blue lines). In cases like `complex-layers` (Blue), this precision comes at a moderate increase in state space size.

### Time-Precision Trade-off (Time)

![Time-Precision Tradeoff](/Users/timwhiting/.gemini/antigravity/brain/d0bb3d21-7a53-4240-a516-b7fbe1ad3c16/plot_expert_time_productivity.png)

Figure 3 shows the trade-off in terms of analysis time.
*   **Green (Win-Win):** HMCFAR improves precision **AND** reduces analysis time.
*   **Blue (Trade-off):** HMCFAR improves precision but takes longer.
*   **Red (Regression):** HMCFAR has worse precision.

This view confirms that HMCFAR often pays a time cost for its precision (Blue lines), but in some cases (Green lines), the precision trade-off yields performance benefits.

### Part 3: Parameter Sensitivity

Finally, we explore the design space of our HMCFAR analysis by varying the call sensitivity ($m$) while fixing handler sensitivity ($h$). We plot four metric variations using the **Geometric Mean** across complex benchmarks.

#### Continuation Precision (Improvement & Real)
![Continuation Improvement](/Users/timwhiting/.gemini/antigravity/brain/d0bb3d21-7a53-4240-a516-b7fbe1ad3c16/plot_dmcfa_sweep_cont_productivity.png)
![Continuation Real](/Users/timwhiting/.gemini/antigravity/brain/d0bb3d21-7a53-4240-a516-b7fbe1ad3c16/plot_dmcfa_sweep_cont_real.png)

#### Value Precision (Improvement & Real)
![Value Improvement](/Users/timwhiting/.gemini/antigravity/brain/d0bb3d21-7a53-4240-a516-b7fbe1ad3c16/plot_dmcfa_sweep_val_productivity.png)
![Value Real](/Users/timwhiting/.gemini/antigravity/brain/d0bb3d21-7a53-4240-a516-b7fbe1ad3c16/plot_dmcfa_sweep_val_real.png)

*   **Impact of $m$:** Increasing call sensitivity ($m$) consistently improves both Continuation and Value precision, with diminishing returns after $m=1$.
*   **Role of $h$:** Detailed breakdown shows $h=1$ provides significant lift over $h=0$, confirming the benefit of handler sensitivity.

## Threats to Validity

*   **Benchmark Selection:** Our "complex" filter may bias results, but it focuses the evaluation on the cases where analysis choice actually matters.
*   **Baseline Tuning:** We compare against 1-kCFA. Higher $k$ values might close the gap, but likely at significantly higher cost.

