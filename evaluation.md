
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
*   **Structural Precision:** 1,2-HMCFAR achieves the highest average improvement (**6.8%**), outperforming 1-kCFA (**5.8%**) and matching 2-kCFA (**6.7%**).
*   **Continuation Precision:** 1,2-HMCFAR demonstrates a massive advantage with **32.3%** average improvement compared to 1-kCFA (**23.4%**), confirming its superior handling of complex control-flow.

**Discussion:** The new data confirms that HMCFAR (specifically with $m \ge 1$) provides robust improvement across the benchmark suite. The ability to distinguish return contexts allows HMCFAR to achieve significantly higher continuation precision, resolving control-flow ambiguities that k-CFA conflates.

## 2. Expert Trade-off Analysis: Linear vs. Branched History

For analysis experts, we compare k-CFA (linear history) and HMCFAR (branched history) across two dimensions: State Space and Analysis Time.

### Cost-Precision Trade-off (States)

![Cost-Precision Tradeoff](benchmarks/new_analysis/plot_expert_tradeoff.png)

Figure 2 illustrates the trade-off between state space size and precision. Detailed cost/benefit analysis is encoded in the colors:
*   **Green lines (Win-Win):** HMCFAR improves precision **AND** reduces state space.
*   **Blue lines (Trade-off):** HMCFAR improves precision but explores more states.
*   **Red lines (Regression):** HMCFAR has worse precision.

We see that for many benchmarks, HMCFAR achieves higher precision (Green/Blue lines). In cases like `complex-layers` (Blue), this precision comes at a moderate increase in state space size.

### Time-Precision Trade-off (Time)

![Time-Precision Tradeoff](benchmarks/new_analysis/plot_expert_time_tradeoff.png)

Figure 3 shows the trade-off in terms of analysis time.
*   **Green lines (Win-Win):** HMCFAR improves precision **AND** reduces analysis time.
*   **Blue lines (Trade-off):** HMCFAR improves precision but takes longer.
*   **Red lines (Regression):** HMCFAR has worse precision.

This view confirms that HMCFAR often pays a time cost for its precision (Blue lines), but in some cases (Green lines), the precision trade-off yields performance benefits due to smaller state spaces or faster convergence.

This view confirms that HMCFAR often pays a time cost for its precision (green lines often show increased time), but in some cases (blue lines), the precision trade-off yields performance benefits.

Finally, we explore the design space of our HMCFAR analysis by varying the call sensitivity ($m$) while fixing handler sensitivity ($h$).

![HMCFA Parameter Sweep](benchmarks/new_analysis/plot_dmcfa_sweep_line.png)

Figure 4 presents the median precision as we increase $m$.
*   **Impact of $m$:** Increasing call sensitivity ($m$) provides substantial gains up to $m=1$, resolving many ambiguities.
*   **Diminishing Returns:** Beyond $m=1$, precision plateaus for most benchmarks.
*   **Role of $h$:** Comparing the lines for $h=0, 1, 2$, we see that having at least $h=1$ provides a consistent improvement over $h=0$, but $h=2$ adds little value. This confirms that $(1,1)$ is the optimal trade-off.

## Threats to Validity

*   **Benchmark Selection:** Our "complex" filter may bias results, but it focuses the evaluation on the cases where analysis choice actually matters.
*   **Baseline Tuning:** We compare against 1-kCFA. Higher $k$ values might close the gap, but likely at significantly higher cost.

