# Koka Effect Handler Analysis

This document serves as the single source of truth for the Koka effect handler analysis suite, covering usage, methodology, and key findings.

## Pipeline & Usage

Run scripts in order to regenerate the full dataset and reports:

1.  **Collect Data**: `python3 analyze-suite-results.py`
    *   Aggregates CSVs from `benchmarks/results/suite/` into `suite-analysis.json`.
2.  **Generate Reports**: 
    *   `python3 analyze-suite-details.py`: Complexity and anomaly detection.
    *   `python3 export-suite-reports.py`: Generates `PERFORMANCE_REPORT.md` and CSV summaries.
    *   `python3 generate-sensitivity-reports.py`: Generates text-based sensitivity reports.
3.  **Generate Graphs**: (Requires `matplotlib`)
    *   `python3 generate-comparison-graphs.py`: Cost vs. Parameter trends.
    *   `python3 visualize-parameter-correlation.py`: Precision vs. Parameter correlation.

## Key Metrics & Parameters

*   **D (Demand Level)**: Depth of demand-driven analysis. Usually 0-4. Minimal precision impact; moderate performance impact.
*   **M(K) / K**: Context sensitivity depth. Major performance impact; critical for precision in complex handlers.
*   **Precision (0.0 - 1.0)**: Degree of flow-analysis accuracy (1.0 = perfect).


## Analyzer Comparison

*   **DMCFA**: Fast, reliable for most patterns.
*   **DMCFAE**: Exponential variant. Slower.
*   **KCFA**: k-Context-sensitive CFA. (Not a focus right now, ignore this)

## Generated Artifacts Index

Reports are generated in `benchmarks/analysis/`:
*   `exports/PERFORMANCE_REPORT.md`: Primary human-readable summary.
*   `exports/parameter_tuning_guide.txt`: Actionable recommendations for $D$ and $M(K)$.
*   `exports/*_sensitivity_report.txt`: Specific drill-downs for $D$ and $M(K)$.
*   `graphs/*.png`: Visual correlation plots per benchmark.
