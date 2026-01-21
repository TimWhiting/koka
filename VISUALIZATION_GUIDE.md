# Benchmark Visualization Guide

## Overview
This guide explains the simplified visualization workflow for analyzing DMCFA benchmark results, focusing on precision, proxy metrics, and cost analysis.

## Generated Visualizations

Every precision-based visualization has a **Proxy** variant using the $1/AvgS$ metric.

### 1. Precision vs Cost (`precision_vs_cost.png` / `proxy_vs_cost.png`)
Scatter plot showing the relationship between analysis time (cost) and precision for each benchmark, color-coded by category (handlers, koka-gen, rosetta, suite). 

**Key insights:**
- Benchmarks in the top-left are ideal (high precision, low cost)
- **Proxy variant**: Compares how predictable the proxy is relative to computational cost.

### 2. Parameter Sensitivity (`precision_parameter_sensitivity.png` / `proxy_parameter_sensitivity.png`)
Six-panel grid showing how D parameter affects Time and Precision. Note the X-axis break for D=20 and D=100 to maintain readability.

**Key insights:**
- Shows whether increasing D improves precision (diminishing returns?)
- Time vs D shows computational cost scaling
- **Proxy variant**: Shows if the proxy metric follows the same trend as actual precision across D values.

### 3. Cost Distribution (`cost_distribution.png`)
Box plots showing time distribution for each category.

### 4. Precision by Sensitivity (`precision_by_sensitivity.png` / `proxy_by_sensitivity.png`)
Grouped bar chart showing the distribution of precision across different D values.

**Key insights:**
- Shows how the "quality curve" shifts as D increases
- **Proxy variant**: Useful for seeing if the proxy metric is uniformly distributed across sensitivities.

### 5. M across D Comparison (`precision_m_across_d_comparison.png` / `proxy_m_across_d_comparison.png`)
Line graphs showing precision for different M values across D parameters. DMCFA is shown in blue, DMCFAE in orange. Different line dashes represent different M values.

**Key insights:**
- Compare DMCFA vs DMCFAE directly for the same parameters
- **Proxy variant**: Helps identify if DMCFAE's benefits are reflected in the abstract state depth (AvgS).

## Quick Start

1. **Activate Python environment:**
   ```bash
   source .venv/bin/activate
   ```

2. **Run analysis:**
   ```bash
   python3 analyze-benchmarks.py
   ```
   
   This loads all CSV files from `benchmarks/results/D/M/category/benchmark.csv`, computes statistics, and saves `benchmarks/analysis/benchmark-summary.json`.

3. **Generate visualizations:**
   ```bash
   python3 visualize-benchmarks.py
   ```
   
   This reads the JSON summary and generates 5 PNG files in `benchmarks/analysis/graphs/`.

4. **View results:**
   - Open PNG files directly
   - Or use: `open benchmarks/analysis/graphs/*.png` (macOS)

## Data Flow

```
CSV Results (benchmarks/results/)
    ↓
analyze-benchmarks.py
    ↓
JSON Summary (benchmarks/analysis/benchmark-summary.json)
    ↓
visualize-benchmarks.py
    ↓
PNG Graphs (benchmarks/analysis/graphs/)
```

## Key Metrics

- **Precision**: Percentage of context-sensitive calls that are precisely analyzed (0-1)
- **Time**: Wall-clock time in seconds for analysis to complete
- **Proxy (1/AvgS)**: Quick precision estimate based on average stack depth
- **AvgS**: Average stack depth in abstract domain
- **AvgK**: Average continuation depth
- **D Parameter**: Depth bound for context sensitivity (0, 1, 2, 3, 20, 100)
- **M Parameter**: Merge strategy parameter

## Common Tasks

### Finding Optimization Targets
Look at `precision_vs_cost.png` for benchmarks with:
- High cost (>1s) but low precision (<50%)
- These are candidates for optimization or parameter tuning

### Validating Proxy Metric
Check `proxy_precision_correlation.png`:
- Strong correlation (R² > 0.7) means proxy is reliable
- Weak correlation means you need actual precision measurements

### Understanding D Parameter Effects
Review `parameter_sensitivity.png`:
- If precision plateaus at D=2, no need to run D=20 or D=100
- If time grows exponentially, consider capping D parameter

### Category Comparison
Use `cost_distribution.png` to compare:
- Which categories are fastest (handlers? suite?)
- Which have highest variance (unpredictable performance)

## Integration with LOC Analysis

To correlate LOC with performance:

1. **Run LOC analysis:**
   ```bash
   cd analysis
   koka loc-analysis.kk > ../benchmarks/analysis/loc-report.txt
   ```

2. **Future enhancement:** Modify `analyze-benchmarks.py` to:
   - Parse `loc-report.txt`
   - Add LOC data to JSON summary
   - Create bubble plots with LOC as bubble size

3. **Efficiency metrics to compute:**
   - Time per LOC (computational cost per code size)
   - Precision per LOC (analysis quality relative to code size)
   - Identify high-LOC benchmarks with low precision (optimization targets)

## Troubleshooting

### "No such file or directory" errors
- Ensure you're in the koka root directory
- Check that `benchmarks/results/` exists with CSV files
- Run benchmarks first if results are missing

### "timeout" warnings
- Normal - some benchmarks don't complete within time limit
- These are skipped in statistics calculations
- No action needed unless all benchmarks timeout

### Empty graphs
- Check that CSV files have valid data (not all timeouts)
- Verify JSON summary has non-empty benchmark entries
- Inspect CSV structure matches expected format

### Matplotlib deprecation warnings
- These are informational, graphs still generate correctly
- Update to latest matplotlib if desired: `pip install --upgrade matplotlib`

## Future Enhancements

1. **Interactive visualizations**: Use Plotly for zoom/hover capabilities
2. **LOC integration**: Add code size as a dimension in scatter plots
3. **Efficiency scoring**: Combine precision, time, and LOC into single metric
4. **Time series**: Track how precision/cost changes across git commits
5. **Parameter recommendations**: Suggest optimal D/M for each benchmark
6. **Comparative analysis**: Compare DMCFA vs other analysis types (if needed)

## File Locations

- Python scripts: `analyze-benchmarks.py`, `visualize-benchmarks.py`
- Workflow doc: `ANALYSIS_WORKFLOW.md`
- CSV results: `benchmarks/results/D/M/category/benchmark.csv`
- JSON summary: `benchmarks/analysis/benchmark-summary.json`
- Output graphs: `benchmarks/analysis/graphs/*.png`
- LOC analysis: `analysis/loc-analysis.kk`, `analysis/graph-data.kk`
