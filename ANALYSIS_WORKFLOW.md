# Benchmark Analysis & Visualization Workflow

## Overview

This workflow analyzes benchmark results focusing on **precision**, **proxy metrics**, and **cost (execution time)**. It generates visualizations to understand how the DMCFA analysis performs across different benchmarks and parameters.

## Prerequisites

- Python 3 with matplotlib installed in `.venv`
- Benchmark results in `benchmarks/results/` directory
- LOC analysis from `analysis/loc-analysis.kk`

## Workflow Steps

### 1. Activate Python Environment

```bash
source .venv/bin/activate
```

### 2. Run LOC Analysis (Koka)

Generate the LOC report for all analyze-* functions:

```bash
stack run koka -- analysis/loc-analysis.kk
# or run the compiled binary:
./.koka/v3.2.3/clang-debug-1e5359/analysis_loc_dash_analysis__main
```

This produces a sorted list of all analyze functions with their total LOC costs.

### 3. Analyze Benchmark Results (Python)

Run the analysis script to aggregate benchmark data:

```bash
python3 analyze-benchmarks.py
```

**What it does:**
- Loads all CSV results from `benchmarks/results/D/M/category/benchmark.csv`
- Computes statistics (mean, median, stdev) for:
  - Precision (actual precision percentage)
  - Execution time
  - Proxy metrics (1/AvgS, representing precision estimate)
  - AvgK and AvgS values
- Analyzes parameter sensitivity (how metrics change with D parameter)
- Saves summary to `benchmarks/analysis/benchmark-summary.json`

**Output:**
- Quick overview showing benchmarks by category
- List of benchmarks with < 100% precision

### 4. Generate Visualizations (Python)

Run the visualization script:

```bash
python3 visualize-benchmarks.py
```

**Generated Graphs** (saved to `benchmarks/analysis/graphs/`):

1. **`precision_vs_cost.png`**
   - Scatter plot: Precision vs Execution Time
   - Separate subplots for DMCFA and DMCFA-Exp
   - Color-coded by category (suite, handlers, koka-gen, rosetta)
   - *Purpose: Identify if higher precision comes with higher cost*

2. **`proxy_precision_correlation.png`**
   - Scatter plot: Proxy Precision (1/AvgS) vs Actual Precision
   - Shows how well the proxy metric predicts actual precision
   - Includes diagonal line for perfect correlation
   - *Purpose: Validate that AvgS is a good precision estimator*

3. **`parameter_sensitivity.png`**
   - Multi-panel plot showing 6 representative benchmarks
   - Dual-axis: Time (blue) and Precision (red) vs D parameter
   - *Purpose: Understand how increasing D affects cost/precision tradeoff*

4. **`cost_distribution.png`**
   - Box plots showing execution time distribution by category
   - Separate for DMCFA and DMCFA-Exp
   - *Purpose: Compare cost characteristics across benchmark categories*

5. **`precision_distribution.png`**
   - Histogram of precision values across all benchmarks
   - Bins: 0-50%, 50-70%, 70-80%, 80-90%, 90-95%, 95-99%, 99-100%
   - 100% precision bin highlighted in green
   - *Purpose: Show overall precision characteristics of the analysis*

## Key Metrics Explained

### Actual Metrics
- **Precision**: Percentage of examples that are analyzed precisely (0.0 to 1.0)
- **Time**: Average execution time in seconds across 3 runs
- **NEval**: Number of eval operations
- **NApply**: Number of apply operations

### Proxy Metrics
- **AvgS**: Average store size (lower = more precise)
- **AvgK**: Average continuation size
- **AvgMK**: Average M(K) value
- **Proxy Precision** = 1/AvgS (higher = more precise)

### Parameters
- **D**: Depth parameter (context sensitivity)
- **M(K)**: Memo parameter (how many continuations to track)

## Common Analysis Tasks

### Check precision issues
```bash
python3 analyze-benchmarks.py | grep "< 100%"
```

### Re-generate specific graph
Edit `visualize-benchmarks.py` and comment out unwanted plots in `main()`.

### Compare categories
Look at `cost_distribution.png` to see which categories are more expensive.

### Identify outliers
Check `precision_vs_cost.png` for benchmarks with unusual cost/precision ratios.

## Data Structure

```
benchmarks/
├── results/           # Raw CSV files organized by D/M parameters
│   └── {D}/
│       └── {M}/
│           ├── suite/
│           ├── handlers/
│           ├── koka-gen/
│           └── rosetta/
└── analysis/          # Generated analysis files
    ├── benchmark-summary.json    # Aggregated statistics
    └── graphs/                   # PNG visualizations
```

## Troubleshooting

### No results found
- Check that `benchmarks/results/` exists and contains CSV files
- Verify CSV files have the expected format with headers: `Analysis,File/Example,D,M(K),Precise,Time1,Time2,Time3,...`

### Missing matplotlib
```bash
source .venv/bin/activate
pip install matplotlib numpy
```

### Graphs look wrong
- Check for data quality issues in CSV files
- Verify that Time1, Time2, Time3 columns have numeric values
- Look for outliers that may skew the scales

## Future Enhancements

Potential additions:
- Integrate LOC data into scatter plots (bubble size = LOC)
- Add interactive HTML reports with Plotly
- Correlation analysis: LOC vs Time, LOC vs Precision
- Efficiency metric: Time per LOC ratio
- Identify optimization targets based on high LOC + low precision
