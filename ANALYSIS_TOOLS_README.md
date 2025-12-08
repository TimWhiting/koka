# Benchmark Suite Analysis Tools

This directory contains Python scripts for analyzing and reporting on the Koka benchmark suite results.

## Scripts

### 1. `analyze-suite-results.py`
Main analysis script that aggregates and summarizes benchmark results.

**Features:**
- Loads CSV results from `benchmarks/results/suite/`
- Treats **D** (demand-level) and **M(K)** (continuation approximation) as independent variables
- Computes statistics (min, max, mean, median, stdev) for each metric
- Generates trends across sensitivity parameters
- Outputs both human-readable summary and JSON data

**Usage:**
```bash
python3 analyze-suite-results.py
```

**Output:**
- Console summary with sensitivity parameter trends
- `benchmarks/analysis/suite-analysis.json` - Full analysis data in JSON format

### 2. `analyze-suite-details.py`
Provides detailed analysis and insights from the benchmark results.

**Features:**
- Complexity trend analysis
- Time distribution categorization (fast/normal/slow)
- Anomaly detection for outlier results
- Precision analysis to identify problematic benchmarks
- Comparison tables

**Usage:**
```bash
python3 analyze-suite-details.py
```

### 3. `export-suite-reports.py`
Generates various report formats for documentation and comparison.

**Features:**
- CSV export of summary statistics
- Per-analysis-type CSV files
- Markdown performance report with detailed benchmark breakdowns
- HTML comparison table

**Usage:**
```bash
python3 export-suite-reports.py
```

**Output:**
- `benchmarks/analysis/exports/benchmark-summary.csv` - Overall summary
- `benchmarks/analysis/exports/benchmark-summary-*.csv` - Per-analysis summaries
- `benchmarks/analysis/exports/PERFORMANCE_REPORT.md` - Markdown report
- `benchmarks/analysis/exports/benchmark-comparison.html` - HTML visualization

## Key Metrics

### Sensitivity Parameters
- **D**: Demand-level sensitivity (typically 0-4 or 1-4)
- **M(K)**: Continuation approximation sensitivity (typically 0-10 or 1-6)

These are treated as **independent variables**, allowing analysis of their individual impact on performance.

### Performance Metrics
- **Time**: Execution time in seconds
- **NEval**: Number of evaluations
- **NApply**: Number of applications
- **Precise**: Precision metric (1.0 = perfect, <1.0 = approximation)

## Benchmark Suite

The suite includes 8 focused benchmarks:
1. **basic** - Basic exception and resumption patterns
2. **nondet** - Nondeterminism with branching effects
3. **nested** - Nested effect handlers
4. **multi-effect** - Multiple independent effects
5. **recursion** - Recursive functions with effects
6. **state-handler** - Stateful effect handlers
7. **complex-flow** - Complex control flow patterns
8. **nested-nondet** - Nested nondeterminism

## Analysis Results

### Key Findings

**D (Demand-level) Impact:**
- Minimal impact on execution time across all benchmarks
- Time variation by D is typically <5% across different D values

**M(K) (Continuation) Impact:**
- Significant impact on execution time, especially for:
  - `complex-flow`: Up to ~152x difference between M(K)=1 and M(K)=5
  - `nested-nondet`: Up to ~31x difference
  - `state-handler`: Up to ~4x difference

**Precision Observations:**
- 100% precision: `basic`, `nested`
- 85-95% precision: `nondet`, `recursion`, `multi-effect`, `complex-flow`
- <85% precision: `state-handler`, `nested-nondet`

## Interpreting Results

### Time Trends
- Fast benchmarks (<10ms): basic, nested, recursion, nondet
- Normal benchmarks (10-50ms): multi-effect, state-handler, nested-nondet
- Slow benchmarks (>50ms): complex-flow

### Precision Issues
Lower precision indicates the analysis is making approximations rather than computing exact values. This is expected for complex analyses with higher sensitivity parameters.

### Anomalies
Some benchmarks have outlier cases (e.g., complex-flow with some M(K) combinations) that show significantly higher execution times. These may indicate:
- Exponential complexity hitting worst-case behavior
- Cache misses or memory allocation patterns
- Specific example patterns that stress the analysis

## Running the Full Pipeline

```bash
# Run benchmarks
stack run koka -- -e run-benchmarks.kk

# Analyze results
python3 analyze-suite-results.py

# Generate detailed insights
python3 analyze-suite-details.py

# Export reports
python3 export-suite-reports.py
```

## JSON Output Format

The `suite-analysis.json` file contains:

```json
{
  "benchmark-name": {
    "analysis-type": {
      "name": "Analysis display name",
      "num_examples": 150,
      "d_values": [1, 2, 3, 4],
      "m_values": [1, 2, 3, 4, 5, 6],
      "time": {
        "count": 150,
        "min": 0.0009,
        "max": 0.0033,
        "mean": 0.0018,
        "median": 0.0018,
        "stdev": 0.0004
      },
      "d_trends": {
        "1": { "mean": 0.0019, ... },
        "2": { "mean": 0.0018, ... }
      },
      "m_trends": {
        "1": { "mean": 0.0016, ... },
        "2": { "mean": 0.0018, ... }
      }
    }
  }
}
```
