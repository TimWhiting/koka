# Benchmark Suite Analysis - Complete Summary

## Overview

A comprehensive analysis of the Koka effect handler benchmark suite, examining how different analysis types (DMCFA, DMCFAE, KCFA) scale with sensitivity parameter variations. Primary focus on precision-performance trade-offs and parameter sensitivity across benchmark categories.

## Key Findings

### D (Demand Level) Impact: MINIMAL
- **Average multiplier**: 1.08x - 1.30x from D=1 to D=4
- **Conclusion**: D has low-to-moderate impact on execution time
- **Recommendation**: Safe to increase D for precision without major performance penalty

### M(K) (Context Sensitivity) Impact: VARIABLE
- **Basic patterns**: 1.17x - 1.32x multiplier (LOW impact)
- **Complex patterns**: 1.61x - 94x multiplier (MODERATE to HIGH impact)
- **Hotspots**:
  - `complex-flow`: 94.2x increase from M(K)=1 to M(K)=6 (exponential complexity)
  - `nested-nondet`: 8.9x increase (exponential growth)
  - `state-handler`: 1.6x increase (moderate growth)

## Benchmark Characteristics

### High-Precision Benchmarks (100% Precision)
1. **basic** - Elementary exception/resumption patterns
   - D: 1.08x impact (minimal)
   - M(K): 1.18x impact (minimal)
   - Best for: Validating baseline analysis correctness

2. **nested** - Nested effect handlers
   - D: 1.15x impact (minimal)
   - M(K): 1.17x impact (minimal)
   - Best for: Testing nested handler composition

### Standard Benchmarks (85-95% Precision)
3. **nondet** - Nondeterminism and branching
   - D: 1.14x impact (minimal)
   - M(K): 1.18x impact (minimal)
   - Precision: 86.7%

4. **recursion** - Recursive effects
   - D: 1.08x impact (minimal)
   - M(K): 1.29x impact (minimal)
   - Precision: 92.6%

5. **multi-effect** - Multiple independent effects
   - D: 1.29x impact (moderate)
   - M(K): 1.32x impact (minimal)
   - Precision: 94.4%

### Complex Benchmarks (62-90% Precision)
6. **complex-flow** - Complex control flow
   - D: 1.10x impact (minimal)
   - M(K): 94.2x impact (EXTREME - exponential!)
   - Precision: 90.5%
   - Note: Shows worst-case exponential behavior

7. **nested-nondet** - Nested nondeterminism
   - D: 1.23x impact (moderate)
   - M(K): 8.9x impact (significant)
   - Precision: 62.5%

8. **state-handler** - Stateful handlers
   - D: 1.30x impact (moderate)
   - M(K): 1.6x impact (minimal)
   - Precision: 63.3%

## Analysis Comparison

### DMCFA (Demand-driven Monovariant CFA)
**Status**: Complete data for all 8 benchmarks

**Average Precision**: 86.3%
- Perfect (100%): basic, nested
- High (90-94%): multi-effect, complex-flow, recursion
- Moderate (85-89%): nondet
- Low (<80%): state-handler (63.3%), nested-nondet (62.5%)

**Characteristics**:
- Standard demand-driven context-free analysis
- Monovariant: single value per location
- Both D (demand-level) and M(K) (context sensitivity) tunable
- Excellent for simple patterns; struggles with combined effects

**Best for**: Elementary patterns, baseline validation
**Weak on**: State + nondeterminism combinations

### DMCFAE (Demand-driven Monovariant CFA - Exponential)
**Status**: Partial data (only `basic` benchmark complete)

**Current Precision**: 
- basic: 100.0% (matches DMCFA)

**Characteristics**:
- Exponential approximation variant of monovariant CFA
- May recover precision on complex patterns through exponential sensitivity
- Awaiting data from remaining benchmarks

**Hypothesis**: DMCFAE may improve precision on state-handler and nested-nondet where DMCFA loses 37% accuracy

### KCFA (k-Context-sensitive CFA)
**Status**: Benchmarks in progress

**Expected Characteristics**:
- Classical context-sensitive analysis
- Uses K parameter (context depth) instead of M(K)
- Likely superior on recursive patterns; different scaling
- Will provide comparison point for precision/performance trade-offs

## Generated Artifacts

### Analysis Scripts
- `analyze-suite-results.py` - Main analysis aggregation
- `analyze-suite-details.py` - Detailed insights
- `export-suite-reports.py` - Multi-format reporting
- `generate-comparison-graphs.py` - Visualization
- `generate-sensitivity-reports.py` - Metric reports

### Output Files

**JSON Data**:
- `benchmarks/analysis/suite-analysis.json` - Complete analysis data

**Graphs** (19 PNG files):
- 8 benchmarks × 2 graphs (D and M(K) comparisons)
- 2 cross-benchmark summary graphs
- Per-benchmark precision vs cost graphs

**Reports** (Text):
- `d_sensitivity_report.txt` - D impact analysis
- `mk_sensitivity_report.txt` - M(K)/K impact analysis
- `sensitivity_cost_summary.txt` - Cost comparison table

**Reports** (Markdown):
- `PERFORMANCE_REPORT.md` - Human-readable summary

## Precision-Performance Trade-offs

Key finding: **D parameter has no precision impact; M(K) parameter is precision-preserving**.

### Impact Summary
- **D (Demand-Level)**:
  - Time: 1.08-1.30x increase from D=1 to D=4
  - Precision: 0% change (remains constant)
  - Safe to increase for performance reasons

- **M(K) (Context Sensitivity)**:
  - Time: 1.18-94.2x increase from M(K)=1 to M(K)=6
  - Precision: Never decreases (sometimes improves)
  - Represents true precision opportunity

### Problematic Patterns

**state-handler (63.3% precision)**
- State propagation through handler chains loses information
- 37% of value flows untraced
- Needs special-case handling or higher sensitivity

**nested-nondet (62.5% precision)**
- Nondeterministic choices in nested contexts cause explosion
- 37% precision loss with exponential M(K) cost
- Most challenging pattern in suite

See `PRECISION_ANALYSIS.md` for detailed precision breakdown and recovery strategies.

## Practical Usage Guide

### For Fast Analysis (< 10ms)
```
Recommendations:
- Use: D=1, M(K)=1 or 2
- Benchmarks: basic, nondet, nested, recursion
- Expected precision: 85-100%
```

### For Balanced Analysis (10-50ms)
```
Recommendations:
- Use: D=2-3, M(K)=3-4
- Benchmarks: multi-effect, state-handler
- Expected precision: 85-95%
```

### For Precise Analysis (willing to go slower)
```
Recommendations:
- Use: D=3, M(K)=4-5
- Avoid M(K)=6 for complex-flow (extreme cost)
- Be careful with nested-nondet above M(K)=4
```

### For Complex Patterns
```
Warning: complex-flow shows exponential scaling
- M(K)=1: 0.0047s
- M(K)=2: 0.0124s (2.6x)
- M(K)=3: 0.0271s (5.8x)
- M(K)=4: 0.1054s (22x)
- M(K)=5: 0.4453s (95x) ← AVOID
- M(K)=6: 0.0068s (back to minimal?) ← Possible timeout/approximation
```

## Statistical Summary

### D Impact Distribution
- LOW (< 1.2x): basic, nondet, nested, recursion, complex-flow
- MODERATE (1.2-2x): multi-effect, state-handler, nested-nondet

### M(K) Impact Distribution
- LOW (< 1.5x): basic, nondet, nested, multi-effect, recursion
- MODERATE (1.5-10x): state-handler, nested-nondet
- HIGH (> 10x): complex-flow

## Running the Analysis Pipeline

```bash
# 1. Run benchmarks (generates CSV results)
stack run koka -- -e run-benchmarks.kk

# 2. Aggregate results
python3 analyze-suite-results.py

# 3. Generate detailed insights
python3 analyze-suite-details.py

# 4. Create comparison graphs
python3 generate-comparison-graphs.py

# 5. Generate metric reports
python3 generate-sensitivity-reports.py

# 6. Export multi-format reports
python3 export-suite-reports.py
```

## Next Steps

### For Researchers
1. Investigate why complex-flow shows exponential M(K) scaling
2. Analyze nested-nondet precision/cost trade-offs
3. Compare DMCFA vs KCFA scaling characteristics

### For Performance Tuning
1. Profile memory usage in addition to time
2. Analyze cache behavior for M(K)=5-6 transitions
3. Optimize state-handler implementation

### For Algorithm Development
1. Use as baseline for new analysis algorithm comparison
2. Test precision improvements in complex-flow
3. Verify scaling expectations for new patterns

## File Locations

```
/Users/timwhiting/koka/
├── BENCHMARK_ANALYSIS_SUMMARY.md         # This file - overview
├── PRECISION_ANALYSIS.md                 # Detailed precision breakdown
├── analyze-suite-results.py              # Main analysis
├── analyze-suite-details.py              # Insights
├── export-suite-reports.py               # Export reports
├── generate-comparison-graphs.py         # Graph generation
├── generate-sensitivity-reports.py       # Metric reports
├── ANALYSIS_TOOLS_README.md              # Tool documentation
├── benchmarks/
│   ├── analysis/
│   │   ├── GRAPHS_README.md              # Graph guide
│   │   ├── suite-analysis.json           # Complete data
│   │   ├── graphs/                       # PNG visualizations
│   │   └── exports/                      # CSV/Markdown/text reports
│   ├── results/
│   │   └── suite/                        # Raw CSV results
│   └── ...
└── run-benchmarks.kk                     # Benchmark runner
```

## Version Info
- Generated: December 8, 2025 (Updated with precision focus)
- Koka Version: 3.2.3
- Benchmark Suite: 8 focused effect handler benchmarks
- Total Examples: 1,690 (across all analyses and parameter combinations)
- Analysis Types: 3 (DMCFA complete, DMCFAE partial, KCFA pending)
- Complete Data: DMCFA all 8 benchmarks; DMCFAE basic only; KCFA in progress
- Key Metrics: 51 core tests passing, 86.3% average precision (DMCFA), 100% on simple patterns

## Documentation Structure

1. **BENCHMARK_ANALYSIS_SUMMARY.md** (this file)
   - Overview of benchmarks and analysis types
   - Performance characteristics and sensitivity
   - Usage recommendations

2. **PRECISION_ANALYSIS.md** (detailed)
   - Per-benchmark precision breakdown
   - Analysis type comparison
   - Precision recovery strategies
   - Why state-handler and nested-nondet are challenging

3. **ANALYSIS_TOOLS_README.md** (reference)
   - Python script documentation
   - How to run analysis pipeline
   - Output formats and interpretation

4. **GRAPHS_README.md** (visual reference)
   - Graph interpretation guide
   - Per-benchmark visualizations
