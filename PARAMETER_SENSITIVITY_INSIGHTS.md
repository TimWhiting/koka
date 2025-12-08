# Context Sensitivity Parameter Analysis - Key Insights

## Overview

These analyses show **how context sensitivity parameters (D, M(K), K) actually correlate with precision improvements on individual examples**, not just aggregate statistics.

## Three New Reports Generated

1. **parameter_sensitivity_analysis.txt** - Per-example precision tracking
   - Shows which examples improve/worsen/stabilize as parameter increases
   - Breaks down cost multiplier for each example

2. **precision_cost_tradeoff.txt** - Categorization of examples
   - Perfect (100% precision examples)
   - Improvable (sensitivity helps)
   - Limited (high cost, no precision improvement)

3. **parameter_effectiveness.txt** - D vs M(K) comparison (DMCFA/DMCFAE only)
   - Which parameter drives precision improvements
   - Cost multipliers for each parameter independently

## Key Findings

### 1. Most Benchmarks Are "Precision-Limited"

For **basic, nested, multi-effect, recursion**: Increasing parameters **doesn't improve precision**
- All examples are already analyzed perfectly or hit a precision ceiling
- Increased sensitivity only adds cost, no benefit

Examples:
- **basic**: All 5 examples stay at 100% precision regardless of M(K) (cost: 1.17x)
- **nested**: All 13 examples stay at 100% precision (cost: 1.81x)

### 2. Some Examples Benefit from Increased Sensitivity

**nondet, recursion, complex-flow, nested-nondet** have examples where higher M(K)/K improves precision:

#### nondet (4 examples):
- **nondet-context**: 0% → 100% precision with M(K) increase [0.86x cost]
- **nondet-nested**: 0% → 100% precision with M(K) increase [1.24x cost]
- **nondet-discard**: 0% → 100% precision with K increase [1.08x cost] (KCFA)

#### nested-nondet (8 examples):
- **6 out of 8 examples** improve precision with increased sensitivity
- Cost multiplier: 2.86x average

#### complex-flow (7 examples):
- **2 out of 7 examples** improve precision with increased sensitivity
- Cost multiplier: 1.59x average

### 3. Parameter Effectiveness: D vs M(K) Are Equally Effective

**For DMCFA/DMCFAE**, both D and M(K) drive precision improvements equally:

| Benchmark | D Improvements | M(K) Improvements | Status |
|-----------|----------------|-------------------|--------|
| **basic** | 0/5 | 0/5 | Both ineffective (precision-limited) |
| **nondet** | 2/4 | 2/4 | Equally effective |
| **nested** | 0/13 | 0/13 | Both ineffective (precision-limited) |
| **multi-effect** | 1/3 | 1/3 | Equally effective |
| **recursion** | 4/9 | 4/9 | Equally effective |
| **state-handler** | 1/1 | 1/1 | Equally effective |
| **complex-flow** | 2/7 | 2/7 | Equally effective |
| **nested-nondet** | 6/8 | 6/8 | Equally effective |

**Interpretation**: Neither D nor M(K) is inherently more effective - they improve the same examples.

### 4. Cost of Increased Sensitivity

**Cost multipliers from minimum to maximum parameter value:**

| Benchmark | DMCFA D | DMCFA M(K) | DMCFAE M(K) | KCFA K |
|-----------|---------|-----------|-------------|--------|
| **basic** | 1.17x | 1.17x | 1.17x | 1.35x |
| **nested** | 1.81x | 1.81x | 2.03x | (higher) |
| **nondet** | 1.18x | 1.18x | 1.18x | 1.57x |
| **multi-effect** | 2.26x | 2.26x | 2.26x | (higher) |
| **recursion** | 1.66x | 1.66x | 1.66x | (higher) |
| **state-handler** | 2.30x | 2.30x | 2.30x | (higher) |
| **complex-flow** | 1.59x | 1.59x | 1.59x | (higher) |
| **nested-nondet** | 2.86x | 2.86x | 2.86x | (higher) |

**Observation**: Precision-limited benchmarks have low cost multipliers despite no precision gain.

### 5. Examples That Show No Improvement Despite High Cost

These examples are **fundamentally precision-limited** - the analysis algorithm cannot fully analyze them:

| Benchmark | Example | Precision | Cost | Analysis |
|-----------|---------|-----------|------|----------|
| **nondet (KCFA)** | nondet-nested | 0% | 2.14x | K-sensitive CFA completely fails |
| **state-handler (KCFA)** | state-countdown | 0% | 4.26x | K-sensitive CFA completely fails |
| **state-handler (DMCFA)** | state-countdown | ~63% | 2.30x | Inherent algorithm limitation |
| **nested-nondet** | Various | 62.5% (DMCFA) | ~0.1s+ | Exponential nondeterminism limits analysis |

## Critical Insight: What "Sensitivity" Actually Means

**Higher context sensitivity (D, M(K), K) doesn't automatically improve precision.**

Instead:
1. For **precision-limited examples**: Sensitivity only increases cost (wasted computation)
2. For **improvable examples**: Sensitivity can recover lost information at reasonable cost
3. **Key question**: Which examples are precision-limited vs improvable?

## Recommendations

### 1. Benchmark-Specific Tuning

- **basic, nested**: Use D=1, M(K)=1, K=1 (no benefit from higher values)
- **nondet, recursion**: Use D=2-3, M(K)=3-4, K=4-6 (some examples improve)
- **complex-flow, nested-nondet**: Need investigation - high cost for uncertain gains
- **state-handler**: DMCFAE at M(K)=4-5 recommended (76.7% vs 63.3%)

### 2. Precision-Limited Detection

Implement heuristic to detect when an example is precision-limited:
- Run analysis with lowest and highest sensitivity
- If precision unchanged, example is precision-limited → don't increase sensitivity further
- Could save significant computation on precision-limited examples

### 3. For nested-nondet and complex-flow

These show extreme cost variations. Investigate:
1. Which specific examples cause exponential blowup?
2. Can we use lower sensitivity for those examples?
3. Does selective sensitivity (per-example tuning) help?

## Data Availability

All detailed per-example analyses available in:
- `benchmarks/analysis/exports/parameter_sensitivity_analysis.txt`
- `benchmarks/analysis/exports/precision_cost_tradeoff.txt`
- `benchmarks/analysis/exports/parameter_effectiveness.txt`

Raw data in `benchmarks/analysis/suite-analysis.json` with `d_trends`, `m_trends` per analysis.
