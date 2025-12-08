# Corrected Parameter Sensitivity Analysis

## The Real Story: Not "Precision-Limited," But Rather "Already Precise" or "Threshold-Based"

### What I Got Wrong

I labeled benchmarks like `basic` and `nested` as "precision-limited," which was **misleading**. They're not precision-limited - they achieve **perfect 100% precision from the start** at any parameter values.

**Correct characterization**:
- These are **"Already Optimal"** benchmarks - parameters don't help because they don't need to
- No precision improvement possible because we're already at 100%

### What's Actually Happening: Three Categories of Behavior

#### Category 1: Already Perfect (No Parameter Sensitivity Needed)
Examples: `basic`, `nested`, simple patterns

**Pattern**: precision = 1.0 at all parameter combinations (D=0-4, M(K)=1-6)

**What this means**:
- The analysis algorithm can perfectly understand these patterns
- No precision ceiling to hit
- Increasing parameters just wastes time
- **Recommendation**: Use minimum settings (D=0, M(K)=1)

**Examples from `basic` benchmark**:
- `basic-exception`: 1.0 at all D,M(K) values
- `basic-resume`: 1.0 at all D,M(K) values
- `basic-resume-context`: 1.0 at all D,M(K) values
- (All 5 examples in basic: consistently 100%)

---

#### Category 2: Threshold Behavior (True Parameter Sensitivity)
Examples: Examples from `nested-nondet`, `nondet`, `recursion`

**Pattern**: Precision is either 0% or 100%, depending on whether sensitivity is sufficient

```
Example: nondet-guarded
  D=1, M(K)=1: precise=0.00 (too insensitive)
  D=1, M(K)=2: precise=1.00 (suddenly perfect!)
  D=1, M(K)=3-6: precise=1.00 (stays perfect)
```

**What this means**:
- There's a **minimum sensitivity threshold** required to analyze the pattern
- Below threshold: analysis fails completely (0% precision)
- Above threshold: analysis succeeds completely (100% precision)
- Once you cross the threshold, further increases don't help precision (but cost time)

**Cost/benefit**:
- M(K)=1 → M(K)=2: **Infinite precision gain** (0% → 100%), cost ~2x time
- M(K)=2 → M(K)=3: **Zero precision gain** (already 100%), cost ~10% more time

**Recommendation**: 
- Find the minimum threshold for your pattern
- Use that exact setting (don't oversensitize)

**Real examples from nested-nondet**:
- `nondet-both-contexts`: 0% at M(K)=1 → 100% at M(K)=2+
- `nondet-guarded`: 0% at M(K)=1 → 100% at M(K)=2+
- `nondet-nested-simple`: 0% at M(K)=1 → 100% at M(K)=2+
- `nondet-three-levels`: 0% at M(K)=1 → 100% at M(K)=2+

---

#### Category 3: Precision Ceiling (Hard Algorithm Limitation)
Examples: `state-handler`, `complex-flow`, `nested-nondet` (aggregate)

**Pattern**: Precision improves with parameters, but hits a maximum and plateaus

```
Example: state-handler + DMCFA
  D=0, M(K)=1: precise=0.63 (63%)
  D=1, M(K)=1: precise=0.63 (no change)
  D=2, M(K)=2: precise=0.63 (no change)
  ...even at D=4, M(K)=6: precise=0.63 (CEILING)
```

**What this means**:
- The algorithm has a hard limit on what it can analyze
- No parameter tuning will exceed that limit
- The 37% precision loss is **fundamental to the algorithm**
- Different algorithms may have different ceilings (DMCFAE reaches 76.7% on state-handler)

**Examples**:
- `state-handler`: 63% ceiling (DMCFA), 76% ceiling (DMCFAE)
- `complex-flow`: ~90% ceiling across all analyses
- `nested-nondet`: 62% ceiling (DMCFA), 58% ceiling (DMCFAE)

**Recommendation**: 
- If precision is already at ceiling, don't tune parameters
- Switch to a different algorithm instead (DMCFAE for state patterns)

---

## Parameter Sensitivity Summary

### D vs M(K) - Which One Actually Works?

Looking at the raw data:

**Threshold examples (where parameters matter)**:
- `nondet-guarded`: Threshold at M(K)=2, not sensitive to D at all
- `nondet-both-contexts`: Threshold at M(K)=2, not sensitive to D  
- `nondet-nested-simple`: Threshold at M(K)=2, not sensitive to D

**Finding**: When precision does respond to parameters, **M(K) is the sensitive one, D is not**. This is because these examples have complex nondeterministic flow that needs context sensitivity (M(K)), not demand analysis (D).

### Cost Analysis for Threshold Crossing

From actual data:

```
nondet-guarded crossing threshold (D=1):
  M(K)=1: 0.0157s (0% precision)
  M(K)=2: 0.0066s (100% precision) ← CHEAPER and BETTER!
  
nondet-both-contexts crossing threshold (D=2):
  M(K)=1: 0.0147s (0% precision)
  M(K)=2: 0.0318s (100% precision) ← 2.2x cost but infinite gain
```

**Key insight**: Crossing the precision threshold is **not always more expensive** - sometimes it's cheaper! The analysis only needs enough sensitivity to understand the pattern, not more.

---

## What This Changes

### Old (Incorrect) View
- "These benchmarks are precision-limited"
- "Parameters don't help because of algorithm limits"
- "D and M(K) are interchangeable"

### New (Correct) View
- "These benchmarks are already perfectly analyzed OR hit a hard algorithm ceiling"
- "Some patterns have precision thresholds below which they fail completely"
- "M(K) matters for complex flows; D is mostly irrelevant for the patterns we tested"
- "Once you cross a threshold, further parameter increases waste time"

---

## Revised Recommendations

### For Benchmarks Already at 100%
(`basic`, `nested`, `multi-effect` when fully precise):
```
DON'T tune. Use D=0, M(K)=1.
You're already at the maximum precision.
Every extra parameter is wasted computation.
```

### For Benchmarks with Threshold Behavior
(`nested-nondet`, `nondet`, `recursion` for some examples):
```
1. Test M(K)=1 vs M(K)=2 (the key transition)
2. If precision jumps, stop at M(K)=2
3. Don't keep increasing - you already have 100%
4. Cost: ~2x for M(K)=2, but you get perfect analysis
```

### For Benchmarks with Precision Ceiling
(`state-handler`, `complex-flow`):
```
1. Check if you're at the ceiling
2. If yes: don't tune, switch algorithms instead
3. If no: increase M(K) carefully
4. DMCFAE might break your ceiling (13% improvement on state-handler)
```

---

## The Real Impact of Parameters

From actual measured data:

**D Parameter**:
- Causes time variation (1.08-1.30x range)
- **Does not cause precision changes** on the benchmarks tested
- Mostly irrelevant for nondeterminism/control flow patterns
- Might matter for demand-driven optimizations we're not testing

**M(K) Parameter**:
- Causes time variation (1.18-94x range!)
- **Does cause precision changes** when there's a threshold
- Beyond the threshold: time increases but precision plateaus
- Critical for context-sensitive patterns

---

## Corrected Data Summary

### Benchmarks with Zero Parameter Sensitivity

These get 100% precision at D=0, M(K)=1 and don't improve further:
- `basic` (5/5 examples): 100% at all settings
- `nested` (13/13 examples): 100% at all settings
- Parts of `multi-effect`: 100% at baseline

**Correct characterization**: Not "precision-limited" - these are **"perfectly analyzed"** benchmarks.

### Benchmarks with Threshold Behavior

These have examples that go 0% → 100% at some M(K) value:
- `nested-nondet`: 6-8 examples show threshold at M(K)=2 or M(K)=3
- `nondet`: 2-4 examples show threshold at M(K)=2
- `recursion`: Some examples show threshold behavior

**Correct characterization**: **"Threshold-sensitive"** - they need minimum M(K) but excess is wasted.

### Benchmarks with Precision Ceiling

These reach a maximum precision that parameters can't exceed:
- `state-handler`: Ceiling 63% (DMCFA) or 76% (DMCFAE) - hit immediately
- `complex-flow`: Ceiling ~90% - hit immediately
- `nested-nondet`: Ceiling 62% (DMCFA) - hit at baseline or after small M(K) increase

**Correct characterization**: **"Algorithm-limited"** - parameters can't break the ceiling.

---

## Conclusion

The analysis revealed that **context sensitivity parameters don't universally improve precision**. Instead:

1. **Most patterns are already perfectly analyzed** (basic, nested, etc.)
2. **Some patterns have discrete thresholds** - you need just enough sensitivity to cross it
3. **Some patterns have algorithmic ceilings** - no amount of parameter tuning helps

**The right approach isn't "tune all parameters for maximum sensitivity"** - it's **"understand which patterns need which parameters, and stop tuning once you hit the ceiling or cross the threshold."**

This makes parameter sensitivity analysis critical for performance optimization: **you can often get the same precision at half the cost by avoiding unnecessary tuning on already-optimal patterns.**
