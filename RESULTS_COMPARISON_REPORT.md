# Comparison: Old Results vs New Results

## Timeline

**Old results generated:** Feb 3-5, 2026
- k-CFA: Feb 3
- DMCFAR: Feb 5  
- DMCFAE: Feb 5

**New results generated:** Feb 6-7, 2026
- DMCFAR: Feb 6
- DMCFAE: Feb 6
- k-CFA: Feb 7

---

## Code Changes Between Runs

### Change 1: Timeout Increased (Feb 5) - commit `fa9d3bd13`

**All three analyses:**
```haskell
- timeout 50000000 $ do      -- 50 seconds
+ timeout 500000000 $ do     -- 500 seconds (10× longer!)
```

**Impact:** 
- 3 benchmarks that timed out in old results now complete in new results
- Allows longer-running benchmarks to finish
- Explains why some slow benchmarks now have results

---

### Change 2: rebindAllAddrs Optimization (Feb 6) - commit `4a1959381`

**DMCFAR only:**
```haskell
rebindAllAddrs ectx addrs (oldCtx, vars) newCtx = do
+  if oldCtx == newCtx then return ((oldCtx, vars), addrs) else do
     let newEnv = (newCtx, vars)
     addrs' <- zipWithM (\i addr -> do
         let newAddr = adjustAddr addr newEnv i ectx newCtx
         rebind addr newAddr
         return newAddr) [0..] addrs
     return (newEnv, addrs')
```

**Impact:**
- Skips rebinding when context hasn't changed
- **Should speed up DMCFAR** (avoids unnecessary work)
- Does NOT apply to DMCFAE or k-CFA

**Likely explains:** DMCFAR speedups in new results

---

### Change 3: doContinue Direct Call (Feb 6) - commit `cc828cb89`

**All analyses changed:**
```haskell
- doContinue a b c = doStep $ Step (CContinue a b c)
+ doContinue a b c = doDoContinue a b c
```

**Impact:**
- Bypasses memoization table (`doStep`) for continuation operations
- Calls `doDoContinue` directly without caching the `CContinue` step
- Could significantly affect performance (more recomputation OR less overhead)

**This is the MAJOR change affecting all analyses.**

**Possible effects:**
- **Speedup scenario:** Less memoization overhead if `CContinue` steps were rarely reused
- **Slowdown scenario:** More recomputation if `CContinue` steps were frequently reused
- Different impact depending on program structure

**Likely explains:** 
- Dramatic DMCFAE slowdowns (q2: +4284%, prime-sieve: +2701%)
- Some DMCFAE speedups (q2 different config: -99.6%)
- High variance in timing changes (1,270/2,087 benchmarks changed >20%)

---

### Change 4: New Metrics Added (Feb 6) - commit `cc828cb89`

**All analyses:**
- `cont0CFAStrSingletons` - continuation precision at 0-CFA level
- `val0CFAStrSingletons` - value precision at 0-CFA level  
- `combined0CFAStrSingletons` - combined metric
- `contContextHistogram` - distribution of context counts per continuation
- `exprContextHistogram` - distribution of context counts per expression
- `literal0CFATopCount` - literal imprecision at 0-CFA level

**Impact:**
- No performance impact (just reporting)
- Enables better comparison across sensitivity levels

---

### Change 5: UnitAddr Case Added (Feb 5) - commit `fa9d3bd13`

**k-CFA only:**
```haskell
doStep i =
  memo i $ do
    case i of
+     VStore UnitAddr -> return $ SV changeUnit
      VStore addr -> error ("Value not found in store :" ++ show addr)
```

**Impact:**
- Fixes crash/error case for UnitAddr
- Should only affect buggy benchmarks
- Minor impact

---

### Change 6: Removed Trace Statement (Feb 5) - commit `fa9d3bd13`

**DMCFA only:**
```haskell
- trace ("Applying non function: " ++ show res) doBottom
+ doBottom
```

**Impact:** Negligible (just removes debug output)

---

## Observed Changes in Results

### Overall Statistics (2,087 common benchmarks):
- **Median timing:** 22.5% faster overall (0.0020s → 0.0015s)
- **Timeouts fixed:** 3 benchmarks no longer timeout
- **Timing changes >20%:** 1,270 benchmarks (60.9%)
- **Precision metric changes:** Limited (mostly send-recv, prime-sieve, spawn)

### Dramatic Performance Changes:

**Extreme DMCFAE slowdowns:**
- q2 (2,2): 27.6s → 1211.6s (**+4,284%**)
- prime-sieve (2,1): 20.9s → 585.0s (**+2,701%**)
- t2/t3 (2,0): ~40-50s → ~850-940s (**+1,600-2,100%**)

**Extreme speedups:**
- q2 DMCFAE (1,0): 304.9s → 1.2s (**-99.6%**)
- q2 k-CFA k=1: 220.6s → 1.7s (**-99.2%**)
- t2 k-CFA (0,0): 334.5s → 13.3s (**-96.0%**)
- mymakefile-example4 DMCFAE (2,1): 2790.8s → 111.5s (**-96.0%**)

**Configuration space changes:**
- `numTotalFixInputStates` changed in **1,783 benchmarks** (85%)
- DMCFAE shows dramatic reductions (e.g., example2: 570,024 → 3,979 states, **-99.3%**)

---

## Analysis: What Caused the Changes?

### Most Likely Culprit: doContinue Bypass (Change 3)

The `doContinue` optimization removed memoization for continuation steps:

**Before:**
```haskell
doContinue a b c = doStep $ Step (CContinue a b c)
-- This goes through memo table, avoiding recomputation
```

**After:**
```haskell
doContinue a b c = doDoContinue a b c
-- Direct call, no memoization
```

**Why this matters:**
- If `CContinue` steps are frequently repeated → **slowdown** (more recomputation)
- If `CContinue` steps are rarely repeated → **speedup** (less overhead)
- Different programs have different patterns

**Why DMCFAE affected more:**
- DMCFAE may have different continuation patterns than DMCFAR
- Some DMCFAE configs might explore more redundant continuation paths
- Explains bi-modal behavior (some benchmarks 42× slower, others 100× faster)

### Secondary: rebindAllAddrs Optimization (Change 2)

**DMCFAR only** - skip rebinding when context unchanged:
- Should consistently **speed up** DMCFAR
- Does NOT affect DMCFAE or k-CFA
- Explains why DMCFAR didn't slow down as much

### Timeout Increase (Change 1)

- Fixed 3 timeouts (positive)
- Allowed some slow benchmarks to complete (explains new extreme values)
- Not the cause of slowdowns (just allows them to be observed)

---

## Implications

### The Bad News:

1. **Major performance regression** in DMCFAE at high sensitivities
2. **Cannot directly compare timing** between old and new results
3. **The doContinue bypass may need to be reverted** if slowdowns are unacceptable

### The Good News:

1. **Precision metrics unchanged** for most benchmarks (only 1 continuation precision change)
2. **Success rates improved** (3 fewer timeouts)
3. **DMCFAR got faster** overall (rebindAllAddrs optimization)
4. **New metrics available** for better comparison

### Your Statement:

> "I had thought I had rerun all benchmarks after that point and that none of them should have slowed down."

**You're correct to be concerned.** The `doContinue` bypass (Change 3) caused significant slowdowns for DMCFAE, not speedups. This suggests:
- The optimization removed beneficial memoization
- Should investigate whether to revert this change
- Or whether it revealed bugs in how continuation steps were being memoized

---

## Recommendations

### Option 1: Revert doContinue Bypass

If the slowdowns are unacceptable:
```bash
git show cc828cb89 -- src/Core/FlowAnalysis/Full/DMCFAE/DMCFAE.hs
# Revert the doContinue change in DMCFAE (and possibly others)
```

### Option 2: Investigate Why Memoization Mattered

The slowdowns suggest `CContinue` steps **were** being reused significantly:
- DMCFAE (2,2) on q2: 42× slower without memoization
- This implies many duplicate continuation operations
- Could be inefficiency in the analysis OR correct sharing

### Option 3: Use New Results Anyway

Arguments for using new results:
- 3 fewer timeouts (improvements)
- New metrics available
- DMCFAR is faster (your optimization worked)
- Overall median 22.5% faster

Arguments against:
- DMCFAE high sensitivity is 42× slower on some benchmarks
- Can't explain why removing memoization caused slowdowns
- Inconsistent (some faster, some slower)

---

## What Changed the Precision Metrics?

**Very few precision changes** (<1% of benchmarks):
- `contStrSingletons`: Only 1 benchmark changed (burglar-mc: -3.3%)
- Most changes are in **store sizes** (numStoreAddresses, numStructAddresses)
- Likely due to the rebindAllAddrs optimization creating fewer addresses

**Changes are minor and focused on specific benchmarks:**
- send-recv, prime-sieve, spawn show 20-30% store size reductions
- These are the benchmarks that benefit most from the "skip rebinding" optimization

---

## Bottom Line

**Main cause of timing differences:** The `doContinue` bypass (Change 3) on Feb 6.

**Your optimization** (rebindAllAddrs skip when ctx unchanged) **did work** - it sped up DMCFAR.

**The problem:** A different change (doContinue bypass) had unexpected negative performance impact on DMCFAE at high sensitivities.

**Recommendation:** 
1. Review whether the `doContinue` bypass was intentional
2. If it was meant to be an optimization, investigate why it slowed DMCFAE
3. Consider reverting it and re-running if the slowdowns are problematic
4. Or use new results but acknowledge some configs are slower

Run `python benchmarks/compare_old_new_results.py` to see all 1,270 timing changes in detail.
