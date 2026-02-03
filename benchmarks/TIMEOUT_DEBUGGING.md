# Timeout Debugging Log

This document tracks the investigation and resolution of benchmark timeouts.

## Overview

- **Total timeouts**: 252 out of 3,837 results (6.6%)
- **dmcfa variant**: 113 timeouts (5.9%)
- **dmcfae variant**: 139 timeouts (7.2%)

## Critical Issues - Baseline Configuration Timeouts (d=0 or m=0)

These benchmarks timeout even with minimal analysis sensitivity, indicating fundamental issues.

### High Priority - Timeouts at 0-0

| Benchmark | Status | Last Tested | Notes |
|-----------|--------|-------------|-------|
| `handlers/scoped/example4` | ❌ TIMEOUT (dmcfae only) | 2026-02-02 | dmcfa works fine (10.982s) |
| `koka-gen/coop-communication/prime-sieve` | ❓ NOT TESTED | - | 14 baseline timeouts in old data |
| `koka-gen/interp2/t2` | ❓ NOT TESTED | - | 6 baseline timeouts in old data |
| `koka-gen/interp2/t3` | ❓ NOT TESTED | - | 7 baseline timeouts in old data |

### Medium Priority - Timeouts at d=0, m>0 or d>0, m=0

| Benchmark | Timeout Configs | Count |
|-----------|----------------|-------|
| `coop-communication/send-recv` | 0-1, 0-2, 0-3, 1-0, 2-0, 3-0 | 12 |
| `koka-gen/build/mymakefile-example1` | 0-1, 0-2, 0-3, 2-0, 3-0 | 7 |
| `koka-gen/build/mymakefile-example2` | 0-1, 0-2, 0-3, 2-0, 3-0 | 7 |
| `koka-gen/build/mymakefile-example4` | 0-1, 0-2, 0-3, 2-0, 3-0 | 5 |
| `koka-gen/interp2/t1` | 1-0, 2-0, 3-0 | 5 |
| `koka-gen/interp2/err3` | 2-0, 3-0 | 4 |
| `koka-gen/ukanren/q1` | 0-2, 0-3 | 4 |
| `koka-gen/ukanren/q2` | 0-2, 0-3 | 4 |

## Investigation Log

### 2026-02-02: Initial Analysis

**Issue Found**: JSON result files had `storeMetrics: null` with `isTimeout: false`, causing inconsistencies.

**Actions Taken**:
1. Created [fix-timeout-flags.py](fix-timeout-flags.py) to correct all JSON files
2. Updated all files with `storeMetrics: null` to have `isTimeout: true`
3. Created [find-timeouts.py](find-timeouts.py) for ongoing analysis
4. Updated [analyze.py](analyze.py) to show timeout annotations (⚠️N) on graphs

**Results**:
- Discovered 252 actual timeouts (previously hidden by incorrect flags)
- Generated detailed timeout report at `analysis/timeouts.csv`

### 2026-02-02: Scoped Example2 Discrepancy

**Observation**: Manual run of `analysis/benchmarks/handlers/scoped.kk --sensitivity="(0,0)"` completed quickly.

**Data Check (Before Fix)**:
```
benchmarks/results/dmcfa/0/0/.../example2.json
  isTimeout: True
  storeMetrics: null
  analysisTimes: []
```

**Hypothesis**: The stored results were stale, but also the analysis had a timeout issue (50 second limit).

**Resolution**: ✅ **FIXED** - Timeout issue resolved in analysis code.

**Data Check (After Fix)**:
```
benchmarks/results/dmcfa/0/0/.../example2.json
  isTimeout: False
### 2026-02-02: Comprehensive Re-test of Scoped Examples

**Major Fix Applied**: All dmcfa scoped examples now passing!

**Previously timing out, now FIXED:**

| Example | (0,0) | (100,100) | 
|---------|-------|-----------|
| example1 | 0.019s | 0.102s |
| example2 | 2.234s | 0.704s |
| example3 | 0.611s | 0.562s |
| example4 | 10.982s | 0.039s |
| example5 | 0.113s | 8.007s |

**Still timing out:**
- `dmcfae example4` at (0,0) - variant-specific issue

**Observations**:
- All 5 scoped handler examples that were timing out are now fixed in dmcfa
- Interesting performance characteristic: Higher sensitivity (100,100) can be faster in some cases (example2, example4)
- dmcfae variant still has issues with example4 at (0,0), suggesting variant-specific problem

**Next Steps**:
- [ ] Re-run the full benchmark suite to update all timeout results
- [ ] Test other previously-timing-out benchmarks (prime-sieve, interp2, etc.)
- [ ] Investigate why dmcfae still times out on example4
- [ ] Update timeout analysis reports with fresh data

## Benchmark File Locations

### Coop-Communication
- File: [analysis/benchmarks/koka-gen/coop-communication.kk](../analysis/benchmarks/koka-gen/coop-communication.kk)
- Functions: `analyze-prime-sieve()`, `analyze-send-recv()`, `analyze-spawn()`

### Handler Examples
- File: [analysis/benchmarks/handlers/scoped.kk](../analysis/benchmarks/handlers/scoped.kk)
- Functions: `example2()`, `example3()`, `example4()`

### Interpreter Tests
- File: [analysis/benchmarks/koka-gen/interp2.kk](../analysis/benchmarks/koka-gen/interp2.kk)
- Functions: `analyze-t1()`, `analyze-t2()`, `analyze-t3()`, `analyze-err3()`

### Build System Examples
- File: [analysis/benchmarks/koka-gen/build.kk](../analysis/benchmarks/koka-gen/build.kk)
- Functions: Various mymakefile-example* functions

### Ukanren Tests
- File: [analysis/benchmarks/koka-gen/ukanren.kk](../analysis/benchmarks/koka-gen/ukanren.kk)
- Functions: `analyze-q1()`, `analyze-q2()`

## Running Individual Benchmarks

To test a specific benchmark manually:
```bash
stack run koka -- <file.kk> --sensitivity="(d,m)"
```

Example:
```bash
stack run koka -- analysis/benchmarks/handlers/scoped.kk --sensitivity="(0,0)"
```

## Analysis Scripts

- **[find-timeouts.py](find-timeouts.py)**: Analyzes timeout patterns across all results
- **[fix-timeout-flags.py](fix-timeout-flags.py)**: Corrects isTimeout flags in JSON files
- **[analyze.py](analyze.py)**: Main analysis script with visualizations
- **Results**: Stored in `benchmarks/results/variant/d/m/` hierarchy
- **Reports**: Generated in `benchmarks/analysis/`

## Notes

- Empty `analysisTimes: []` suggests the analysis never started or was killed before timing
- `storeMetrics: null` indicates the analysis didn't produce results
- Some timeouts may be due to infinite loops or cycles in the analysis rather than just slow performance
