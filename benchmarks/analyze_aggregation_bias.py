#!/usr/bin/env python3
"""
Analyze whether microbenchmarks bias aggregate statistics.
Check distribution of sizes, times, precision across categories.
"""

import json
import os
import numpy as np
import pandas as pd
from scipy.stats import gmean
from collections import defaultdict

def categorize_benchmark(name):
    """Categorize benchmark by path."""
    if '/suite/' in name:
        return 'Microbenchmarks'
    elif '/koka-gen/' in name:
        return 'Koka Standard'
    elif '/handlers/' in name:
        return 'Handler Examples'
    elif '/rosetta/' in name:
        return 'Rosetta Code'
    else:
        return 'Other'

def load_all_results(root_path="benchmarks/old-results"):
    """Load all benchmark results."""
    all_results = []
    for root, dirs, files in os.walk(root_path):
        for f_name in files:
            if f_name.endswith('.json'):
                rel_path = os.path.relpath(root, root_path)
                parts = rel_path.split(os.sep)
                if len(parts) >= 3:
                    variant = parts[0]
                    d = parts[1]
                    m = parts[2]
                    
                    file_path = os.path.join(root, f_name)
                    with open(file_path, 'r') as f:
                        try:
                            if os.path.getsize(file_path) == 0:
                                continue
                            data = json.load(f)
                            if isinstance(data, dict):
                                data.update({
                                    'variant': variant,
                                    'd': int(d),
                                    'm': int(m),
                                    'config': f"{d}-{m}"
                                })
                                all_results.append(data)
                        except (json.JSONDecodeError, ValueError):
                            pass
    return all_results

def analyze_size_distribution(results):
    """Analyze program size distribution."""
    
    print("="*80)
    print("PROGRAM SIZE DISTRIBUTION (0-CFA configurations)")
    print("="*80)
    
    # Get sizes from KCFA 0-0
    sizes_by_cat = defaultdict(list)
    
    for r in results:
        if r['variant'] == 'kcfa' and r['d'] == 0 and r['m'] == 0:
            if r.get('storeMetrics'):
                m = r['storeMetrics']
                total = m.get('numTotalFixInputStates', 0)
                store = m.get('numStoreAddresses', 0)
                size = total - store
                
                cat = categorize_benchmark(r['benchmarkName'])
                sizes_by_cat[cat].append({
                    'name': r['benchmarkName'].split('/')[-1],
                    'size': size
                })
    
    # Aggregate by category
    print(f"\n{'Category':<20} {'Count':<8} {'Min':<10} {'Median':<10} {'Mean':<10} {'Max':<10}")
    print("-"*80)
    
    all_sizes = []
    for cat in ['Microbenchmarks', 'Koka Standard', 'Handler Examples', 'Rosetta Code']:
        if cat in sizes_by_cat:
            sizes = [s['size'] for s in sizes_by_cat[cat]]
            all_sizes.extend(sizes)
            print(f"{cat:<20} {len(sizes):<8} {min(sizes):<10.0f} {np.median(sizes):<10.0f} "
                  f"{np.mean(sizes):<10.1f} {max(sizes):<10.0f}")
    
    print(f"{'TOTAL':<20} {len(all_sizes):<8} {min(all_sizes):<10.0f} {np.median(all_sizes):<10.0f} "
          f"{np.mean(all_sizes):<10.1f} {max(all_sizes):<10.0f}")
    
    # Show outliers
    print(f"\n{'='*80}")
    print("SIZE OUTLIERS (>1000 configs)")
    print(f"{'='*80}")
    
    for cat, data in sizes_by_cat.items():
        outliers = [d for d in data if d['size'] > 1000]
        if outliers:
            print(f"\n{cat}:")
            for o in sorted(outliers, key=lambda x: x['size'], reverse=True):
                print(f"  {o['name']:<40} {o['size']:>6.0f} configs")
    
    return sizes_by_cat

def analyze_precision_by_size(results, sizes_by_cat):
    """Check if microbenchmarks have different precision characteristics."""
    
    print(f"\n{'='*80}")
    print("PRECISION BY PROGRAM SIZE (DMCFAR d=1, m=1)")
    print(f"{'='*80}")
    
    # Categorize by size
    size_map = {}
    for cat, data in sizes_by_cat.items():
        for d in data:
            full_name = None
            for r in results:
                if r['benchmarkName'].endswith(d['name']):
                    full_name = r['benchmarkName']
                    break
            if full_name:
                size_map[full_name] = d['size']
    
    # Collect precision data
    small = []  # <100 configs
    medium = []  # 100-500 configs
    large = []  # >500 configs
    
    for r in results:
        if r['variant'] == 'dmcfar' and r['d'] == 1 and r['m'] == 1:
            if r.get('isTimeout') or not r.get('storeMetrics'):
                continue
            
            bench = r['benchmarkName']
            size = size_map.get(bench, 0)
            if size == 0:
                continue
            
            m = r['storeMetrics']
            num_struct = m.get('numStructAddresses', 0)
            num_cont = m.get('numContAddresses', 0)
            
            if num_struct > 0 and num_cont > 0:
                val_prec = m.get('valStrSingletons', 0) / num_struct
                cont_prec = m.get('contStrSingletons', 0) / num_cont
                time = np.mean(r.get('analysisTimes', [0]))
                
                data_point = {
                    'val': val_prec,
                    'cont': cont_prec,
                    'time': time,
                    'name': bench.split('/')[-1]
                }
                
                if size < 100:
                    small.append(data_point)
                elif size < 500:
                    medium.append(data_point)
                else:
                    large.append(data_point)
    
    print(f"\n{'Size Range':<20} {'Count':<8} {'Val Prec':<12} {'Cont Prec':<12} {'Med Time (s)':<12}")
    print("-"*80)
    
    for label, data in [('Small (<100)', small), ('Medium (100-500)', medium), ('Large (>500)', large)]:
        if data:
            val_precs = [d['val'] for d in data]
            cont_precs = [d['cont'] for d in data]
            times = [d['time'] for d in data]
            
            print(f"{label:<20} {len(data):<8} {np.mean(val_precs)*100:>10.1f}% "
                  f"{np.mean(cont_precs)*100:>10.1f}% {np.median(times):>10.4f}s")
    
    # Check if small benchmarks bias results
    all_data = small + medium + large
    all_val = np.mean([d['val'] for d in all_data]) * 100
    all_cont = np.mean([d['cont'] for d in all_data]) * 100
    
    print(f"{'OVERALL (all sizes)':<20} {len(all_data):<8} {all_val:>10.1f}% {all_cont:>10.1f}%")
    
    # Without small benchmarks
    no_small = medium + large
    if no_small:
        no_small_val = np.mean([d['val'] for d in no_small]) * 100
        no_small_cont = np.mean([d['cont'] for d in no_small]) * 100
        
        print(f"{'EXCL. SMALL (<100)':<20} {len(no_small):<8} {no_small_val:>10.1f}% {no_small_cont:>10.1f}%")
        print(f"\n⚠️  BIAS ANALYSIS:")
        print(f"    Value precision changes by: {no_small_val - all_val:+.1f} pp")
        print(f"    Cont precision changes by:  {no_small_cont - all_cont:+.1f} pp")
        
        if abs(no_small_val - all_val) > 1 or abs(no_small_cont - all_cont) > 1:
            print(f"    → Small benchmarks have >1pp effect on aggregate precision")
        else:
            print(f"    → Small benchmarks have minimal effect (<1pp) on aggregate precision")

def analyze_timing_bias(results, sizes_by_cat):
    """Check if microbenchmarks bias timing statistics."""
    
    print(f"\n{'='*80}")
    print("TIMING STATISTICS BIAS ANALYSIS (DMCFAR d=1, m=1)")
    print(f"{'='*80}")
    
    # Get sizes
    size_map = {}
    for cat, data in sizes_by_cat.items():
        for d in data:
            for r in results:
                if r['benchmarkName'].endswith(d['name']):
                    size_map[r['benchmarkName']] = d['size']
                    break
    
    # Collect timing data
    times_small = []
    times_all = []
    
    for r in results:
        if r['variant'] == 'dmcfar' and r['d'] == 1 and r['m'] == 1:
            if r.get('isTimeout') or not r.get('analysisTimes'):
                continue
            
            bench = r['benchmarkName']
            size = size_map.get(bench, 0)
            time = np.mean(r['analysisTimes'])
            
            times_all.append(time)
            if size < 100:
                times_small.append(time)
    
    times_medium_large = [t for t in times_all if t not in times_small]
    
    print(f"\n{'Dataset':<25} {'Count':<8} {'Mean':<12} {'Median':<12} {'Max':<12}")
    print("-"*80)
    print(f"{'All benchmarks':<25} {len(times_all):<8} {np.mean(times_all):>10.4f}s "
          f"{np.median(times_all):>10.4f}s {max(times_all):>10.4f}s")
    print(f"{'Small only (<100)':<25} {len(times_small):<8} {np.mean(times_small):>10.4f}s "
          f"{np.median(times_small):>10.4f}s {max(times_small):>10.4f}s")
    if times_medium_large:
        print(f"{'Medium+Large (≥100)':<25} {len(times_medium_large):<8} {np.mean(times_medium_large):>10.4f}s "
              f"{np.median(times_medium_large):>10.4f}s {max(times_medium_large):>10.4f}s")
    
    # Check for outliers
    print(f"\n{'='*80}")
    print("TIMING OUTLIERS (>10s at d=1,m=1)")
    print(f"{'='*80}")
    
    outliers = []
    for r in results:
        if r['variant'] == 'dmcfar' and r['d'] == 1 and r['m'] == 1:
            if not r.get('isTimeout') and r.get('analysisTimes'):
                time = np.mean(r['analysisTimes'])
                if time > 10:
                    size = size_map.get(r['benchmarkName'], 0)
                    cat = categorize_benchmark(r['benchmarkName'])
                    outliers.append({
                        'name': r['benchmarkName'].split('/')[-1],
                        'time': time,
                        'size': size,
                        'cat': cat
                    })
    
    if outliers:
        outliers.sort(key=lambda x: x['time'], reverse=True)
        print(f"\n{'Benchmark':<40} {'Time (s)':<12} {'Size':<10} {'Category'}")
        print("-"*80)
        for o in outliers:
            print(f"{o['name']:<40} {o['time']:>10.2f}s {o['size']:>8.0f} {o['cat']}")
    else:
        print("\nNo timing outliers found (all <10s).")
    
    # Arithmetic mean vs geometric mean
    print(f"\n{'='*80}")
    print("ARITHMETIC MEAN vs GEOMETRIC MEAN vs MEDIAN")
    print(f"{'='*80}")
    
    arith_mean = np.mean(times_all)
    geom_mean = gmean([t for t in times_all if t > 0])
    median = np.median(times_all)
    
    print(f"\nAll benchmarks (n={len(times_all)}):")
    print(f"  Arithmetic Mean: {arith_mean:.4f}s")
    print(f"  Geometric Mean:  {geom_mean:.4f}s")
    print(f"  Median:          {median:.4f}s")
    print(f"\n  Arith/Geom ratio: {arith_mean/geom_mean:.2f}x")
    
    if arith_mean / geom_mean > 2:
        print(f"\n  ⚠️  WARNING: Arithmetic mean is {arith_mean/geom_mean:.1f}× larger than geometric mean")
        print(f"      This suggests RIGHT-SKEWED distribution (outliers inflating the mean)")
        print(f"      → Use MEDIAN or GEOMETRIC MEAN for central tendency, not arithmetic mean")
    else:
        print(f"\n  ✓ Ratio is reasonable (<2×); arithmetic mean is OK")

def check_aggregation_methodology(results):
    """Check current aggregation methodology."""
    
    print(f"\n{'='*80}")
    print("CURRENT AGGREGATION METHODOLOGY REVIEW")
    print(f"{'='*80}")
    
    print("""
Current approach in extract_paper_stats.py:
    
1. Precision (lines 106-108):
   - Uses np.mean() (arithmetic mean) across all benchmarks
   - Treats all benchmarks equally regardless of size
   - No weighting by program complexity
   
2. Timing (lines 162-164):
   - Absolute times: np.mean() (arithmetic mean)
   - Relative times: gmean() (geometric mean) ✓ CORRECT
   - Median also reported ✓ GOOD
   
3. No exclusions:
   - Microbenchmarks (<100 configs) included
   - All categories weighted equally
   - No outlier filtering

RECOMMENDATIONS:
""")

def main():
    print("Loading results...")
    results = load_all_results()
    print(f"Loaded {len(results)} results.\n")
    
    # Analyze size distribution
    sizes_by_cat = analyze_size_distribution(results)
    
    # Check precision bias
    analyze_precision_by_size(results, sizes_by_cat)
    
    # Check timing bias
    analyze_timing_bias(results, sizes_by_cat)
    
    # Review methodology
    check_aggregation_methodology(results)
    
    print(f"\n{'='*80}")
    print("RECOMMENDATIONS")
    print(f"{'='*80}")
    print("""
1. PRECISION METRICS:
   - Current arithmetic mean is OK IF small benchmarks don't bias results
   - Consider REPORTING BOTH:
     * Overall (all benchmarks)
     * By size category (small/medium/large)
     * By benchmark category (micro/standard/handlers/rosetta)
   
2. TIMING METRICS:
   - Arithmetic mean is SUSCEPTIBLE to outliers
   - Already using geometric mean for relative times ✓
   - PRIORITIZE MEDIAN over mean for reporting
   - Report geometric mean alongside arithmetic mean
   
3. AGGREGATION STRATEGY:
   - If small benchmarks bias results significantly (>2pp difference):
     → Report separately OR exclude from main claims
   - If timing outliers exist:
     → Report median as primary metric
     → Report geometric mean as secondary
     → Mention arithmetic mean with caveat about skew
   
4. WHAT TO REPORT:
   GOOD: "Median analysis time: 0.003s"
   GOOD: "Geometric mean overhead: 1.24×"
   RISKY: "Mean analysis time: 1.29s" (if heavily skewed by outliers)
   
5. SIZE FILTERING:
   - Consider excluding benchmarks <100 configs if:
     * They dominate the sample (>50%)
     * They have systematically different characteristics
     * You want to focus on "realistic" programs
   - If excluding, be TRANSPARENT: "excluding microbenchmarks <100 configs"
""")

if __name__ == '__main__':
    main()
