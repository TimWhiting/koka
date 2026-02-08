#!/usr/bin/env python3
"""
Compare old results (benchmarks/old-results/) with new results (benchmarks/results/)
to identify any differences beyond the new metrics added.
"""

import json
import os
import numpy as np
from collections import defaultdict

def load_results(root_path):
    """Load all results from a directory."""
    all_results = {}
    
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
                                # Create unique key
                                bench_name = data.get('benchmarkName', '')
                                key = (variant, int(d), int(m), bench_name)
                                all_results[key] = data
                        except (json.JSONDecodeError, ValueError):
                            pass
    
    return all_results

def compare_metrics(old_val, new_val, metric_name):
    """Compare two metric values and return difference info."""
    if old_val is None or new_val is None:
        return None
    
    if isinstance(old_val, (int, float)) and isinstance(new_val, (int, float)):
        if old_val == 0 and new_val == 0:
            return {'type': 'same', 'diff': 0, 'pct': 0}
        
        diff = new_val - old_val
        if old_val != 0:
            pct = 100 * diff / old_val
        else:
            pct = float('inf') if new_val > 0 else 0
        
        return {'type': 'numeric', 'old': old_val, 'new': new_val, 'diff': diff, 'pct': pct}
    elif isinstance(old_val, bool) and isinstance(new_val, bool):
        return {'type': 'bool', 'old': old_val, 'new': new_val, 'changed': old_val != new_val}
    elif isinstance(old_val, list) and isinstance(new_val, list):
        # For timing arrays
        if len(old_val) > 0 and len(new_val) > 0:
            old_mean = np.mean(old_val)
            new_mean = np.mean(new_val)
            diff = new_mean - old_mean
            pct = 100 * diff / old_mean if old_mean > 0 else 0
            return {'type': 'array', 'old_mean': old_mean, 'new_mean': new_mean, 
                    'old_len': len(old_val), 'new_len': len(new_val), 'diff': diff, 'pct': pct}
    
    return None

def main():
    print("Loading old results...")
    old_results = load_results("benchmarks/old-results")
    print(f"  Found {len(old_results)} results")
    
    print("Loading new results...")
    new_results = load_results("benchmarks/results")
    print(f"  Found {len(new_results)} results")
    
    # Find common and missing benchmarks
    old_keys = set(old_results.keys())
    new_keys = set(new_results.keys())
    
    common_keys = old_keys & new_keys
    only_old = old_keys - new_keys
    only_new = new_keys - old_keys
    
    print(f"\n{'='*80}")
    print("BENCHMARK COVERAGE")
    print(f"{'='*80}")
    print(f"Common benchmarks:     {len(common_keys)}")
    print(f"Only in old:           {len(only_old)}")
    print(f"Only in new:           {len(only_new)}")
    
    if only_old:
        print(f"\nMissing from new results (first 10):")
        for key in sorted(only_old)[:10]:
            variant, d, m, bench = key
            print(f"  {variant} ({d},{m}) - {bench.split('/')[-1]}")
    
    if only_new:
        print(f"\nNew benchmarks not in old (first 10):")
        for key in sorted(only_new)[:10]:
            variant, d, m, bench = key
            print(f"  {variant} ({d},{m}) - {bench.split('/')[-1]}")
    
    # Compare common benchmarks
    print(f"\n{'='*80}")
    print("COMPARING COMMON BENCHMARKS")
    print(f"{'='*80}\n")
    
    # Metrics to compare
    top_level_metrics = ['isTimeout', 'analysisTimes']
    store_metrics = [
        'numStoreAddresses',
        'numLitAddresses', 
        'numStructAddresses',
        'numContAddresses',
        'numIndirectCallTargetExprs',
        'numTotalFixInputStates',
        'valSemSingletons',
        'contSemSingletons',
        'valStrSingletons',
        'contStrSingletons',
        'semReturnSingletons',
        'strReturnSingletons',
        'semTargetSingletons',
        'strTargetSingletons',
        'literalTopCount',
    ]
    
    # Collect differences
    significant_diffs = defaultdict(list)
    timeout_changes = []
    timing_changes = []
    
    for key in sorted(common_keys):
        old = old_results[key]
        new = new_results[key]
        variant, d, m, bench = key
        bench_short = bench.split('/')[-1]
        
        # Check timeout changes
        old_timeout = old.get('isTimeout', False)
        new_timeout = new.get('isTimeout', False)
        if old_timeout != new_timeout:
            timeout_changes.append({
                'key': key,
                'bench': bench_short,
                'old': old_timeout,
                'new': new_timeout
            })
        
        # Check timing changes
        old_times = old.get('analysisTimes', [])
        new_times = new.get('analysisTimes', [])
        if old_times and new_times:
            old_mean = np.mean(old_times)
            new_mean = np.mean(new_times)
            if old_mean > 0:
                pct_change = 100 * (new_mean - old_mean) / old_mean
                if abs(pct_change) > 20:  # >20% change
                    timing_changes.append({
                        'key': key,
                        'bench': bench_short,
                        'old_mean': old_mean,
                        'new_mean': new_mean,
                        'pct': pct_change
                    })
        
        # Check store metrics
        old_store = old.get('storeMetrics')
        new_store = new.get('storeMetrics')
        
        if old_store and new_store:
            for metric in store_metrics:
                old_val = old_store.get(metric)
                new_val = new_store.get(metric)
                
                if old_val is not None and new_val is not None:
                    if old_val != new_val:
                        diff_pct = 0
                        if isinstance(old_val, (int, float)) and old_val > 0:
                            diff_pct = 100 * (new_val - old_val) / old_val
                        
                        if abs(diff_pct) > 1:  # >1% change
                            significant_diffs[metric].append({
                                'key': key,
                                'bench': bench_short,
                                'old': old_val,
                                'new': new_val,
                                'diff': new_val - old_val,
                                'pct': diff_pct
                            })
    
    # Report timeout changes
    if timeout_changes:
        print(f"TIMEOUT CHANGES: {len(timeout_changes)} benchmarks")
        print("-" * 80)
        for item in timeout_changes[:20]:
            variant, d, m, bench = item['key']
            status = "NEW TIMEOUT" if item['new'] else "FIXED"
            print(f"  {status}: {variant} ({d},{m}) - {item['bench']}")
        print()
    else:
        print("✓ No timeout changes\n")
    
    # Report timing changes
    if timing_changes:
        print(f"SIGNIFICANT TIMING CHANGES (>20%): {len(timing_changes)} benchmarks")
        print("-" * 80)
        timing_changes.sort(key=lambda x: abs(x['pct']), reverse=True)
        print(f"{'Benchmark':<40} {'Variant':<15} {'Old (s)':<10} {'New (s)':<10} {'Change':<10}")
        print("-" * 80)
        for item in timing_changes[:20]:
            variant, d, m, bench = item['key']
            config = f"{variant} ({d},{m})"
            print(f"{item['bench']:<40} {config:<15} {item['old_mean']:>8.4f}s {item['new_mean']:>8.4f}s {item['pct']:>+8.1f}%")
        print()
    else:
        print("✓ No significant timing changes (>20%)\n")
    
    # Report metric changes
    if significant_diffs:
        print(f"METRIC CHANGES (>1%)")
        print("-" * 80)
        for metric, diffs in sorted(significant_diffs.items()):
            if len(diffs) > 0:
                print(f"\n{metric}: {len(diffs)} benchmarks changed")
                # Show a few examples
                diffs.sort(key=lambda x: abs(x['pct']), reverse=True)
                for item in diffs[:5]:
                    variant, d, m, bench = item['key']
                    print(f"  {variant} ({d},{m}) - {item['bench']:<40} {item['old']:>6} → {item['new']:>6} ({item['pct']:>+6.1f}%)")
        print()
    else:
        print("✓ No significant metric changes (>1%)\n")
    
    # Summary statistics
    print(f"{'='*80}")
    print("SUMMARY")
    print(f"{'='*80}")
    print(f"Total benchmarks compared:     {len(common_keys)}")
    print(f"Timeout changes:               {len(timeout_changes)}")
    print(f"Timing changes (>20%):         {len(timing_changes)}")
    print(f"Metrics with changes (>1%):    {len([m for m in significant_diffs if significant_diffs[m]])}")
    
    # Overall timing comparison
    all_old_times = []
    all_new_times = []
    for key in common_keys:
        old_times = old_results[key].get('analysisTimes', [])
        new_times = new_results[key].get('analysisTimes', [])
        if old_times and new_times:
            all_old_times.append(np.mean(old_times))
            all_new_times.append(np.mean(new_times))
    
    if all_old_times and all_new_times:
        print(f"\nOverall timing statistics (n={len(all_old_times)}):")
        print(f"  Old median: {np.median(all_old_times):.4f}s")
        print(f"  New median: {np.median(all_new_times):.4f}s")
        print(f"  Old mean:   {np.mean(all_old_times):.4f}s")
        print(f"  New mean:   {np.mean(all_new_times):.4f}s")
        
        pct_changes = [100*(n-o)/o for o, n in zip(all_old_times, all_new_times) if o > 0]
        if pct_changes:
            print(f"  Median timing change: {np.median(pct_changes):+.1f}%")
    
    print(f"\n{'='*80}")
    print("NEW METRICS IN NEW RESULTS")
    print(f"{'='*80}")
    
    # Check what metrics are new
    if common_keys:
        sample_key = list(common_keys)[0]
        old_store = old_results[sample_key].get('storeMetrics', {})
        new_store = new_results[sample_key].get('storeMetrics', {})
        
        old_metrics = set(old_store.keys())
        new_metrics = set(new_store.keys())
        
        added_metrics = new_metrics - old_metrics
        removed_metrics = old_metrics - new_metrics
        
        if added_metrics:
            print(f"\nAdded metrics ({len(added_metrics)}):")
            for m in sorted(added_metrics):
                print(f"  - {m}")
        
        if removed_metrics:
            print(f"\nRemoved metrics ({len(removed_metrics)}):")
            for m in sorted(removed_metrics):
                print(f"  - {m}")
        
        if not added_metrics and not removed_metrics:
            print("\nNo new or removed metrics (same set of metrics in both)")

if __name__ == '__main__':
    main()
