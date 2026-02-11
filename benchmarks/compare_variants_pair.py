#!/usr/bin/env python3
"""
Compare results/*2 variants against their base variants.
Ignores small timing differences.
"""

import json
import os
from collections import defaultdict

def load_all_results(root_path="benchmarks/results"):
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
                                    'd': d,
                                    'm': m,
                                    'benchmarkName': data.get('benchmarkName', f_name.replace('.json', ''))
                                })
                                all_results.append(data)
                        except (json.JSONDecodeError, ValueError):
                            pass
    return all_results

def compare_metrics(m1, m2, path=""):
    diffs = []
    
    if isinstance(m1, dict) and isinstance(m2, dict):
        keys = set(m1.keys()) | set(m2.keys())
        for k in keys:
            if k not in m1:
                diffs.append(f"{path}.{k}: Missing in base")
            elif k not in m2:
                diffs.append(f"{path}.{k}: Missing in variant2")
            else:
                diffs.extend(compare_metrics(m1[k], m2[k], f"{path}.{k}" if path else k))
    elif isinstance(m1, list) and isinstance(m2, list):
        if len(m1) != len(m2):
             diffs.append(f"{path}: Length mismatch ({len(m1)} vs {len(m2)})")
        else:
            for i, (v1, v2) in enumerate(zip(m1, m2)):
                diffs.extend(compare_metrics(v1, v2, f"{path}[{i}]"))
    else:
        if m1 != m2:
            if isinstance(m1, (int, float)) and isinstance(m2, (int, float)):
                # Handle potential floating point issues if they ever appear in metrics
                if abs(m1 - m2) > 1e-9:
                    diffs.append(f"{path}: {m1} != {m2}")
            else:
                diffs.append(f"{path}: {m1} != {m2}")
    
    return diffs

def main():
    print("Loading results...")
    results = load_all_results()
    print(f"Loaded {len(results)} results.")

    # Group results by (benchmarkName, d, m)
    grouped = {}
    for r in results:
        key = (r['benchmarkName'], r['d'], r['m'])
        if key not in grouped:
            grouped[key] = {}
        grouped[key][r['variant']] = r

    # Find variants ending in '2'
    comparisons = []
    variants = set(r['variant'] for r in results)
    v2_variants = [v for v in variants if v.endswith('2')]
    
    for v2 in v2_variants:
        base_v = v2[:-1]
        if base_v in variants:
            comparisons.append((base_v, v2))
    
    if not comparisons:
        print("No variants ending in '2' found with a corresponding base variant.")
        return

    print(f"Comparing variant pairs: {', '.join([f'{b} vs {v}' for b, v in comparisons])}")
    print("-" * 80)

    total_diffs = 0
    timing_threshold_rel = 0.10 # 10%
    timing_threshold_abs = 0.05 # 50ms

    for base_v, v2 in comparisons:
        print(f"\nComparing {base_v} and {v2}:")
        v_diffs_found = 0
        
        # Trend tracking: metric_name -> {'inc': count, 'dec': count, 'same': count}
        trends = defaultdict(lambda: {'inc': 0, 'dec': 0, 'same': 0})
        precise_result_changes = []

        for key, variants_data in grouped.items():
            bench, d, m = key
            if base_v in variants_data and v2 in variants_data:
                r1 = variants_data[base_v]
                r2 = variants_data[v2]
                
                # Compare metrics
                m1 = r1.get('storeMetrics') or {}
                m2 = r2.get('storeMetrics') or {}
                
                # Check preciseResult
                p1 = r1.get('preciseResult') if r1.get('preciseResult') is not None else m1.get('preciseResult')
                p2 = r2.get('preciseResult') if r2.get('preciseResult') is not None else m2.get('preciseResult')
                if p1 != p2:
                    precise_result_changes.append(f"  Benchmark: {bench} (d={d}, m={m}): {p1} -> {p2}")

                metric_diffs = compare_metrics(m1, m2)
                
                # Update trends for top-level numeric metrics in storeMetrics
                all_metrics_keys = set(m1.keys()) | set(m2.keys())
                for mk in all_metrics_keys:
                    v1 = m1.get(mk)
                    v2_val = m2.get(mk)
                    if isinstance(v1, (int, float)) and isinstance(v2_val, (int, float)):
                        if v2_val > v1:
                            trends[mk]['inc'] += 1
                        elif v2_val < v1:
                            trends[mk]['dec'] += 1
                        else:
                            trends[mk]['same'] += 1

                # Compare timing
                t1_list = r1.get('analysisTimes', [])
                t2_list = r2.get('analysisTimes', [])
                
                t_diffs = []
                if t1_list and t2_list:
                    avg1 = sum(t1_list) / len(t1_list)
                    avg2 = sum(t2_list) / len(t2_list)
                    
                    if avg1 > 0:
                        rel_diff = abs(avg1 - avg2) / avg1
                        if rel_diff > timing_threshold_rel and abs(avg1 - avg2) > timing_threshold_abs:
                            t_diffs.append(f"Timing: {avg1:.4f}s vs {avg2:.4f}s ({rel_diff*100:.1f}% diff)")
                
                # Report individual differences (optional, maybe too verbose if there are many)
                if metric_diffs or t_diffs:
                    v_diffs_found += 1
                    total_diffs += 1
                    # print(f"  Benchmark: {bench} (d={d}, m={m})")
                    # for d_msg in metric_diffs:
                    #     print(f"    - METRIC: {d_msg}")
                    # for d_msg in t_diffs:
                    #     print(f"    - TIME:   {d_msg}")

        print(f"  Total benchmarks compared: {len([k for k in grouped if base_v in grouped[k] and v2 in grouped[k]])}")
        print(f"  Total benchmarks with differences: {v_diffs_found}")
        
        if precise_result_changes:
            print("\n  preciseResult Changes:")
            for msg in precise_result_changes:
                print(msg)
        else:
            print("\n  No preciseResult changes found.")

        if trends:
            print("\n  Top-level Metric Trends (Increase / Decrease / Same):")
            # Sort by number of changes (inc + dec)
            sorted_trends = sorted(trends.items(), key=lambda x: x[1]['inc'] + x[1]['dec'], reverse=True)
            for mk, counts in sorted_trends:
                if counts['inc'] > 0 or counts['dec'] > 0:
                    print(f"    {mk:<30}: {counts['inc']:>4} ↑ / {counts['dec']:>4} ↓ / {counts['same']:>4} =")

    print("\n" + "=" * 80)
    print(f"Analysis complete. Total discrepancies (individual benchmarks) found: {total_diffs}")

if __name__ == "__main__":
    main()
