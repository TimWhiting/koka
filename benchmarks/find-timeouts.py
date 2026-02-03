#!/usr/bin/env python3
"""
Find and analyze timeouts in benchmark results.
Helps identify which benchmarks and configurations are timing out.
"""

import json
import os
import pandas as pd
from collections import defaultdict

def load_results(root_path):
    """Loads results from results/variant/d/m hierarchy."""
    all_results = []
    print(f"Scanning {root_path}...")
    
    for root, dirs, files in os.walk(root_path):
        for f_name in files:
            if f_name.endswith('.json'):
                rel_path = os.path.relpath(root, root_path)
                parts = rel_path.split(os.sep)
                
                # Structure: variant/d/m/...
                if len(parts) >= 3:
                    variant = parts[0]
                    d = parts[1]
                    m = parts[2]
                    
                    file_path = os.path.join(root, f_name)
                    try:
                        if os.path.getsize(file_path) == 0:
                            continue
                        
                        with open(file_path, 'r') as f:
                            data = json.load(f)
                            
                        if isinstance(data, dict):
                            data.update({
                                'variant': variant,
                                'd': d,
                                'm': m,
                                'filePath': file_path
                            })
                            all_results.append(data)
                    except (json.JSONDecodeError, ValueError) as e:
                        print(f"Warning: Failed to decode {file_path}: {e}")
    
    print(f"Loaded {len(all_results)} result files.")
    return all_results

def analyze_timeouts(results):
    """Analyzes timeout patterns in the results."""
    timeouts = [r for r in results if r.get('isTimeout', False)]
    non_timeouts = [r for r in results if not r.get('isTimeout', False)]
    
    print(f"\n{'='*80}")
    print(f"TIMEOUT ANALYSIS")
    print(f"{'='*80}")
    print(f"Total results: {len(results)}")
    print(f"Timeouts: {len(timeouts)} ({100*len(timeouts)/len(results):.1f}%)")
    print(f"Successful: {len(non_timeouts)} ({100*len(non_timeouts)/len(results):.1f}%)")
    
    if not timeouts:
        print("\n✓ No timeouts found!")
        return
    
    # Group by benchmark
    by_benchmark = defaultdict(list)
    for t in timeouts:
        bench_name = t.get('benchmarkName', 'unknown')
        by_benchmark[bench_name].append(t)
    
    print(f"\n{'='*80}")
    print(f"TIMEOUTS BY BENCHMARK")
    print(f"{'='*80}")
    print(f"{'Benchmark':<40} {'Count':>8} {'Variants':>12}")
    print(f"{'-'*80}")
    
    for bench, items in sorted(by_benchmark.items(), key=lambda x: len(x[1]), reverse=True):
        variants = set(item['variant'] for item in items)
        print(f"{bench:<40} {len(items):>8} {', '.join(sorted(variants)):>12}")
    
    # Group by variant
    by_variant = defaultdict(list)
    for t in timeouts:
        variant = t.get('variant', 'unknown')
        by_variant[variant].append(t)
    
    print(f"\n{'='*80}")
    print(f"TIMEOUTS BY VARIANT")
    print(f"{'='*80}")
    print(f"{'Variant':<20} {'Count':>8} {'% of Variant':>15}")
    print(f"{'-'*80}")
    
    for variant in sorted(by_variant.keys()):
        items = by_variant[variant]
        variant_total = sum(1 for r in results if r.get('variant') == variant)
        pct = 100 * len(items) / variant_total if variant_total > 0 else 0
        print(f"{variant:<20} {len(items):>8} {pct:>14.1f}%")
    
    # Group by configuration (d, m)
    by_config = defaultdict(list)
    for t in timeouts:
        config = f"{t.get('d', '?')}-{t.get('m', '?')}"
        by_config[config].append(t)
    
    print(f"\n{'='*80}")
    print(f"TIMEOUTS BY CONFIGURATION (d-m)")
    print(f"{'='*80}")
    print(f"{'Config':>10} {'Count':>8} {'% of Config':>15}")
    print(f"{'-'*80}")
    
    for config in sorted(by_config.keys(), key=lambda x: [int(v) if v.isdigit() else 999 for v in x.split('-')]):
        items = by_config[config]
        d, m = config.split('-')
        config_total = sum(1 for r in results if str(r.get('d')) == d and str(r.get('m')) == m)
        pct = 100 * len(items) / config_total if config_total > 0 else 0
        print(f"{config:>10} {len(items):>8} {pct:>14.1f}%")
    
    # Detailed timeout list
    print(f"\n{'='*80}")
    print(f"DETAILED TIMEOUT LIST")
    print(f"{'='*80}")
    
    # Create DataFrame for easy viewing
    timeout_data = []
    for t in timeouts:
        timeout_data.append({
            'Benchmark': t.get('benchmarkName', 'unknown'),
            'Variant': t.get('variant', 'unknown'),
            'd': t.get('d', '?'),
            'm': t.get('m', '?'),
            'Config': f"{t.get('d', '?')}-{t.get('m', '?')}",
            'File': os.path.basename(t.get('filePath', 'unknown'))
        })
    
    if timeout_data:
        df = pd.DataFrame(timeout_data)
        df = df.sort_values(['Variant', 'Benchmark', 'd', 'm'])
        print(df.to_string(index=False))
        
        # Save to CSV for further analysis
        output_file = "benchmarks/analysis/timeouts.csv"
        os.makedirs(os.path.dirname(output_file), exist_ok=True)
        df.to_csv(output_file, index=False)
        print(f"\n✓ Detailed timeout list saved to: {output_file}")
    
    # Check if any benchmark ALWAYS times out
    print(f"\n{'='*80}")
    print(f"BENCHMARKS THAT ALWAYS TIMEOUT")
    print(f"{'='*80}")
    
    always_timeout = []
    for bench_name in by_benchmark.keys():
        bench_total = sum(1 for r in results if r.get('benchmarkName') == bench_name)
        bench_timeouts = len(by_benchmark[bench_name])
        if bench_timeouts == bench_total and bench_total > 0:
            always_timeout.append((bench_name, bench_total))
    
    if always_timeout:
        for bench, count in sorted(always_timeout, key=lambda x: x[1], reverse=True):
            print(f"  • {bench} ({count} configurations)")
    else:
        print("  (None - all benchmarks have at least some successful runs)")
    
    # Configurations that always timeout
    print(f"\n{'='*80}")
    print(f"CONFIGURATIONS THAT ALWAYS TIMEOUT")
    print(f"{'='*80}")
    
    config_always_timeout = []
    for config in by_config.keys():
        d, m = config.split('-')
        config_total = sum(1 for r in results if str(r.get('d')) == d and str(r.get('m')) == m)
        config_timeouts = len(by_config[config])
        if config_timeouts == config_total and config_total > 0:
            config_always_timeout.append((config, config_total))
    
    if config_always_timeout:
        for config, count in sorted(config_always_timeout, key=lambda x: [int(v) if v.isdigit() else 999 for v in x[0].split('-')]):
            print(f"  • {config} ({count} benchmarks)")
    else:
        print("  (None - all configurations have at least some successful runs)")

def main():
    results_path = "benchmarks/results"
    
    if not os.path.exists(results_path):
        print(f"Error: Path '{results_path}' does not exist.")
        return
    
    results = load_results(results_path)
    
    if not results:
        print("Error: No data found in benchmarks/results.")
        return
    
    analyze_timeouts(results)

if __name__ == "__main__":
    main()
