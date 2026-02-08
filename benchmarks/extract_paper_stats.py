#!/usr/bin/env python3
"""
Extract concrete statistics for the paper's evaluation section.
Generates tables and numbers ready for LaTeX/Markdown.
"""

import json
import os
import numpy as np
import pandas as pd
from scipy.stats import gmean
from collections import defaultdict

def load_all_results(root_path="benchmarks/old-results"):
    """Load all benchmark results from the hierarchical structure."""
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

def categorize_benchmark(name):
    """Categorize benchmark by path."""
    if '/suite/' in name:
        return 'Microbenchmarks'
    elif '/koka-gen/' in name:
        return 'Koka Standard'
    elif '/rosetta/' in name:
        return 'Rosetta Code'
    elif '/handlers/' in name:
        return 'Handler Examples'
    return 'Other'

def compute_precision_stats(results):
    """Compute precision statistics by category and configuration."""
    
    # Group by variant, config, and category
    grouped = defaultdict(list)
    
    for r in results:
        if r.get('isTimeout') or not r.get('storeMetrics'):
            continue
        
        variant = r['variant']
        config = r['config']
        category = categorize_benchmark(r['benchmarkName'])
        m = r['storeMetrics']
        
        # Compute precision metrics
        num_struct = m.get('numStructAddresses', 0)
        if num_struct > 0:
            val_str_prec = m.get('valStrSingletons', 0) / num_struct
            val_sem_prec = m.get('valSemSingletons', 0) / num_struct
        else:
            val_str_prec = val_sem_prec = 0
        
        num_cont = m.get('numContAddresses', 0)
        if num_cont > 0:
            cont_prec = m.get('contStrSingletons', 0) / num_cont
        else:
            cont_prec = 0
        
        key = (variant, config, category)
        grouped[key].append({
            'val_str_prec': val_str_prec,
            'val_sem_prec': val_sem_prec,
            'cont_prec': cont_prec,
            'expansion': m.get('numStoreAddresses', 0),
            'time': np.mean(r.get('analysisTimes', [0]))
        })
    
    # Aggregate statistics
    stats = []
    for (variant, config, category), data_list in grouped.items():
        if not data_list:
            continue
        
        stats.append({
            'Variant': variant.upper(),
            'Config': config,
            'Category': category,
            'Count': len(data_list),
            'Val Str Prec (%)': np.mean([d['val_str_prec'] for d in data_list]) * 100,
            'Val Sem Prec (%)': np.mean([d['val_sem_prec'] for d in data_list]) * 100,
            'Cont Prec (%)': np.mean([d['cont_prec'] for d in data_list]) * 100,
            'Avg Time (s)': np.mean([d['time'] for d in data_list]),
        })
    
    return pd.DataFrame(stats)

def compute_scalability_stats(results):
    """Compute scalability statistics."""
    
    # Get baseline (0-0) times
    baselines = {}
    for r in results:
        if r['d'] == 0 and r['m'] == 0 and not r.get('isTimeout'):
            bench = r['benchmarkName']
            baselines[bench] = np.mean(r.get('analysisTimes', [0]))
    
    # Compute relative times
    scalability = defaultdict(list)
    
    for r in results:
        if r.get('isTimeout') or not r.get('analysisTimes'):
            continue
        
        bench = r['benchmarkName']
        variant = r['variant']
        config = r['config']
        
        time = np.mean(r['analysisTimes'])
        baseline_time = baselines.get(bench, time)
        
        if baseline_time > 0:
            rel_time = time / baseline_time
        else:
            rel_time = 1.0
        
        key = (variant, config)
        scalability[key].append({
            'time': time,
            'rel_time': rel_time
        })
    
    # Aggregate
    stats = []
    for (variant, config), data_list in scalability.items():
        if not data_list:
            continue
        
        times = [d['time'] for d in data_list]
        rel_times = [d['rel_time'] for d in data_list if d['rel_time'] > 0]
        
        stats.append({
            'Variant': variant.upper(),
            'Config': config,
            'Count': len(data_list),
            'Mean Time (s)': np.mean(times),
            'Median Time (s)': np.median(times),
            'Geom Mean Speedup': gmean(rel_times) if rel_times else 1.0,
        })
    
    return pd.DataFrame(stats)

def count_benchmarks_by_category(results):
    """Count unique benchmarks by category."""
    benchmarks_by_cat = defaultdict(set)
    
    for r in results:
        bench = r['benchmarkName']
        cat = categorize_benchmark(bench)
        benchmarks_by_cat[cat].add(bench)
    
    print("\n" + "="*60)
    print("BENCHMARK SUITE COMPOSITION")
    print("="*60)
    
    total = 0
    for cat in sorted(benchmarks_by_cat.keys()):
        count = len(benchmarks_by_cat[cat])
        total += count
        print(f"{cat:20s}: {count:3d} benchmarks")
    
    print(f"{'TOTAL':20s}: {total:3d} benchmarks")
    print("="*60)

def precision_table_by_config(results):
    """Generate precision table suitable for paper."""
    
    # Select key configurations
    configs = ['0-0', '1-0', '1-1', '2-2']
    variants = ['kcfa', 'dmcfar', 'dmcfae']
    
    print("\n" + "="*80)
    print("TABLE 1: PRECISION BY CONFIGURATION (Average across all benchmarks)")
    print("="*80)
    
    # Create pivot table
    pivot_data = []
    
    for variant in variants:
        for config in configs:
            # Collect data
            val_str_precs = []
            cont_precs = []
            
            for r in results:
                if (r['variant'] == variant and 
                    r['config'] == config and 
                    not r.get('isTimeout') and 
                    r.get('storeMetrics')):
                    
                    m = r['storeMetrics']
                    num_struct = m.get('numStructAddresses', 0)
                    if num_struct > 0:
                        val_str_precs.append(m.get('valStrSingletons', 0) / num_struct)
                    
                    num_cont = m.get('numContAddresses', 0)
                    if num_cont > 0:
                        cont_precs.append(m.get('contStrSingletons', 0) / num_cont)
            
            if val_str_precs:
                pivot_data.append({
                    'Analysis': variant.upper(),
                    'Config (d-m)': config if variant != 'kcfa' else f'k={config.split("-")[1]}',
                    'N': len(val_str_precs),
                    'Val Prec': f"{np.mean(val_str_precs)*100:.1f}%",
                    'Cont Prec': f"{np.mean(cont_precs)*100:.1f}%" if cont_precs else "N/A"
                })
    
    df = pd.DataFrame(pivot_data)
    print(df.to_string(index=False))
    print("="*80)
    
    return df

def timeout_summary(results):
    """Summarize timeouts."""
    print("\n" + "="*60)
    print("TIMEOUT SUMMARY (500s limit)")
    print("="*60)
    
    timeouts_by_config = defaultdict(int)
    total_by_config = defaultdict(int)
    
    for r in results:
        key = (r['variant'], r['config'])
        total_by_config[key] += 1
        if r.get('isTimeout'):
            timeouts_by_config[key] += 1
    
    timeout_list = []
    for key, timeout_count in sorted(timeouts_by_config.items()):
        variant, config = key
        total = total_by_config[key]
        pct = (timeout_count / total * 100) if total > 0 else 0
        timeout_list.append({
            'Variant': variant.upper(),
            'Config': config,
            'Timeouts': timeout_count,
            'Total': total,
            'Rate (%)': f"{pct:.1f}%"
        })
    
    if timeout_list:
        df = pd.DataFrame(timeout_list)
        print(df.to_string(index=False))
    else:
        print("No timeouts!")
    
    print("="*60)

def main():
    print("Loading benchmark results...")
    results = load_all_results()
    print(f"Loaded {len(results)} result files.")
    
    count_benchmarks_by_category(results)
    
    timeout_summary(results)
    
    precision_table_by_config(results)
    
    print("\n" + "="*80)
    print("TABLE 2: PRECISION BY CATEGORY AND CONFIGURATION")
    print("="*80)
    prec_stats = compute_precision_stats(results)
    
    # Filter for key configs and print nicely
    key_configs = ['0-0', '1-1', '2-2']
    for config in key_configs:
        subset = prec_stats[prec_stats['Config'] == config]
        if not subset.empty:
            print(f"\nConfiguration: {config}")
            print(subset[['Variant', 'Category', 'Count', 'Val Str Prec (%)', 'Cont Prec (%)']].to_string(index=False))
    
    print("="*80)
    
    print("\n" + "="*80)
    print("TABLE 3: SCALABILITY - RELATIVE TIME OVERHEAD")
    print("="*80)
    scale_stats = compute_scalability_stats(results)
    
    # Show key variants and configs
    for variant in ['KCFA', 'DMCFAR', 'DMCFAE']:
        subset = scale_stats[scale_stats['Variant'] == variant]
        if not subset.empty:
            print(f"\n{variant}:")
            print(subset[['Config', 'Count', 'Mean Time (s)', 'Geom Mean Speedup']].to_string(index=False))
    
    print("="*80)
    
    print("\n" + "="*60)
    print("KEY TAKEAWAYS FOR PAPER")
    print("="*60)
    
    # Compute overall averages for (1,1) config
    dmcfar_11 = [r for r in results if r['variant'] == 'dmcfar' and r['config'] == '1-1' and not r.get('isTimeout') and r.get('storeMetrics')]
    
    if dmcfar_11:
        val_precs = [r['storeMetrics']['valStrSingletons'] / r['storeMetrics']['numStructAddresses'] 
                     for r in dmcfar_11 if r['storeMetrics']['numStructAddresses'] > 0]
        cont_precs = [r['storeMetrics']['contStrSingletons'] / r['storeMetrics']['numContAddresses'] 
                      for r in dmcfar_11 if r['storeMetrics']['numContAddresses'] > 0]
        times = [np.mean(r['analysisTimes']) for r in dmcfar_11]
        
        print(f"\nDMCFAR at (d=1, m=1) - Recommended Configuration:")
        print(f"  - Benchmarks analyzed: {len(dmcfar_11)}")
        print(f"  - Average value precision: {np.mean(val_precs)*100:.1f}%")
        print(f"  - Average continuation precision: {np.mean(cont_precs)*100:.1f}%")
        print(f"  - Mean analysis time: {np.mean(times):.3f}s")
        print(f"  - Median analysis time: {np.median(times):.3f}s")
    
    # Compare to baseline
    dmcfar_00 = [r for r in results if r['variant'] == 'dmcfar' and r['config'] == '0-0' and not r.get('isTimeout') and r.get('storeMetrics')]
    
    if dmcfar_00:
        val_precs_base = [r['storeMetrics']['valStrSingletons'] / r['storeMetrics']['numStructAddresses'] 
                          for r in dmcfar_00 if r['storeMetrics']['numStructAddresses'] > 0]
        
        print(f"\nBaseline (d=0, m=0):")
        print(f"  - Average value precision: {np.mean(val_precs_base)*100:.1f}%")
        print(f"  - Improvement at (1,1): +{(np.mean(val_precs) - np.mean(val_precs_base))*100:.1f} percentage points")
    
    print("="*60)

if __name__ == '__main__':
    main()
