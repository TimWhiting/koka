#!/usr/bin/env python3
"""
Compare DMCFAR, DMCFAE, and k-CFA on same benchmarks.
Uses multiple continuation precision metrics to find the most reliable one.
"""

import json
import os
import numpy as np
from collections import defaultdict

def categorize_benchmark(name):
    if '/suite/' in name:
        return 'Microbenchmarks'
    elif '/koka-gen/' in name:
        return 'Koka Standard'
    elif '/handlers/' in name:
        return 'Handler Examples'
    elif '/rosetta/' in name:
        return 'Rosetta Code'
    return 'Other'

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
                                    'd': int(d),
                                    'm': int(m),
                                    'config': f"{d}-{m}"
                                })
                                all_results.append(data)
                        except (json.JSONDecodeError, ValueError):
                            pass
    return all_results

def get_program_sizes(results):
    """Get program sizes from KCFA 0-0."""
    sizes = {}
    for r in results:
        if r['variant'] == 'kcfa' and r['d'] == 0 and r['m'] == 0:
            if r.get('storeMetrics'):
                m = r['storeMetrics']
                total = m.get('numTotalFixInputStates', 0)
                store = m.get('numStoreAddresses', 0)
                size = total - store
                sizes[r['benchmarkName']] = size
    return sizes

def compute_metrics(sm):
    """Compute all available continuation precision metrics."""
    metrics = {}
    
    # Traditional context-sensitive metric
    num_cont = sm.get('numContAddresses', 0)
    cont_str_sing = sm.get('contStrSingletons', 0)
    metrics['trad_cont_prec'] = cont_str_sing / num_cont if num_cont > 0 else 0
    
    # 0-CFA aggregated metrics
    cont0cfa_sing = sm.get('cont0CFAStrSingletons', 0)
    cont_histogram = sm.get('contContextHistogram', {})
    num_0cfa_addrs = len(cont_histogram)  # unique 0-CFA addresses
    
    # Try different interpretations
    metrics['cont0cfa_over_hist'] = cont0cfa_sing / num_0cfa_addrs if num_0cfa_addrs > 0 else 0
    metrics['cont0cfa_over_total'] = cont0cfa_sing / num_cont if num_cont > 0 else 0
    
    # Value precision (for reference)
    num_struct = sm.get('numStructAddresses', 0)
    val_str_sing = sm.get('valStrSingletons', 0)
    metrics['val_prec'] = val_str_sing / num_struct if num_struct > 0 else 0
    
    # Store raw counts for analysis
    metrics['num_cont'] = num_cont
    metrics['cont0cfa_sing'] = cont0cfa_sing
    metrics['num_0cfa_addrs'] = num_0cfa_addrs
    metrics['cont_str_sing'] = cont_str_sing
    
    return metrics

def compare_configs(results, sizes, min_size=250):
    """Compare all configurations on programs >= min_size."""
    
    # Collect data by benchmark and config
    data = defaultdict(lambda: defaultdict(dict))
    
    for r in results:
        bench = r['benchmarkName']
        if bench not in sizes or sizes[bench] < min_size:
            continue
        
        if r.get('isTimeout') or not r.get('storeMetrics'):
            continue
        
        variant = r['variant']
        d = r['d']
        m = r['m']
        
        if variant == 'dmcfar':
            key = f"DMCFAR ({d},{m})"
        elif variant == 'dmcfae':
            key = f"DMCFAE ({d},{m})"
        elif variant == 'kcfa':
            key = f"k-CFA k={m}"
        else:
            continue
        
        metrics = compute_metrics(r['storeMetrics'])
        metrics['time'] = np.mean(r.get('analysisTimes', [0]))
        metrics['size'] = sizes[bench]
        metrics['category'] = categorize_benchmark(bench)
        
        data[bench][key] = metrics
    
    return data

def analyze_metric_validity(data):
    """Check which metric makes most sense by looking for anomalies."""
    
    print(f"\n{'='*80}")
    print("METRIC VALIDITY ANALYSIS")
    print(f"{'='*80}\n")
    
    # Check for values >100% in each metric
    for metric_name in ['trad_cont_prec', 'cont0cfa_over_hist', 'cont0cfa_over_total']:
        over_100 = []
        all_vals = []
        
        for bench, configs in data.items():
            for config, metrics in configs.items():
                val = metrics.get(metric_name, 0) * 100
                all_vals.append(val)
                if val > 100:
                    over_100.append((bench.split('/')[-1], config, val))
        
        print(f"{metric_name}:")
        print(f"  Range: {min(all_vals):.1f}% - {max(all_vals):.1f}%")
        print(f"  Values >100%: {len(over_100)}")
        if over_100 and len(over_100) <= 5:
            for b, c, v in over_100[:5]:
                print(f"    {b} @ {c}: {v:.1f}%")
        print()

def compare_head_to_head(data, config1, config2, metric='trad_cont_prec'):
    """Head-to-head comparison between two configs."""
    
    wins_1 = 0
    wins_2 = 0
    ties = 0
    improvements = []
    examples = []
    
    for bench, configs in data.items():
        if config1 in configs and config2 in configs:
            val1 = configs[config1].get(metric, 0) * 100
            val2 = configs[config2].get(metric, 0) * 100
            diff = val1 - val2
            
            if diff > 0.1:
                wins_1 += 1
            elif diff < -0.1:
                wins_2 += 1
            else:
                ties += 1
            
            improvements.append(diff)
            examples.append({
                'name': bench.split('/')[-1],
                'config1_val': val1,
                'config2_val': val2,
                'diff': diff,
                'size': configs[config1]['size']
            })
    
    return {
        'wins_1': wins_1,
        'wins_2': wins_2,
        'ties': ties,
        'mean_improvement': np.mean(improvements) if improvements else 0,
        'median_improvement': np.median(improvements) if improvements else 0,
        'examples': sorted(examples, key=lambda x: x['diff'], reverse=True),
        'n': len(improvements)
    }

def main():
    print("Loading results...")
    results = load_all_results()
    sizes = get_program_sizes(results)
    
    min_size = 250
    data = compare_configs(results, sizes, min_size=min_size)
    
    print(f"\nFiltered to {len(data)} programs with ≥{min_size} configurations")
    
    # Analyze which metric is most reliable
    analyze_metric_validity(data)
    
    # Use the traditional metric (most reliable based on above)
    metric = 'trad_cont_prec'
    
    print(f"\n{'='*80}")
    print(f"USING METRIC: {metric} (traditional context-sensitive precision)")
    print(f"{'='*80}\n")
    
    # Aggregate by configuration
    configs_of_interest = [
        ("DMCFAR (0,0)", "Baseline"),
        ("DMCFAR (1,1)", "DMCFAR recommended"),
        ("DMCFAR (2,2)", "DMCFAR high sensitivity"),
        ("DMCFAE (0,0)", "Baseline"),
        ("DMCFAE (1,1)", "DMCFAE recommended"),
        ("DMCFAE (2,2)", "DMCFAE high sensitivity"),
        ("k-CFA k=0", "Baseline"),
        ("k-CFA k=1", "k-CFA standard"),
        ("k-CFA k=2", "k-CFA high"),
    ]
    
    agg = defaultdict(lambda: {'val': [], 'cont': [], 'time': [], 'n': 0})
    
    for bench, configs in data.items():
        for config_name, _ in configs_of_interest:
            if config_name in configs:
                m = configs[config_name]
                agg[config_name]['val'].append(m['val_prec'])
                agg[config_name]['cont'].append(m[metric])
                agg[config_name]['time'].append(m['time'])
                agg[config_name]['n'] += 1
    
    print(f"{'Configuration':<25} {'N':<6} {'Val Prec':<12} {'Cont Prec':<12} {'Median Time':<12}")
    print("-"*80)
    
    for config, desc in configs_of_interest:
        if agg[config]['n'] > 0:
            val_mean = np.mean(agg[config]['val']) * 100
            cont_mean = np.mean(agg[config]['cont']) * 100
            time_median = np.median(agg[config]['time'])
            n = agg[config]['n']
            
            print(f"{config:<25} {n:<6} {val_mean:>10.1f}% {cont_mean:>10.1f}% {time_median:>10.4f}s")
    
    # Key comparisons
    print(f"\n{'='*80}")
    print("KEY COMPARISONS")
    print(f"{'='*80}\n")

    # --- Report cont0cfa_sing ratio over rebinding 0CFA ---
    print(f"\n{'='*80}")
    print("cont0cfa_sing relative to rebinding 0CFA (0,0) for each config:")
    print(f"{'='*80}\n")
    for config, desc in configs_of_interest:
        # Determine the matching rebinding 0CFA config for this variant
        if config.startswith("DMCFAR"):
            base_config = "DMCFAR (0,0)"
        elif config.startswith("DMCFAE"):
            base_config = "DMCFAE (0,0)"
        elif config.startswith("k-CFA"):
            base_config = "k-CFA k=0"
        else:
            continue
        ratios = []
        for bench, configs in data.items():
            if config in configs and base_config in configs:
                base_val = configs[base_config].get('cont0cfa_sing', 0)
                val = configs[config].get('cont0cfa_sing', 0)
                if base_val > 0:
                    ratios.append(val / base_val)
        if ratios:
            mean_ratio = np.mean(ratios)
            median_ratio = np.median(ratios)
            print(f"{config:<25} Mean: {mean_ratio:>7.3f}  Median: {median_ratio:>7.3f}  N={len(ratios)}")
        else:
            print(f"{config:<25} No data.")
    
    comparisons = [
        ("DMCFAR (1,1)", "k-CFA k=1", "DMCFAR vs k-CFA"),
        ("DMCFAE (1,1)", "k-CFA k=1", "DMCFAE vs k-CFA"),
        ("DMCFAE (1,1)", "DMCFAR (1,1)", "DMCFAE vs DMCFAR"),
        ("DMCFAR (2,2)", "k-CFA k=2", "DMCFAR high vs k-CFA high"),
        ("DMCFAE (2,2)", "k-CFA k=2", "DMCFAE high vs k-CFA high"),
    ]
    
    for config1, config2, desc in comparisons:
        if agg[config1]['n'] > 0 and agg[config2]['n'] > 0:
            result = compare_head_to_head(data, config1, config2, metric)
            
            print(f"{desc}:")
            print(f"  {config1}: {np.mean(agg[config1]['cont'])*100:.1f}% continuation precision")
            print(f"  {config2}: {np.mean(agg[config2]['cont'])*100:.1f}% continuation precision")
            print(f"  Head-to-head ({result['n']} programs):")
            print(f"    {config1} wins: {result['wins_1']} ({100*result['wins_1']/result['n']:.1f}%)")
            print(f"    {config2} wins: {result['wins_2']} ({100*result['wins_2']/result['n']:.1f}%)")
            print(f"    Ties: {result['ties']} ({100*result['ties']/result['n']:.1f}%)")
            print(f"    Mean improvement: {result['mean_improvement']:+.1f}pp")
            print(f"    Median improvement: {result['median_improvement']:+.1f}pp")
            
            # Show top improvements
            if result['examples']:
                print(f"  Top 3 improvements for {config1}:")
                for ex in result['examples'][:3]:
                    print(f"    {ex['name']:<40} {ex['diff']:>+6.1f}pp ({ex['config1_val']:.1f}% vs {ex['config2_val']:.1f}%)")
            print()

if __name__ == '__main__':
    main()
