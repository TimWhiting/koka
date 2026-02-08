#!/usr/bin/env python3
"""
Compare DMCFAR to k-CFA on same benchmarks.
Focus on programs >=100 configs to avoid trivial examples.
"""

import json
import os
import numpy as np
from scipy.stats import gmean
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

def compare_configs(results, sizes, min_size=100):
    """Compare DMCFAR vs k-CFA on programs >= min_size."""
    
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
        
        # Compute metrics
        sm = r['storeMetrics']
        num_struct = sm.get('numStructAddresses', 0)
        
        # Use 0-CFA aggregated continuation precision (better metric for comparison)
        cont0cfa_singletons = sm.get('cont0CFAStrSingletons', 0)
        # Compute number of unique 0-CFA continuation addresses from histogram
        # contContextHistogram format: {num_contexts: count_of_continuations}
        cont_histogram = sm.get('contContextHistogram', {})
        num_0cfa_conts = sum(cont_histogram.values())  # Total unique 0-CFA continuation addresses
        
        val_prec = sm.get('valStrSingletons', 0) / num_struct if num_struct > 0 else 0
        cont_prec = cont0cfa_singletons / num_0cfa_conts if num_0cfa_conts > 0 else 0
        time = np.mean(r.get('analysisTimes', [0]))
        
        if variant == 'dmcfar':
            key = f"DMCFAR ({d},{m})"
        elif variant == 'kcfa':
            key = f"k-CFA k={m}"
        else:
            continue
        
        data[bench][key] = {
            'val': val_prec,
            'cont': cont_prec,
            'time': time,
            'size': sizes[bench],
            'category': categorize_benchmark(bench)
        }
    
    return data

def main():
    print("Loading results...")
    results = load_all_results()
    sizes = get_program_sizes(results)
    
    print(f"\n{'='*80}")
    print("k-CFA vs DMCFAR COMPARISON")
    print(f"{'='*80}")
    
    # Compare on programs >= 250 configs
    min_size = 250
    data = compare_configs(results, sizes, min_size=min_size)
    
    print(f"\nFiltered to {len(data)} programs with ≥{min_size} configurations")
    
    # Aggregate by configuration
    configs_of_interest = [
        "DMCFAR (0,0)",
        "DMCFAR (1,0)", 
        "DMCFAR (1,1)",
        "DMCFAR (2,2)",
        "k-CFA k=0",
        "k-CFA k=1",
        "k-CFA k=2",
    ]
    
    agg = defaultdict(lambda: {'val': [], 'cont': [], 'time': [], 'n': 0})
    
    for bench, configs in data.items():
        for config_name in configs_of_interest:
            if config_name in configs:
                d = configs[config_name]
                agg[config_name]['val'].append(d['val'])
                agg[config_name]['cont'].append(d['cont'])
                agg[config_name]['time'].append(d['time'])
                agg[config_name]['n'] += 1
    
    print(f"\n{'Configuration':<20} {'N':<6} {'Val Prec':<12} {'Cont Prec':<12} {'Median Time':<12}")
    print("-"*80)
    
    for config in configs_of_interest:
        if agg[config]['n'] > 0:
            val_mean = np.mean(agg[config]['val']) * 100
            cont_mean = np.mean(agg[config]['cont']) * 100
            time_median = np.median(agg[config]['time'])
            n = agg[config]['n']
            
            print(f"{config:<20} {n:<6} {val_mean:>10.1f}% {cont_mean:>10.1f}% {time_median:>10.4f}s")
    
    # Head-to-head comparison
    print(f"\n{'='*80}")
    print("HEAD-TO-HEAD: DMCFAR (1,1) vs k-CFA k=1")
    print(f"{'='*80}")
    
    # Find benchmarks with both
    both = []
    for bench, configs in data.items():
        if "DMCFAR (1,1)" in configs and "k-CFA k=1" in configs:
            both.append({
                'name': bench.split('/')[-1],
                'size': configs["DMCFAR (1,1)"]['size'],
                'dmcfar_cont': configs["DMCFAR (1,1)"]['cont'] * 100,
                'kcfa_cont': configs["k-CFA k=1"]['cont'] * 100,
                'improvement': (configs["DMCFAR (1,1)"]['cont'] - configs["k-CFA k=1"]['cont']) * 100,
                'dmcfar_time': configs["DMCFAR (1,1)"]['time'],
                'kcfa_time': configs["k-CFA k=1"]['time'],
            })
    
    print(f"\n{len(both)} benchmarks have both DMCFAR (1,1) and k-CFA k=1 results (≥{min_size} configs)")
    
    # Summary stats
    improvements = [b['improvement'] for b in both]
    dmcfar_wins = sum(1 for i in improvements if i > 0)
    ties = sum(1 for i in improvements if i == 0)
    kcfa_wins = sum(1 for i in improvements if i < 0)
    
    print(f"\nContinuation Precision:")
    print(f"  DMCFAR wins:  {dmcfar_wins}/{len(both)} ({100*dmcfar_wins/len(both):.1f}%)")
    print(f"  Ties:         {ties}/{len(both)}")
    print(f"  k-CFA wins:   {kcfa_wins}/{len(both)} ({100*kcfa_wins/len(both):.1f}%)")
    print(f"  Mean improvement: {np.mean(improvements):+.1f} pp")
    print(f"  Median improvement: {np.median(improvements):+.1f} pp")
    
    # Show top improvements
    both.sort(key=lambda x: x['improvement'], reverse=True)
    
    print(f"\nTop 10 improvements (DMCFAR over k-CFA):")
    print(f"{'Benchmark':<40} {'Size':<8} {'DMCFAR':<10} {'k-CFA':<10} {'Diff':<8}")
    print("-"*80)
    for b in both[:10]:
        print(f"{b['name']:<40} {b['size']:<8.0f} {b['dmcfar_cont']:>8.1f}% {b['kcfa_cont']:>8.1f}% {b['improvement']:>+6.1f}pp")
    
    # Show where k-CFA wins
    if kcfa_wins > 0:
        print(f"\nWhere k-CFA wins (worse for DMCFAR):")
        print(f"{'Benchmark':<40} {'Size':<8} {'DMCFAR':<10} {'k-CFA':<10} {'Diff':<8}")
        print("-"*80)
        both.sort(key=lambda x: x['improvement'])
        for b in both[:min(10, kcfa_wins)]:
            if b['improvement'] < 0:
                print(f"{b['name']:<40} {b['size']:<8.0f} {b['dmcfar_cont']:>8.1f}% {b['kcfa_cont']:>8.1f}% {b['improvement']:>+6.1f}pp")
    
    # Success rates
    print(f"\n{'='*80}")
    print("SUCCESS RATES (programs ≥{min_size} configs)")
    print(f"{'='*80}")
    
    total_benchmarks = len([s for s in sizes.values() if s >= min_size])
    
    for config in configs_of_interest:
        n_success = agg[config]['n']
        success_rate = 100 * n_success / total_benchmarks if total_benchmarks > 0 else 0
        timeouts = total_benchmarks - n_success
        print(f"{config:<20} {n_success}/{total_benchmarks} ({success_rate:.1f}%) - {timeouts} timeouts")

if __name__ == '__main__':
    main()
