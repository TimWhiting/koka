
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, get_complex_benchmarks, filter_common_benchmarks

def analyze_distribution():
    print("Loading results...")
    results = load_results_with_baselines("benchmarks/results-cached")
    df = pd.DataFrame(results)
    
    # Filter for complex benchmarks
    complex_bench = get_complex_benchmarks(df)
    df = df[df['benchmarkName'].isin(complex_bench)]
    
    configs = [
        {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'},
        {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': '1,1-HMCFAR'}
    ]
    
    df = filter_common_benchmarks(df, configs)
    
    for config in configs:
        subset = df[
            (df['variant'] == config['variant']) & 
            (df['d'] == config['d']) & 
            (df['m'] == config['m'])
        ]
        
        print(f"\n--- Distribution for {config['label']} ---")
        
        for metric, name in [('prod_k_str', 'Continuation Impr'), ('prec_val_total', 'Value Impr')]:
            vals = subset[metric].dropna()
            if vals.empty:
                print(f"{name}: No data")
                continue
                
            print(f"{name}:")
            print(f"  Count: {len(vals)}")
            print(f"  Zeros: {(vals == 0).sum()} ({ (vals==0).sum()/len(vals)*100:.1f}%)")
            print(f"  Mean (Arith): {vals.mean():.4f}")
            print(f"  Mean (Pooled): {subset[metric + '_hits'].sum() / subset[metric + '_total'].sum():.4f}")
            print(f"  Percentiles:")
            print(vals.describe(percentiles=[0.25, 0.5, 0.75, 0.9, 0.95]))

if __name__ == "__main__":
    analyze_distribution()
