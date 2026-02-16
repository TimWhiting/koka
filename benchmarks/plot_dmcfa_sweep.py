
import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, get_complex_benchmarks, geometric_mean

def plot_sweep():
    print("Loading results with standardized metrics...")
    results = load_results_with_baselines("benchmarks/results-cached")
    df = pd.DataFrame(results)
    
    # Filter for complex benchmarks 
    # (Use the same definition as High Level plots for consistency)
    complex_benchmarks = get_complex_benchmarks(df)
    print(f"Filtering for {len(complex_benchmarks)} complex benchmarks.")
    df = df[df['benchmarkName'].isin(complex_benchmarks)]

    # Filter for DMCFAR runs only for the sweep
    df_sweep = df[ (df['variant'] == 'dmcfar') ].copy()
    
    # Filter out extreme parameter values
    df_sweep = df_sweep[ (df_sweep['m'] <= 5) & (df_sweep['d'] <= 2) ]
    
    # Rename d -> h
    df_sweep['h'] = df_sweep['d']
    
    # CRITICAL: Ensure we are comparing the SAME benchmarks across all points.
    # If m=2 times out on a benchmark that m=1 solved, m=2's geomean might shift artificially.
    # We find benchmarks present in ALL (m, d) configurations we plan to plot within range m<=2.
    # (Going up to m=5 might be too aggressive for common filtering, let's limit commonality check to m<=2)
    
    common_configs = []
    for m_val in [0, 1, 2]:
        for h_val in [0, 1, 2]:
             common_configs.append((m_val, h_val))
             
    # Find intersection of benchmarks for these core configs
    common_benchs = None
    for m_val, h_val in common_configs:
        subset = df_sweep[ (df_sweep['m'] == m_val) & (df_sweep['h'] == h_val) ]
        b_set = set(subset['benchmarkName'].unique())
        if common_benchs is None:
            common_benchs = b_set
        else:
            common_benchs = common_benchs.intersection(b_set)
            
    print(f"Intersection of benchmarks for m<=2, h<=2: {len(common_benchs)}")
    
    # Filter main df to this intersection
    df_sweep = df_sweep[ df_sweep['benchmarkName'].isin(common_benchs) ]
    
    # Define the 4 metrics to plot
    # Key: Column Name in df
    # Value: (Display Name, Filename Suffix, Y-Label)
    metrics_to_plot = {
        'prod_k_str': ('Continuation Precision (Improvement)', 'cont_productivity', 'Geomean Relative Improvement'),
        'prec_val_total': ('Value Precision (Improvement)', 'val_productivity', 'Geomean Relative Improvement'),
        'prec_cont_real': ('Continuation Precision (Real)', 'cont_real', 'Geomean Real Precision'),
        'prec_val_real': ('Value Precision (Real)', 'val_real', 'Geomean Real Precision')
    }
    
    sns.set_theme(style="whitegrid")
    
    for metric_col, (title, suffix, ylabel) in metrics_to_plot.items():
        plt.figure(figsize=(8, 6))
        
        # Aggregate: Geomean per (m, h)
        # We compute the geomean across all benchmarks for each config
        agg = df_sweep.groupby(['m', 'h'])[metric_col].apply(geometric_mean).reset_index()
        
        sns.lineplot(data=agg, x='m', y=metric_col, hue='h', style='h', 
                     markers=True, palette="viridis", linewidth=2.5, markersize=8)
        
        plt.title(f"Effect of Call Sensitivity on {title}", fontsize=14)
        plt.xlabel("Call Context Sensitivity (m)", fontsize=12)
        plt.ylabel(ylabel, fontsize=12)
        plt.xticks(sorted(agg['m'].unique()))
        
        # Adjust Y-limits slightly to show data clearly
        # For Real/Prec metrics 0-1 is natural, but improvement might be small
        if 'real' in suffix:
             plt.ylim(0.0, 1.05)
        
        plt.legend(title="Handler Sensitivity (h)")
        plt.tight_layout()
        
        outfile = f"benchmarks/new_analysis/plot_dmcfa_sweep_{suffix}.png"
        plt.savefig(outfile)
        print(f"Saved {outfile}")
        plt.close()

if __name__ == "__main__":
    plot_sweep()
