
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
    # Updated Key: Column Name in df -> (HitsCol, TotalCol)
    # Value: (Display Name, Filename Suffix, Y-Label)
    metrics_to_plot = {
        'prod_k_str': ('prod_k_str_hits', 'prod_k_str_total', 
                       'Continuation Precision (Improvement)', 'cont_productivity', 'Relative Improvement (Pooled)'),
        'prec_val_total': ('prec_val_total_hits', 'prec_val_total_total', 
                           'Value Precision (Improvement)', 'val_productivity', 'Relative Improvement (Pooled)'),
        'prec_cont_real': ('prec_cont_real_hits', 'prec_cont_real_total',
                           'Continuation Precision (Real)', 'cont_real', 'Real Precision (Pooled)'),
        'prec_val_real': ('prec_val_real_hits', 'prec_val_real_total',
                          'Value Precision (Real)', 'val_real', 'Real Precision (Pooled)')
    }
    
    sns.set_theme(style="whitegrid")
    
    for metric_key, val in metrics_to_plot.items():
        if len(val) == 5:
            hits_col, total_col, title, suffix, ylabel = val
        else:
             print(f"Skipping malformed metric config {metric_key}")
             continue

        plt.figure(figsize=(8, 6))
        
        # Aggregate: Sum hits and totals per group
        # This effectively calculates the Micro-Average (Weighted Mean)
        # Ratio = Sum(Hits) / Sum(Total) across all benchmarks in the group
        
        # Groupby sums
        sums = df_sweep.groupby(['m', 'h'])[[hits_col, total_col]].sum().reset_index()
        
        # Calculate ratio
        # Avoid division by zero
        sums[metric_key] = sums.apply(lambda row: row[hits_col] / row[total_col] if row[total_col] > 0 else 0.0, axis=1)
        
        sns.lineplot(data=sums, x='m', y=metric_key, hue='h', style='h', 
                     markers=True, palette="viridis", linewidth=2.5, markersize=8)
        
        plt.title(f"Effect of Call Sensitivity on {title}", fontsize=14)
        plt.xlabel("Call Context Sensitivity (m)", fontsize=12)
        plt.ylabel(ylabel, fontsize=12)
        plt.xticks(sorted(sums['m'].unique()))
        
        # Adjust Y-limits slightly to show data clearly
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
