
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
        # Check that it exists AND is OK (not T/O)
        if 'status' in df_sweep.columns:
             subset = df_sweep[ (df_sweep['m'] == m_val) & (df_sweep['h'] == h_val) & (df_sweep['status'] == 'OK') ]
        else: # Fallback if status missing
             subset = df_sweep[ (df_sweep['m'] == m_val) & (df_sweep['h'] == h_val) ]
             
        b_set = set(subset['benchmarkName'].unique())
        if common_benchs is None:
            common_benchs = b_set
        else:
            common_benchs = common_benchs.intersection(b_set)
            
    print(f"Intersection of benchmarks for m<=2, h<=2 (ignoring T/O): {len(common_benchs)}")
    
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
                          'Value Precision (Real)', 'val_real', 'Real Precision (Pooled)'),
                          
        # New Relative Improvement Metrics (Denominator = Imprecise in Baseline)
        'prec_val_relative': ('prec_val_relative_hits', 'prec_val_relative_total',
                              'Value Precision improvement (Relative to Imprecise)', 'val_relative_impr', 'Pct of Baseline Imprecision Resolved'),
        'prec_cont_relative': ('prec_cont_relative_hits', 'prec_cont_relative_total',
                               'Continuation Precision Improvement (Relative to Imprecise)', 'cont_relative_impr', 'Pct of Baseline Imprecision Resolved')
    }
    
    sns.set_theme(style="whitegrid")
    
    # Get palette
    unique_h = sorted(df_sweep['h'].unique())
    palette = sns.color_palette("viridis", n_colors=len(unique_h))
    color_map = {h: palette[i] for i, h in enumerate(unique_h)}
    
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
        sums[metric_key] = sums.apply(lambda row: row[hits_col] / row[total_col] if row[total_col] > 0 else 0.0, axis=1)

        # Calculate timeouts per group (within the complex set, before common filtering? 
        # Actually user wants to know if THIS config failed. 
        # So we use the 'df_sweep' which is filtered for DMCFAR and Complex benchmarks.)
        
        # We compute timeouts from the FULL complex set for this config, not just the intersection set.
        # Otherwise if a bench times out, it's removed from intersection, so count would be 0 in filtered df.
        
        # Re-select from original 'df' (filtered for complex) to get timeouts
        timeout_df = df[ (df['variant'] == 'dmcfar') & 
                         (df['benchmarkName'].isin(complex_benchmarks)) & 
                         (df['m'] <= 5) & (df['d'] <= 2) ].copy()
        timeout_df['h'] = timeout_df['d']
        
        # Count TOs
        timeout_counts = timeout_df[timeout_df['status'] == 'T/O'].groupby(['m', 'h']).size().reset_index(name='timeout_count')
        
        # Merge timeouts into sums
        sums = pd.merge(sums, timeout_counts, on=['m', 'h'], how='left')
        sums['timeout_count'] = sums['timeout_count'].fillna(0).astype(int)
        
        sns.lineplot(data=sums, x='m', y=metric_key, hue='h', style='h', 
                     markers=True, palette=palette, linewidth=2.5, markersize=8)
        
        # Annotate Timeouts
        # We iterate through the data points plotted
        for i, row in sums.iterrows():
            if row['timeout_count'] > 0:
                h_val = row['h']
                color = color_map.get(h_val, 'black')
                
        # Determine scale
        y_data_max = sums[metric_key].max()
        # Ensure we have some height even if data is all 0
        if pd.isna(y_data_max) or y_data_max == 0:
            y_data_max = 0.1
            
        # Top limit with padding
        y_top = y_data_max * 1.1
        if 'real' in suffix: # Real precision is roughly 0-1, don't clip top if near 1
             y_top = max(y_top, 1.05)
             
        # Annotation steps based on scale
        # We place them below y=0
        num_h = len(unique_h)
        step = y_top * 0.08 # 8% of height per row
        
        # Bottom limit to fit annotations
        # We need space for num_h rows
        y_bottom = - (step * (num_h + 0.5))
        
        plt.ylim(y_bottom, y_top)
        
        # Annotate Timeouts
        for i, row in sums.iterrows():
            if row['timeout_count'] > 0:
                h_val = row['h']
                color = color_map.get(h_val, 'black')
                
                # Dynamic Position below 0
                # h_val is 0, 1, 2...
                # We map index of h_val in unique_h
                try:
                    h_idx = unique_h.index(h_val)
                except: h_idx = 0
                
                y_pos = - (step * (h_idx + 0.8))
                
                # Add simple text annotation with count
                plt.text(row['m'], y_pos, 
                         f"{row['timeout_count']}", 
                         color=color, fontsize=10, ha='center', va='center', fontweight='bold')
        
        plt.legend(title="Handler Sensitivity (h)")
        plt.tight_layout()
        
        outfile = f"benchmarks/new_analysis/plot_dmcfa_sweep_{suffix}.png"
        plt.savefig(outfile)
        print(f"Saved {outfile}")
        plt.close()

if __name__ == "__main__":
    plot_sweep()
