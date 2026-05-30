import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import seaborn as sns
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, resolve_results_dir, get_large_benchmarks, geometric_mean, filter_common_benchmarks

def plot_sweep():
    import os
    os.makedirs("benchmarks/images", exist_ok=True)
    print("Loading results with standardized metrics...")
    results = load_results_with_baselines(resolve_results_dir())
    df = pd.DataFrame(results)
    
    # Filter for complex benchmarks 
    complex_benchmarks = get_large_benchmarks(df, threshold=300)
    print(f"Filtering for {len(complex_benchmarks)} large benchmarks (States > 300).")
    df = df[df['benchmarkName'].isin(complex_benchmarks)]

    # Filter for DMCFAR runs and DMCFAE (0CFA)
    df_sweep = df[ (df['variant'] == 'dmcfar') | (df['variant'] == 'dmcfae') ].copy()
    
    # Filter out extreme parameter values
    df_sweep = df_sweep[ (df_sweep['m'] <= 5) & (df_sweep['d'] <= 2) ]
    
    # Handle dmcfae as d=0 points if needed, or just let d passed through
    # Rename d -> h
    df_sweep['h'] = df_sweep['d']
    
    # Map dmcfae to dmcfar (e.g. dmcfae(0,0) becomes dmcfar(0,0) for the plot)
    df_sweep.loc[df_sweep['variant'] == 'dmcfae', 'variant'] = 'dmcfar'
    
    # Define Sweep configurations for common intersection
    sweep_configs = []
    for m_val in [0, 1, 2]:
        for h_val in [0, 1, 2]:
             sweep_configs.append({'variant': 'dmcfar', 'd': h_val, 'm': m_val})
             
    # Filter common benchmarks strictly (excluding timeouts)
    df_sweep = filter_common_benchmarks(df_sweep, sweep_configs, exclude_timeouts=True)
    
    metrics_to_plot = {
        'prod_k_str': ('prod_k_str_hits', 'prod_k_str_total', 
                       'Continuation Precision (Shifted Geomean)', 'cont_productivity', 'Relative Improvement (Geomean)'),
        'prec_val_total': ('prec_val_total_hits', 'prec_val_total_total', 
                           'Value Precision (Shifted Geomean)', 'val_productivity', 'Relative Improvement (Geomean)'),
        'prec_cont_real': ('prec_cont_real_hits', 'prec_cont_real_total',
                           'Continuation Precision (Real)', 'cont_real', 'Real Precision (Pooled)'),
        'prec_val_real': ('prec_val_real_hits', 'prec_val_real_total',
                          'Value Precision (Real)', 'val_real', 'Real Precision (Pooled)'),
                          
        'prec_val_rir_strict': ('prec_val_rir_strict_hits', 'baseline_val_imprecise',
                              'Value RIR (Shifted Geomean)', 'val_rir_strict', 'Pct of Baseline Imprecision Resolved'),
        'prec_cont_rir_strict': ('prec_cont_rir_strict_hits', 'baseline_cont_imprecise',
                               'Continuation RIR (Shifted Geomean)', 'cont_rir_strict', 'Pct of Baseline Imprecision Resolved')
    }
    
    sns.set_theme(style="whitegrid")
    
    unique_h = sorted(df_sweep['h'].unique())
    palette = sns.color_palette("viridis", n_colors=len(unique_h))
    color_map = {h: palette[i] for i, h in enumerate(unique_h)}
    
    collected_data = {}

    for metric_key, val in metrics_to_plot.items():
        if len(val) == 5:
            hits_col, total_col, title, suffix, ylabel = val
        else:
             print(f"Skipping malformed metric config {metric_key}")
             continue

        # Calculate per-benchmark ratios
        df_sweep['ratio'] = df_sweep.apply(lambda row: row[hits_col] / row[total_col] if row[total_col] > 0 else 0.0, axis=1)
        
        def shifted_geomean_agg(series):
            vals = series + 1.0
            vals = vals[vals > 0]
            if len(vals) == 0: return 0.0
            return np.exp(np.mean(np.log(vals))) - 1.0

        sums = df_sweep.groupby(['m', 'h'])['ratio'].apply(shifted_geomean_agg).reset_index()
        sums.rename(columns={'ratio': metric_key}, inplace=True)

        # Timeouts logic
        timeout_df = df[ (df['variant'] == 'dmcfar') & 
                         (df['benchmarkName'].isin(complex_benchmarks)) & 
                         (df['m'] <= 5) & (df['d'] <= 2) ].copy()
        timeout_df['h'] = timeout_df['d']
        
        timeout_counts = timeout_df[timeout_df['status'] == 'T/O'].groupby(['m', 'h']).size().reset_index(name='timeout_count')
        sums = pd.merge(sums, timeout_counts, on=['m', 'h'], how='left')
        sums['timeout_count'] = sums['timeout_count'].fillna(0).astype(int)
        
        # Store for combined RIR plot
        collected_data[metric_key] = sums.copy()

    # --- COMBINED RIR PLOT ---
    print("Generating combined RIR sweep plot...")
    fig, axs = plt.subplots(1, 2, figsize=(14, 4))
    sns.set_theme(style="whitegrid", font_scale=1.4)
    
    rir_metrics = [
        ('prec_val_rir_strict', 'Value RIR', axs[0]),
        ('prec_cont_rir_strict', 'Continuation RIR', axs[1])
    ]
    
    for metric_key, title, ax in rir_metrics:
        if metric_key not in collected_data: continue
        
        data = collected_data[metric_key]
        
        sns.lineplot(data=data, x='m', y=metric_key, hue='h', style='h', 
                     markers=True, palette=palette, linewidth=2.5, markersize=8, ax=ax, legend=(ax == axs[0]))
        
        # Scaling & Annotations
        y_data_max = data[metric_key].max()
        if pd.isna(y_data_max) or y_data_max == 0: y_data_max = 0.1
        y_top = y_data_max * 1.1
        
        num_h = len(unique_h)
        step = y_top * 0.08
        y_bottom = - (step * (num_h + 0.5))
        
        ax.set_ylim(y_bottom, y_top)
        ax.set_title(title)
        ax.set_ylabel("RIR" if ax == axs[0] else "")
        ax.set_xlabel("m")
        ax.set_xticks([0, 1, 2]) # Explicitly set x-ticks
        
        for i, row in data.iterrows():
            if row['timeout_count'] > 0:
                h_val = row['h']
                color = color_map.get(h_val, 'black')
                try: h_idx = unique_h.index(h_val)
                except: h_idx = 0
                y_pos = - (step * (h_idx + 0.8))
                ax.text(row['m'], y_pos, f"{row['timeout_count']}", 
                         color=color, fontsize=10, ha='center', va='center', fontweight='bold')

        if ax.get_legend():
             ax.get_legend().remove()

    legend_elements = [Line2D([0], [0], color=color_map[h], lw=2.5, marker='o', label=f"h={h}") for h in unique_h]
    fig.legend(handles=legend_elements, title="Handler Sensitivity", bbox_to_anchor=(1.02, 0.9), loc='upper left', borderaxespad=0.)
    
    plt.tight_layout(pad=0.2)
    outfile = "benchmarks/images/plot_dmcfa_sweep_combined_rir.png"
    plt.savefig(outfile, bbox_inches='tight')
    print(f"Saved {outfile}")

if __name__ == "__main__":
    plot_sweep()
