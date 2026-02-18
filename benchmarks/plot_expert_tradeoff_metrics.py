import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
import numpy as np
from matplotlib.lines import Line2D
from plot_utils import load_results_with_baselines, prepare_tradeoff_data, get_tradeoff_color

# Load results
print("Loading results with sophisticated metrics...")
# Configs to compare
c_base = {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'}
c_new = {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': 'H(1,1)'}

# Metrics and Cost Configs
metrics_to_plot = [
    {'Name': 'Value RIR (Strict)', 'Col': 'prec_val_rir_strict', 'File': 'plot_expert_tradeoff_productivity.png'},
    {'Name': 'Continuation RIR (Strict)', 'Col': 'prec_cont_rir_strict', 'File': 'plot_expert_tradeoff_cont_productivity.png'},
    {'Name': 'Value Absolute Precision', 'Col': 'prec_val_real', 'File': 'plot_expert_tradeoff_real.png'},
    {'Name': 'Continuation Absolute Precision', 'Col': 'prec_cont_real', 'File': 'plot_expert_tradeoff_cont_real.png'}
]

cost_configs = [
    {'CostName': 'States', 'CostCol': 'States', 'XLabel': 'State Space Size', 'Suffix': ''},
    {'CostName': 'Time', 'CostCol': 'Time', 'XLabel': 'Analysis Time (s)', 'Suffix': '_time'}
]

# Load results using shared util
df_final = load_results_with_baselines()

# Collect data for combined plots
collected_data = {} # Key: (MetricName, CostName) -> DataFrame

# Process each metric
for m_info in metrics_to_plot:
    metric_name = m_info['Name']
    col_name = m_info['Col']
    base_filename = m_info['File']
    
    for cost_cfg in cost_configs:
        cost_name = cost_cfg['CostName']
        cost_col = cost_cfg['CostCol']
        xlabel = cost_cfg['XLabel']
        suffix = cost_cfg['Suffix']
        
        # Construct filename
        if suffix:
            parts = base_filename.rsplit('.', 1)
            filename = f"{parts[0]}{suffix}.{parts[1]}"
        else:
            filename = base_filename
            
        print(f"Plotting {metric_name} vs {cost_name}...")
        
        try:
            metrics_map = {'Cost': cost_col, 'Precision': col_name}
            plot_df = prepare_tradeoff_data(df_final, c_base, c_new, metrics_map)
        except KeyError:
            print(f"Skipping {metric_name}: Column {col_name} not found.")
            continue

        print(f"Plotting {len(plot_df)} common benchmarks.")

        # Calculate Gain and Ratio
        plot_df['Prec_Gain'] = plot_df['Precision_New'] - plot_df['Precision_Base']
        
        cost_new = plot_df['Cost_New'].fillna(0.0).astype(float)
        cost_base = plot_df['Cost_Base'].fillna(0.0).astype(float)
        
        cost_ratios = []
        for n, b in zip(cost_new, cost_base):
            if b <= 1e-12: 
                r = 1.0 if n == 0 else 1e6
            else:
                r = n / b
            cost_ratios.append(r)
            
        plot_df['Cost_Ratio'] = cost_ratios
        
        # Filter for interesting benchmarks
        initial_len = len(plot_df)
        plot_df = plot_df[
            (plot_df['Prec_Gain'].abs() > 0.01) | 
            (plot_df['Cost_Ratio'] < 0.9) | 
            (plot_df['Cost_Ratio'] > 1.1)
        ]
        print(f"Filtered {initial_len} -> {len(plot_df)} interesting benchmarks.")
        
        # Store for combined
        collected_data[(metric_name, cost_name)] = plot_df.copy()

        # --- INDIVIDUAL PLOT ---
        plt.figure(figsize=(7, 4))
        sns.set_theme(style="whitegrid", font_scale=1.4)

        for i, row in plot_df.iterrows():
            stat_base = row.get('Status_Base', 'Missing')
            stat_new = row.get('Status_New', 'Missing')
            has_base = stat_base == 'OK' and pd.notna(row.get('Cost_Base')) and pd.notna(row.get('Precision_Base'))
            has_new = stat_new == 'OK' and pd.notna(row.get('Cost_New')) and pd.notna(row.get('Precision_New'))
            
            if has_base and has_new:
                prec_gain = row['Precision_New'] - row['Precision_Base']
                cost_ratio = row['Cost_New'] / row['Cost_Base'] # Safety handled in prep? No, need check
                if row['Cost_Base'] <= 1e-12: cost_ratio = 1.0
                
                color, alpha = get_tradeoff_color(prec_gain, cost_ratio)
                p0 = (row['Cost_Base'], row['Precision_Base'])
                p1 = (row['Cost_New'], row['Precision_New'])
                
                plt.plot([p0[0], p1[0]], [p0[1], p1[1]], color=color, alpha=0.3, linewidth=1)
                plt.scatter(p0[0], p0[1], color='gray', s=20, marker='x', alpha=0.6, zorder=2)
                plt.scatter(p1[0], p1[1], color=color, s=25, marker='o', alpha=0.8, zorder=3)
                
            elif has_base:
                p0 = (row['Cost_Base'], row['Precision_Base'])
                plt.scatter(p0[0], p0[1], color='red', s=20, marker='x', alpha=0.8, zorder=2)
                
            elif has_new:
                p1 = (row['Cost_New'], row['Precision_New'])
                plt.scatter(p1[0], p1[1], color='green', s=25, marker='o', alpha=0.9, zorder=3)

        plt.xlabel(xlabel)
        plt.xscale('log')
        plt.ylabel(metric_name)
        plt.title(f"{metric_name} vs {cost_name}")

        legend_elements = [
            Line2D([0], [0], color='green', lw=2, label='Win-Win'),
            Line2D([0], [0], color='blue', lw=2, label='Trade-off'),
            Line2D([0], [0], color='red', lw=2, label='Regression'),
            Line2D([0], [0], color='gray', lw=2, label='Similar Precision'),
            Line2D([0], [0], marker='x', color='gray', label='1-kCFA', linestyle='None', markersize=8),
            Line2D([0], [0], marker='o', color='gray', label='H(1,1)', linestyle='None', markersize=8),
        ]
        plt.legend(handles=legend_elements, bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0.)

        plt.tight_layout(pad=0.2)
        plt.savefig(f"benchmarks/new_analysis/{filename}")
        print(f"Saved benchmarks/new_analysis/{filename}")
        plt.close()

# --- COMBINED PLOTS ---
def plot_combined_tradeoff(cost_name, suffix, xlabel):
    print(f"Generating combined tradeoff plot for {cost_name}...")
    fig, axs = plt.subplots(1, 2, figsize=(14, 4))
    sns.set_theme(style="whitegrid", font_scale=1.4)
    
    metrics = [
        ('Value RIR (Strict)', 'Value RIR', axs[0]),
        ('Continuation RIR (Strict)', 'Continuation RIR', axs[1])
    ]
    
    for metric_name, title, ax in metrics:
        key = (metric_name, cost_name)
        if key not in collected_data: continue
        
        plot_df = collected_data[key]
        
        for i, row in plot_df.iterrows():
            stat_base = row.get('Status_Base', 'Missing')
            stat_new = row.get('Status_New', 'Missing')
            has_base = stat_base == 'OK' and pd.notna(row.get('Cost_Base')) and pd.notna(row.get('Precision_Base'))
            has_new = stat_new == 'OK' and pd.notna(row.get('Cost_New')) and pd.notna(row.get('Precision_New'))
            
            if has_base and has_new:
                prec_gain = row['Precision_New'] - row['Precision_Base']
                cost_ratio = row['Cost_New'] / row['Cost_Base'] if row['Cost_Base'] > 1e-12 else 1.0
                color, alpha = get_tradeoff_color(prec_gain, cost_ratio)
                p0 = (row['Cost_Base'], row['Precision_Base'])
                p1 = (row['Cost_New'], row['Precision_New'])
                ax.plot([p0[0], p1[0]], [p0[1], p1[1]], color=color, alpha=0.3, linewidth=1)
                ax.scatter(p0[0], p0[1], color='gray', s=20, marker='x', alpha=0.6, zorder=2)
                ax.scatter(p1[0], p1[1], color=color, s=25, marker='o', alpha=0.8, zorder=3)
            elif has_base:
                p0 = (row['Cost_Base'], row['Precision_Base'])
                ax.scatter(p0[0], p0[1], color='red', s=20, marker='x', alpha=0.8, zorder=2) # Base only
            elif has_new:
                p1 = (row['Cost_New'], row['Precision_New'])
                ax.scatter(p1[0], p1[1], color='green', s=25, marker='o', alpha=0.9, zorder=3) # New only

        ax.set_title(title)
        ax.set_ylabel("RIR" if ax == axs[0] else "")
        ax.set_xlabel(xlabel)
        ax.set_xscale('log')
        
    legend_elements = [
        Line2D([0], [0], color='green', lw=2, label='Win-Win'),
        Line2D([0], [0], color='blue', lw=2, label='Trade-off'),
        Line2D([0], [0], color='red', lw=2, label='Regression'),
        Line2D([0], [0], color='gray', lw=2, label='Similar Precision'),
        Line2D([0], [0], marker='x', color='gray', label='1-kCFA', linestyle='None', markersize=8),
        Line2D([0], [0], marker='o', color='gray', label='H(1,1)', linestyle='None', markersize=8),
    ]
    fig.legend(handles=legend_elements, bbox_to_anchor=(1.02, 0.9), loc='upper left', borderaxespad=0.)
    
    plt.tight_layout(pad=0.2)
    outfile = f"benchmarks/new_analysis/plot_expert_tradeoff_combined{suffix}.png"
    plt.savefig(outfile, bbox_inches='tight')
    print(f"Saved {outfile}")

plot_combined_tradeoff('States', '', 'State Space Size')
plot_combined_tradeoff('Time', '_time', 'Analysis Time (s)')
