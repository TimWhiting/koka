
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
c_new = {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': '1,1-HMCFAR'}

# Metrics mapping: {'DesiredName': 'ColumnNameInResults', 'Filename': 'savename'}
metrics_to_plot = [
    # 1. RIR (Strict Precision Recovery) - Replacing the old "Productivity" plots with Strict RIR logic
    {'Name': 'Value RIR (Strict)', 'Col': 'prec_val_rir_strict', 'File': 'plot_expert_tradeoff_productivity.png'},
    {'Name': 'Continuation RIR (Strict)', 'Col': 'prec_cont_rir_strict', 'File': 'plot_expert_tradeoff_cont_productivity.png'},

    # 2. Absolute Precision (Real measured precision) - Keeping these as secondary/reference
    {'Name': 'Value Absolute Precision', 'Col': 'prec_val_real', 'File': 'plot_expert_tradeoff_real.png'},
    {'Name': 'Continuation Absolute Precision', 'Col': 'prec_cont_real', 'File': 'plot_expert_tradeoff_cont_real.png'}
]

# Baseline: 1-kCFA (d=0, m=1)
c_base = {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'}
c_new = {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': '1,1-HMCFAR'}

# Load results using shared util
# This caches results so subsequent calls are fast
print("Loading results with sophisticated metrics...")
df_final = load_results_with_baselines()

# Process each metric
for m_info in metrics_to_plot:
    metric_name = m_info['Name']
    col_name = m_info['Col']
    base_filename = m_info['File']
    
    # Loop over Cost Metrics
    cost_configs = [
        {'CostName': 'States', 'CostCol': 'States', 'XLabel': 'State Space Size', 'Suffix': ''},
        {'CostName': 'Time', 'CostCol': 'Time', 'XLabel': 'Analysis Time (s)', 'Suffix': '_time'}
    ]
    
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
            # Pass metrics map expected by prepare_tradeoff_data
            metrics_map = {'Cost': cost_col, 'Precision': col_name}
            plot_df = prepare_tradeoff_data(df_final, c_base, c_new, metrics_map)
        except KeyError:
            print(f"Skipping {metric_name}: Column {col_name} not found.")
            continue

        print(f"Plotting {len(plot_df)} common benchmarks.")

        # Calculate Gain and Ratio which were removed
        plot_df['Prec_Gain'] = plot_df['Precision_New'] - plot_df['Precision_Base']
        
        # Handle zero cost (e.g. Time = 0.0s) and NaNs
        # Ensure float type
        cost_new = plot_df['Cost_New'].fillna(0.0).astype(float)
        cost_base = plot_df['Cost_Base'].fillna(0.0).astype(float)
        
        # Use manual loop to avoid any pandas/numpy division issues
        cost_ratios = []
        for n, b in zip(cost_new, cost_base):
            if b <= 1e-12: # Treat small epsilon as 0
                r = 1.0 if n == 0 else 1e6 # Avoid infinity
            else:
                r = n / b
            cost_ratios.append(r)
            
        plot_df['Cost_Ratio'] = cost_ratios
        
        print(f"Cost Base Range: {cost_base.min()} - {cost_base.max()}")
        
        # Filter for interesting benchmarks (like the old script)
        # Show if useful difference in Precision (> 1%) OR useful difference in Cost (> 10%)
        initial_len = len(plot_df)
        plot_df = plot_df[
            (plot_df['Prec_Gain'].abs() > 0.01) | 
            (plot_df['Cost_Ratio'] < 0.9) | 
            (plot_df['Cost_Ratio'] > 1.1)
        ]
        print(f"Filtered {initial_len} -> {len(plot_df)} interesting benchmarks (Diff > 1% or Cost Ratio > 10%).")

        plt.figure(figsize=(10, 6))
        sns.set_theme(style="whitegrid")

        # Draw lines
        for i, row in plot_df.iterrows():
            # Check status
            stat_base = row.get('Status_Base', 'Missing')
            stat_new = row.get('Status_New', 'Missing')
            
            has_base = stat_base == 'OK' and pd.notna(row.get('Cost_Base')) and pd.notna(row.get('Precision_Base'))
            has_new = stat_new == 'OK' and pd.notna(row.get('Cost_New')) and pd.notna(row.get('Precision_New'))
            
            if has_base and has_new:
                # Full line
                prec_gain = row['Precision_New'] - row['Precision_Base']
                cost_ratio = row['Cost_New'] / row['Cost_Base'] if row['Cost_Base'] > 0 else 1.0 # Safety
                
                color, alpha = get_tradeoff_color(prec_gain, cost_ratio)
                
                p0 = (row['Cost_Base'], row['Precision_Base'])
                p1 = (row['Cost_New'], row['Precision_New'])
                
                plt.plot([p0[0], p1[0]], [p0[1], p1[1]], color=color, alpha=0.3, linewidth=1)
                
                # Plot points
                plt.scatter(p0[0], p0[1], color='gray', s=15, alpha=0.5, zorder=2) # Base start
                plt.scatter(p1[0], p1[1], color=color, s=25, alpha=0.8, zorder=3) # New end
                
            elif has_base:
                # Only Base succeeded
                p0 = (row['Cost_Base'], row['Precision_Base'])
                plt.scatter(p0[0], p0[1], color='red', s=15, marker='*', alpha=0.5, zorder=2)
                
            elif has_new:
                # Only New succeeded (Base T/O) -> Win!
                p1 = (row['Cost_New'], row['Precision_New'])
                plt.scatter(p1[0], p1[1], color='green', s=200, marker='*', alpha=0.9, zorder=3) # Star for Win
                
            # If both failed or missing, do nothing

        # Improve axes
        # plt.xscale('log') # REMOVED log scale as requested
        plt.xlabel(xlabel)
        plt.xscale('log')

        plt.ylabel(metric_name)
        plt.title(f"Expert Trade-off: {cost_name} vs {metric_name}")

        # Add manual legend
        from matplotlib.lines import Line2D
        legend_elements = [
            Line2D([0], [0], color='green', lw=2, label='Win-Win (Better Prec, Lower Cost)'),
            Line2D([0], [0], color='blue', lw=2, label='Trade-off (Better Prec, Higher Cost)'),
            Line2D([0], [0], color='red', lw=2, label='Regression (Worse Prec)'),
            Line2D([0], [0], color='gray', lw=2, label='Efficiency Change (Same Prec)'),
        ]
        plt.legend(handles=legend_elements, loc='best')

        plt.tight_layout()
        plt.savefig(f"benchmarks/new_analysis/{filename}")
        print(f"Saved benchmarks/new_analysis/{filename}")


# Do not run main logic again outside loop
exit()
