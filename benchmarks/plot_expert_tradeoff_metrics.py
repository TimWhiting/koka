
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
    {'Name': 'Value Precision Improvement (Store + Literals)', 'Col': 'prec_val_total', 'File': 'plot_expert_tradeoff_productivity.png'},
    {'Name': 'Value Precision (Absolute via Improvement)', 'Col': 'prec_val_abs_impr', 'File': 'plot_expert_tradeoff_abs_impr.png'},
    {'Name': 'Value Precision (Real)', 'Col': 'prec_val_real', 'File': 'plot_expert_tradeoff_real.png'},
    {'Name': 'Continuation Precision Improvement', 'Col': 'prod_k_str', 'File': 'plot_expert_tradeoff_cont_productivity.png'},
    {'Name': 'Continuation Precision (Absolute via Improvement)', 'Col': 'prec_cont_abs_impr', 'File': 'plot_expert_tradeoff_cont_abs_impr.png'},
    {'Name': 'Continuation Precision (Real)', 'Col': 'prec_cont_real', 'File': 'plot_expert_tradeoff_cont_real.png'}
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
    filename = m_info['File']
    
    print(f"Plotting {metric_name}...")
    
    try:
        # Pass metrics map expected by prepare_tradeoff_data
        metrics_map = {'Cost': 'States', 'Precision': col_name}
        plot_df = prepare_tradeoff_data(df_final, c_base, c_new, metrics_map)
    except KeyError:
        print(f"Skipping {metric_name}: Column {col_name} not found.")
        continue

    print(f"Plotting {len(plot_df)} common benchmarks.")

    # Calculate Gain and Ratio which were removed
    plot_df['Prec_Gain'] = plot_df['Precision_New'] - plot_df['Precision_Base']
    plot_df['Cost_Ratio'] = plot_df['Cost_New'] / plot_df['Cost_Base']

    plt.figure(figsize=(10, 6))
    sns.set_theme(style="whitegrid")

    # Draw lines
    for i, row in plot_df.iterrows():
        color, alpha = get_tradeoff_color(row['Prec_Gain'], row['Cost_Ratio'])
        
        p0 = (row['Cost_Base'], row['Precision_Base'])
        p1 = (row['Cost_New'], row['Precision_New'])
        
        plt.plot([p0[0], p1[0]], [p0[1], p1[1]], color=color, alpha=alpha, linewidth=1)
        
        # Plot points
        plt.scatter(p0[0], p0[1], color='gray', s=10, alpha=0.5) # Base start
        plt.scatter(p1[0], p1[1], color=color, s=20, alpha=0.8) # New end

    # Improve axes
    plt.xscale('log')
    plt.xlabel("State Space Size (Log Scale)")
    plt.ylabel(metric_name)
    plt.title(f"Expert Trade-off: State Cost vs {metric_name}")

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
