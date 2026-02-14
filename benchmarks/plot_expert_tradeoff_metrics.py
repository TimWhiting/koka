
import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
import numpy as np
from matplotlib.lines import Line2D
from plot_utils import load_results_with_baselines, prepare_tradeoff_data, get_tradeoff_color

# Load results
print("Loading results with sophisticated metrics...")
results = load_results_with_baselines("benchmarks/results-cached")

# Configs to compare
c_base = {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'}
c_new = {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': '1,1-HMCFAR'}

# Metrics mapping: {'DesiredName': 'ColumnNameInResults'}
metrics = {
    'Precision': 'prec_val_total',
    'Cost': 'States'
}

# Prepare Data
df_final = prepare_tradeoff_data(results, c_base, c_new, metrics)

# Add "Improvement" columns for filtering/coloring
df_final['Prec_Gain'] = df_final['Precision_New'] - df_final['Precision_Base']
df_final['Cost_Ratio'] = df_final['Cost_New'] / df_final['Cost_Base']

print(f"Plotting {len(df_final)} common benchmarks.")

# Plot
plt.figure(figsize=(10, 8))
sns.set_theme(style="whitegrid")

# Create connected scatter plot
for i, row in df_final.iterrows():
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
plt.ylabel("Value Precision Improvement (Store + Literals)")
plt.title("Expert Trade-off: State Cost vs Value Precision Gain")

# Add manual legend
legend_elements = [
    Line2D([0], [0], color='green', lw=2, label='Win-Win (Better Prec & Smaller)'),
    Line2D([0], [0], color='blue', lw=2, label='Trade-off (Better Prec & Larger)'),
    Line2D([0], [0], color='red', lw=2, label='Regression (Worse Prec)'),
    Line2D([0], [0], marker='o', color='gray', label='1-kCFA Start', markersize=5, linestyle='None'),
    Line2D([0], [0], marker='o', color='black', label='1,1-HMCFAR End', markersize=5, linestyle='None')
]
plt.legend(handles=legend_elements, loc='upper left')
plt.tight_layout()

output_path = "benchmarks/new_analysis/plot_expert_tradeoff_productivity.png"
plt.savefig(output_path)
print(f"Saved {output_path}")
