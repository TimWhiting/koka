
import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, geometric_mean, geometric_sd, get_complex_benchmarks, filter_common_benchmarks

# Load results
print("Loading results with sophisticated metrics...")
results = load_results_with_baselines("benchmarks/results-cached")
df = pd.DataFrame(results)

# Filter for complex benchmarks (0-CFA < 99%)
complex_benchmarks = get_complex_benchmarks(df)
df_complex = df[df['benchmarkName'].isin(complex_benchmarks)]

# Define configurations of interest
configs = [
    {'variant': 'kcfa', 'd': 0, 'm': 0, 'label': '0-CFA'},
    {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'},
    {'variant': 'kcfa', 'd': 0, 'm': 2, 'label': '2-kCFA'},
    {'variant': 'dmcfar', 'd': 1, 'm': 0, 'label': '1,0-HMCFAR'},
    {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': '1,1-HMCFAR'},
    {'variant': 'dmcfar', 'd': 1, 'm': 2, 'label': '1,2-HMCFAR'},
]

# Keep only benchmarks present in ALL configurations
df_filtered = filter_common_benchmarks(df_complex, configs)

filtered_data = []
for config in configs:
    subset = df_filtered[
        (df_filtered['variant'] == config['variant']) & 
        (df_filtered['d'] == config['d']) & 
        (df_filtered['m'] == config['m'])
    ]
    for _, row in subset.iterrows():
        # Metric 3: Value Precision Improvement (Relative to Imprecise)
        filtered_data.append({
            'Configuration': config['label'],
            'MetricType': 'Relative Improvement (Pooled) - Value',
            'Value': row.get('prec_val_relative', 0.0),
            'Hits': row.get('prec_val_relative_hits', 0),
            'Total': row.get('prec_val_relative_total', 0)
        })
        # Metric 4: Continuation Precision Improvement (Relative to Imprecise)
        filtered_data.append({
            'Configuration': config['label'],
            'MetricType': 'Relative Improvement (Pooled) - Continuation',
            'Value': row.get('prec_cont_relative', 0.0),
            'Hits': row.get('prec_cont_relative_hits', 0),
            'Total': row.get('prec_cont_relative_total', 0)
        })

df_long = pd.DataFrame(filtered_data)

# Calculate Summary Stats: Micro-Average (Pooled Mean)
# Sum all hits / Sum all totals for each config group
# This weights larger benchmarks more heavily and handles 0/0 gracefully.

# Group by Configuration and MetricType
summary = df_long.groupby(['Configuration', 'MetricType'])[['Hits', 'Total']].sum().reset_index()
summary['Value_mean'] = summary['Hits'] / summary['Total']
summary['Value_se'] = 0 # Error bars not applicable for single pooled ratio without bootstrapping

# Function to plot dual axis bar chart
def plot_dual_axis(data, metric_col, title, filename):
    fig, ax1 = plt.subplots(figsize=(10, 6))
    sns.set_theme(style="white")
    
    # Filter data
    # We expect 'Relative Improvement (Pooled) - Value' and 'Relative Improvement (Pooled) - Continuation'
    val_metric = 'Relative Improvement (Pooled) - Value'
    cont_metric = 'Relative Improvement (Pooled) - Continuation'
    
    df_val = data[data['MetricType'] == val_metric].set_index('Configuration')
    df_cont = data[data['MetricType'] == cont_metric].set_index('Configuration')
    
    # Align to order
    x = np.arange(len(order))
    width = 0.35
    
    # Plot Value bars (Left Axis)
    vals = [df_val.loc[c][metric_col] if c in df_val.index else 0 for c in order]
    rects1 = ax1.bar(x - width/2, vals, width, label='Value Precision (Relative Impr.)', color='tab:blue', alpha=0.7)
    
    ax1.set_xlabel('Analysis Configuration')
    ax1.set_ylabel('Value Precision Improvement (%)', color='tab:blue')
    ax1.tick_params(axis='y', labelcolor='tab:blue')
    ax1.set_ylim(0, max(vals)*1.2 if vals else 1.0)
    ax1.set_xticks(x)
    ax1.set_xticklabels(order)
    
    # Plot Continuation bars (Right Axis)
    ax2 = ax1.twinx()
    conts = [df_cont.loc[c][metric_col] if c in df_cont.index else 0 for c in order]
    rects2 = ax2.bar(x + width/2, conts, width, label='Continuation Precision (Relative Impr.)', color='tab:orange', alpha=0.7)
    
    ax2.set_ylabel('Continuation Precision Improvement (%)', color='tab:orange')
    ax2.tick_params(axis='y', labelcolor='tab:orange')
    ax2.set_ylim(0, max(conts)*1.2 if conts else 1.0)
    
    # Legends
    lines1, labels1 = ax1.get_legend_handles_labels()
    lines2, labels2 = ax2.get_legend_handles_labels()
    ax1.legend(lines1 + lines2, labels1 + labels2, loc='upper left')
    
    plt.title(title)
    plt.tight_layout()
    plt.savefig(filename)
    print(f"Saved {filename}")

# Define order (Exclude 0-CFA from plot as it is the baseline)
order = [c['label'] for c in configs if c['label'] != '0-CFA']

# 1. Micro-Average Plot
print("\nProductivity Summary (Micro-Average):")
print(summary[['Configuration', 'MetricType', 'Value_mean']])

plot_dual_axis(summary, 'Value_mean', 
            "High-Level Productivity (Pooled Mean Improvement over 0-CFA)", 
            "benchmarks/new_analysis/plot_high_level_productivity_mean.png")

# 2. Median Plot
# Filter dataframes for median calculation
df_struct = df_long[df_long['MetricType'] == 'Relative Improvement (Pooled) - Value']
df_cont = df_long[df_long['MetricType'] == 'Relative Improvement (Pooled) - Continuation']

# Calculate Median
summary_struct_med = df_struct.groupby(['Configuration', 'MetricType'])['Value'].median().reset_index()
summary_cont_med = df_cont.groupby(['Configuration', 'MetricType'])['Value'].median().reset_index()
summary_median = pd.concat([summary_struct_med, summary_cont_med], ignore_index=True)
# Rename for plotting function
summary_median = summary_median.rename(columns={'Value': 'Value_median'})

print("\nProductivity Summary (Median):")
print(summary_median)

plot_dual_axis(summary_median, 'Value_median',
            "High-Level Productivity (Median Improvement over 0-CFA)",
            "benchmarks/new_analysis/plot_high_level_productivity_median.png")
