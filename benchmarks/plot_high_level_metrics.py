
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
        # Metric 1: Value Precision Improvement (prec_val_total)
        filtered_data.append({
            'Configuration': config['label'],
            'MetricType': 'Value Precision (Improvement)',
            'Value': row.get('prec_val_total', 0.0),
            'Hits': row.get('prec_val_total_hits', 0),
            'Total': row.get('prec_val_total_total', 0)
        })
        # Metric 2: Continuation Precision Improvement (prod_k_str)
        filtered_data.append({
            'Configuration': config['label'],
            'MetricType': 'Continuation Precision (Improvement)',
            'Value': row.get('prod_k_str', 0.0),
            'Hits': row.get('prod_k_str_hits', 0),
            'Total': row.get('prod_k_str_total', 0)
        })

df_long = pd.DataFrame(filtered_data)

# Calculate Summary Stats: Micro-Average (Pooled Mean)
# Sum all hits / Sum all totals for each config group
# This weights larger benchmarks more heavily and handles 0/0 gracefully.

# Group by Configuration and MetricType
summary = df_long.groupby(['Configuration', 'MetricType'])[['Hits', 'Total']].sum().reset_index()
summary['Value_mean'] = summary['Hits'] / summary['Total']
summary['Value_se'] = 0 # Error bars not applicable for single pooled ratio without bootstrapping

# Function to plot
def plot_metric(data, metric_col, error_col, title, filename, ylabel):
    plt.figure(figsize=(12, 7))
    sns.set_theme(style="whitegrid")
    
    # Bar plot
    ax = sns.barplot(data=data, x="Configuration", y=metric_col, hue="MetricType", order=order, hue_order=hue_order,
                     palette="viridis")
    
    # Error bars
    if error_col:
        for j, metric in enumerate(hue_order):
            if j >= len(ax.containers): break
            container = ax.containers[j]
            for k, bar in enumerate(container):
                if k >= len(order): continue
                config = order[k]
                
                row = data[(data['Configuration'] == config) & (data['MetricType'] == metric)]
                if row.empty: continue
                
                val = row[metric_col].values[0]
                err = row[error_col].values[0]
                
                if pd.isna(err) or err == 0: continue
                
                ax.errorbar(bar.get_x() + bar.get_width() / 2, val,
                            yerr=err, fmt='none', c='black', capsize=5)

    plt.title(title)
    plt.ylabel(ylabel)
    plt.xlabel("Analysis Configuration")
    plt.legend(title="Metric", loc='upper left')
    plt.tight_layout()
    plt.savefig(filename)
    print(f"Saved {filename}")

# Define order (Exclude 0-CFA from plot as it is the baseline)
order = [c['label'] for c in configs if c['label'] != '0-CFA']
hue_order = ['Continuation Precision (Improvement)', 'Value Precision (Improvement)']

# 1. Micro-Average Plot
print("\nProductivity Summary (Micro-Average):")
print(summary[['Configuration', 'MetricType', 'Value_mean']])

plot_metric(summary, 'Value_mean', None, 
            "High-Level Productivity (Pooled Mean Improvement over 0-CFA)", 
            "benchmarks/new_analysis/plot_high_level_productivity_mean.png",
            "Relative Improvement (Pooled Mean)")

# 2. Median Plot
# Filter dataframes for median calculation
df_struct = df_long[df_long['MetricType'] == 'Value Precision (Improvement)']
df_cont = df_long[df_long['MetricType'] == 'Continuation Precision (Improvement)']

# Calculate Median
summary_struct_med = df_struct.groupby(['Configuration', 'MetricType'])['Value'].median().reset_index()
summary_cont_med = df_cont.groupby(['Configuration', 'MetricType'])['Value'].median().reset_index()
summary_median = pd.concat([summary_struct_med, summary_cont_med], ignore_index=True)
# Rename for plotting function
summary_median = summary_median.rename(columns={'Value': 'Value_median'})
summary_median['Value_err'] = 0 # No error bars for median for now

print("\nProductivity Summary (Median):")
print(summary_median)

plot_metric(summary_median, 'Value_median', None,
            "High-Level Productivity (Median Improvement over 0-CFA)",
            "benchmarks/new_analysis/plot_high_level_productivity_median.png",
            "Relative Improvement (Median)")
