
import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, safe_gmean, geometric_sd, get_complex_benchmarks, filter_common_benchmarks

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
        # Metric 1: Store Precision Improvement (prec_struct)
        filtered_data.append({
            'Configuration': config['label'],
            'MetricType': 'Store Precision (Improvement)',
            'Value': row['prec_struct']
        })
        # Metric 2: Continuation Precision Improvement (prod_k_str)
        filtered_data.append({
            'Configuration': config['label'],
            'MetricType': 'Continuation Precision (Improvement)',
            'Value': row['prod_k_str']
        })

df_long = pd.DataFrame(filtered_data)

# Calculate Summary Stats
# Use Arithmetic Mean for Productivity (Average Relative Improvement)
# Geometric Mean penalizes algorithms that improve more benchmarks if those improvements are small.

# prec_struct uses mean
df_struct = df_long[df_long['MetricType'] == 'Store Precision (Improvement)']
summary_struct = df_struct.groupby(['Configuration', 'MetricType'])['Value'].mean().reset_index()
summary_struct_se = df_struct.groupby(['Configuration', 'MetricType'])['Value'].sem().reset_index()
summary_struct = pd.merge(summary_struct, summary_struct_se, on=['Configuration', 'MetricType'], suffixes=('_mean', '_se'))

# prod_k_str uses mean
df_cont = df_long[df_long['MetricType'] == 'Continuation Precision (Improvement)']
summary_cont = df_cont.groupby(['Configuration', 'MetricType'])['Value'].mean().reset_index()
summary_cont_se = df_cont.groupby(['Configuration', 'MetricType'])['Value'].sem().reset_index()
summary_cont = pd.merge(summary_cont, summary_cont_se, on=['Configuration', 'MetricType'], suffixes=('_mean', '_se'))

# Combine
summary = pd.concat([summary_struct, summary_cont], ignore_index=True)

print("\nProductivity Summary (Mean +/- SE):")
pd.set_option('display.max_columns', None)
pd.set_option('display.width', 1000)
print(summary)

# Plot
plt.figure(figsize=(12, 7))
sns.set_theme(style="whitegrid")

# Define order (Exclude 0-CFA from plot as it is the baseline)
order = [c['label'] for c in configs if c['label'] != '0-CFA']
hue_order = ['Continuation Precision (Improvement)', 'Store Precision (Improvement)']

# Helper for plotting with mixed estimators?
# sns.barplot doesn't support mixed estimators easily per hue.
# We have computed summary stats already. We can plot from summary dataframe directly?
# But we need bars side-by-side.

# Let's use the summary DF for plotting to have total control
# Summary has Configuration, MetricType, Value_mean, Value_se
# Create a barplot of the means
ax = sns.barplot(data=summary, x="Configuration", y="Value_mean", hue="MetricType", order=order, hue_order=hue_order,
                 palette="viridis")

# Add error bars manually
# We need to find the correct bar patches.
# sns.barplot orders bars by hue then by x.
# containers[0] is first hue level (Continuation)
# containers[1] is second hue level (Store)

for j, metric in enumerate(hue_order):
    # Find the bars for this metric
    # containers[j] lists bars for the j-th hue level
    if j >= len(ax.containers): break
    container = ax.containers[j]
    
    for k, bar in enumerate(container):
        if k >= len(order): continue
        config = order[k]
        
        row = summary[(summary['Configuration'] == config) & (summary['MetricType'] == metric)]
        if row.empty: continue
        
        val_mean = row['Value_mean'].values[0]
        val_se = row['Value_se'].values[0]
        
        if pd.isna(val_se): continue

        # Standard Error Bars
        yerr = val_se
            
        ax.errorbar(bar.get_x() + bar.get_width() / 2, val_mean,
                    yerr=yerr,
                    fmt='none', c='black', capsize=5)

plt.title("High-Level Productivity (Improvement over 0-CFA) on Complex Benchmarks (Mean +/- SE)")
plt.ylabel("Relative Improvement (Productivity)")
plt.xlabel("Analysis Configuration")
plt.legend(title="Metric", loc='upper left')
plt.tight_layout()

output_path = "benchmarks/new_analysis/plot_high_level_productivity.png"
plt.savefig(output_path)
print(f"Saved {output_path}")
