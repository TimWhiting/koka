
import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, geometric_mean, geometric_sd, get_large_benchmarks, filter_common_benchmarks

# Load results
print("Loading results with sophisticated metrics...")
results = load_results_with_baselines("benchmarks/results-cached")
df = pd.DataFrame(results)

# Filter for large benchmarks (States > 300)
complex_benchmarks = get_large_benchmarks(df, threshold=300)
df_complex = df[df['benchmarkName'].isin(complex_benchmarks)]

# Define configurations of interest
configs = [
    {'variant': 'dmcfae', 'd': 0, 'm': 0, 'label': '0-CFA'},
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
            'MetricType': 'Relative Imprecision Recovery (Strict) - Value',
            'Value': row.get('prec_val_rir_strict', 0.0),
            'Hits': row.get('prec_val_rir_strict_hits', 0),
            'Total': row.get('baseline_val_imprecise', 0) # Total is same: imprecise in base
        })

        # Metric 4: Continuation Precision Improvement (Relative to Imprecise)
        filtered_data.append({
            'Configuration': config['label'],
            'MetricType': 'Relative Imprecision Recovery (Strict) - Continuation',
            'Value': row.get('prec_cont_rir_strict', 0.0),
            'Hits': row.get('prec_cont_rir_strict_hits', 0),
            'Total': row.get('baseline_cont_imprecise', 0)
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
# Function to plot dual axis bar chart
def plot_dual_axis(data, metric_col, title, filename, min_y_val=0, min_y_cont=0):
    fig, ax1 = plt.subplots(figsize=(10, 6))
    sns.set_theme(style="white")
    
    # Filter data
    # We expect 'Relative Improvement (Pooled) - Value' and 'Relative Improvement (Pooled) - Continuation'
    # Or generically, we filter by the MetricType associated with the passed data
    # But the function hardcodes the metric names in previous version.
    # Let's make it generic or stick to current usage.
    # The current usage passes 'data' which contains the relevant MetricTypes.
    # We can infer the types from the data unique values or assume the caller handles filtering?
    # Actually the current implementation hardcoded 'Relative Improvement...'. 
    # I need to generalize this to handle the new "Ratio Precise..." types.
    
    metrics = data['MetricType'].unique()
    val_metrics = [m for m in metrics if 'Value' in m]
    cont_metrics = [m for m in metrics if 'Continuation' in m]
    
    val_metric = val_metrics[0] if val_metrics else 'Relative Improvement (Pooled) - Value'
    cont_metric = cont_metrics[0] if cont_metrics else 'Relative Improvement (Pooled) - Continuation'
    
    df_val = data[data['MetricType'] == val_metric].set_index('Configuration')
    df_cont = data[data['MetricType'] == cont_metric].set_index('Configuration')
    
    # Align to order
    x = np.arange(len(order))
    width = 0.35
    
    # Plot Value bars (Left Axis)
    vals = [df_val.loc[c][metric_col] if c in df_val.index else 0 for c in order]
    rects1 = ax1.bar(x - width/2, vals, width, label='Value (Left)', color='tab:blue', alpha=0.7)
    
    ax1.set_xlabel('Analysis Configuration')
    ax1.set_ylabel(val_metric, color='tab:blue')
    ax1.tick_params(axis='y', labelcolor='tab:blue')
    
    # Set Y-Lim based on data and min_y
    max_val = max(vals) if vals else 1.0
    ax1.set_ylim(min_y_val, max_val * 1.1)
    
    ax1.set_xticks(x)
    ax1.set_xticklabels(order)
    
    # Plot Continuation bars (Right Axis)
    ax2 = ax1.twinx()
    conts = [df_cont.loc[c][metric_col] if c in df_cont.index else 0 for c in order]
    rects2 = ax2.bar(x + width/2, conts, width, label='Continuation (Right)', color='tab:orange', alpha=0.7)
    
    ax2.set_ylabel(cont_metric, color='tab:orange')
    ax2.tick_params(axis='y', labelcolor='tab:orange')
    
    max_cont = max(conts) if conts else 1.0
    ax2.set_ylim(min_y_cont, max_cont * 1.1)
    
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
df_struct = df_long[df_long['MetricType'] == 'Relative Imprecision Recovery (Strict) - Value']
df_cont = df_long[df_long['MetricType'] == 'Relative Imprecision Recovery (Strict) - Continuation']

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

# 3. Geometric Mean Plot (Shifted)
# Metric: exp(mean(log(1 + improvement))) - 1
# This handles 0.0 values naturally (log(1)=0).
def shifted_geomean(series):
    # Ensure no values < -1 (shouldn't happen for improvement > -100%)
    vals = series + 1.0
    vals = vals[vals > 0] # Filter invalid
    if len(vals) == 0: return 0.0
    return np.exp(np.mean(np.log(vals))) - 1.0

summary_struct_geo = df_struct.groupby(['Configuration', 'MetricType'])['Value'].apply(shifted_geomean).reset_index()
summary_cont_geo = df_cont.groupby(['Configuration', 'MetricType'])['Value'].apply(shifted_geomean).reset_index()
summary_geo = pd.concat([summary_struct_geo, summary_cont_geo], ignore_index=True)
summary_geo = summary_geo.rename(columns={'Value': 'Value_geomean'})

print("\nProductivity Summary (Shifted Geometric Mean):")
print(summary_geo)

plot_dual_axis(summary_geo, 'Value_geomean',
            "High-Level Productivity (Geometric Mean Improvement over 0-CFA)",
            "benchmarks/new_analysis/plot_high_level_productivity_geomean.png")


# 4. Improvement Ratio Plots (Factors)
# Metrics: impr_precise_val, impr_precise_cont, impr_any_val, impr_any_cont
# We want to plot the Geometric Mean of these Ratios.

def plot_ratio_geomean(data_long, val_metric, cont_metric, title, filename, ylabel):
    df_val = data_long[data_long['MetricType'] == val_metric].copy()
    df_cont = data_long[data_long['MetricType'] == cont_metric].copy()
    
    # Drop NaNs explicitly and print counts
    original_len_val = len(df_val)
    df_val = df_val.dropna(subset=['Value'])
    print(f"[{val_metric}] Dropped {original_len_val - len(df_val)} NaNs from {original_len_val} rows.")
    
    original_len_cont = len(df_cont)
    df_cont = df_cont.dropna(subset=['Value'])
    print(f"[{cont_metric}] Dropped {original_len_cont - len(df_cont)} NaNs from {original_len_cont} rows.")

    # Calculate Geomean of Ratios
    summary_val = df_val.groupby(['Configuration'])['Value'].apply(geometric_mean).reset_index()
    summary_cont = df_cont.groupby(['Configuration'])['Value'].apply(geometric_mean).reset_index()
    
    summary_val['MetricType'] = val_metric
    summary_cont['MetricType'] = cont_metric
    
    summary = pd.concat([summary_val, summary_cont], ignore_index=True)
    summary = summary.rename(columns={'Value': 'Value_geomean'})
    
    print(f"\nSummary for {filename}:")
    print(summary)
    
    plot_dual_axis(summary, 'Value_geomean', title, filename, min_y_val=1.0, min_y_cont=1.0)


# Add new metrics to filtered_data
# Iterate again to extract new columns
filtered_ratio_data = []
for config in configs:
    subset = df_filtered[
        (df_filtered['variant'] == config['variant']) & 
        (df_filtered['d'] == config['d']) & 
        (df_filtered['m'] == config['m'])
    ]
    for _, row in subset.iterrows():
        filtered_ratio_data.append({
            'Configuration': config['label'],
            'MetricType': 'Ratio Precise - Value',
            'Value': row.get('impr_precise_val', np.nan)
        })
        filtered_ratio_data.append({
            'Configuration': config['label'],
            'MetricType': 'Ratio Precise - Continuation',
            'Value': row.get('impr_precise_cont', np.nan)
        })
        filtered_ratio_data.append({
            'Configuration': config['label'],
            'MetricType': 'Ratio Any - Value',
            'Value': row.get('impr_any_val', np.nan)
        })
        filtered_ratio_data.append({
            'Configuration': config['label'],
            'MetricType': 'Ratio Any - Continuation',
            'Value': row.get('impr_any_cont', np.nan)
        })

df_ratio = pd.DataFrame(filtered_ratio_data)

# Plot 1: Ratio of Truly Precise Matches
plot_ratio_geomean(df_ratio, 'Ratio Precise - Value', 'Ratio Precise - Continuation',
                  "Improvement Factor: Fully Resolved Items (Relative to 0-CFA Hits)",
                  "benchmarks/new_analysis/plot_high_level_impr_ratio_precise.png",
                  "Improvement Factor (x)")

# Plot 2: Ratio of Any Improvement
plot_ratio_geomean(df_ratio, 'Ratio Any - Value', 'Ratio Any - Continuation',
                  "Improvement Factor: Any Improvement (Relative to 0-CFA Hits)",
                  "benchmarks/new_analysis/plot_high_level_impr_ratio_any.png",
                  "Improvement Factor (x)")
