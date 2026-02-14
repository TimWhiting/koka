
import json
import os
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns

# Reuse loading logic
def load_results(base_dir="benchmarks/results-cached"):
    results = []
    for root, _, files in os.walk(base_dir):
        for file in files:
            if file.endswith(".json"):
                try:
                    with open(os.path.join(root, file), 'r') as f:
                        data = json.load(f)
                        data['filePath'] = os.path.join(root, file)
                        results.append(data)
                except: pass
    return results

def get_metrics(run):
    sm = run.get('storeMetrics')
    if sm is None: return None, None, None
    num_cont = sm.get('numContAddresses', 0)
    precise = sm.get('contStrSingletons', 0)
    prec = precise/num_cont if num_cont > 0 else 1.0
    
    num_store = sm.get('numStructAddresses', 0) + sm.get('numLitAddresses', 0)
    precise_val = sm.get('valStrSingletons', 0) + (sm.get('numLitAddresses', 0) - sm.get('literalTopCount', 0))
    val_prec = precise_val/num_store if num_store > 0 else 1.0
    
    return sm.get('numTotalFixInputStates', 0), prec, val_prec

print("Loading cached results...")
data = load_results()

# Filter for relevant configurations
# 1. 0-CFA (Baseline) -> k=0 or (m=0,d=0)
# 2. 1-kCFA -> k=1 (or m=1 for kcfa variant)
# 3. 1,1-DMCFAR -> m=1, d=1

records = []
for r in data:
    v = r.get('variant', '')
    k = r.get('k', 0)
    m = r.get('m', 0)
    d = r.get('d', 0)
    bench = r.get('benchmarkName', '')
    
    label = None
    if v == 'kcfa':
        real_k = k if k > 0 else m
        # if real_k == 0: label = '0-CFA'
        if real_k == 1: label = '1-kCFA'
        elif real_k == 2: label = '2-kCFA'
    elif v == 'dmcfar':
        if m == 0 and d == 0: label = '0-CFA' 
        elif m == 0 and d == 1: label = '1,0-HMCFAR' # h=1
        elif m == 1 and d == 1: label = '1,1-HMCFAR' # h=1
        elif m == 2 and d == 1: label = '1,2-HMCFAR' # h=1
        
    if label:
        states, prec, val_prec = get_metrics(r)
        if states is not None:
             records.append({
                 'Benchmark': bench,
                 'Configuration': label,
                 'ContinuationPrecision': prec,
                 'ValuePrecision': val_prec,
                 'Solved': 1
             })

df = pd.DataFrame(records)
print(f"Loaded {len(df)} records.")

# Aggregate per benchmark
df = df.drop_duplicates(subset=['Benchmark', 'Configuration'])

# Metric 1: Success Rate on "Complex" Benchmarks
complex_bench_names = df[ (df['Configuration'] == '0-CFA') & (df['ContinuationPrecision'] < 0.99) ]['Benchmark'].unique()
print(f"Identified {len(complex_bench_names)} complex benchmarks (0-CFA Prec < 0.99).")

df_complex = df[df['Benchmark'].isin(complex_bench_names)]

# Melt to long format for Seaborn
df_long = df_complex.melt(id_vars=['Benchmark', 'Configuration', 'Solved'], 
                          value_vars=['ContinuationPrecision', 'ValuePrecision'], 
                          var_name='MetricType', value_name='PrecisionValue')

# Rename metric types for display
df_long['MetricType'] = df_long['MetricType'].replace({
    'ContinuationPrecision': 'Continuation Precision',
    'ValuePrecision': 'Value Precision'
})

print(df_long.head())

from scipy.stats import gmean

def geometric_mean(data):
    # Add epsilon to avoid log(0)
    return gmean(np.array(data) + 1e-9)

def geometric_sd(data):
    # GSD = exp(std(log(data)))
    log_data = np.log(np.array(data) + 1e-9)
    return np.exp(np.std(log_data))

# Print summary stats (Geomean)
summary_gmean = df_long.groupby(['Configuration', 'MetricType'])['PrecisionValue'].apply(geometric_mean).reset_index()
summary_gsd = df_long.groupby(['Configuration', 'MetricType'])['PrecisionValue'].apply(geometric_sd).reset_index()

summary = pd.merge(summary_gmean, summary_gsd, on=['Configuration', 'MetricType'], suffixes=('_mean', '_sd'))
summary = summary.rename(columns={'PrecisionValue_mean': 'GMean', 'PrecisionValue_sd': 'GSD'})

print("\nGeomean Precision Summary based on samples:")
pd.set_option('display.max_columns', None)
pd.set_option('display.width', 1000)
print(summary)

# Calculate Median summary
summary_median = df_long.groupby(['Configuration', 'MetricType'])['PrecisionValue'].median().reset_index()
summary_median = summary_median.rename(columns={'PrecisionValue': 'Median'})

print("\nMedian Precision Summary:")
print(summary_median)

# Plot
plt.figure(figsize=(12, 7))
sns.set_theme(style="whitegrid")

# We want Assymetric Error Bars: Upper = GMean * GSD, Lower = GMean / GSD
# yerr needs to be (2, N) where row 0 is lower errors (Mean - Lower), row 1 is upper errors (Upper - Mean)

# To plot with hue and custom error bars in Seaborn is hard.
# We will use sns.barplot to draw the bars (height=GMean) and then loop to draw error bars?
# Or we can just use the 'ci' from bootstrap if we define a custom estimator?
# The user asked for "equivalent of stddev", so GSD interval is best.
# Bootstrapping gmean is also valid and easier in Seaborn: errorbar=('ci', 95), estimator=gmean.
# But user specifically asked for "stddev equivalent".
# Let's try to pass errorbar=None and add them manually, or use matplotlib directly.

# Simplified: Use bootstrap CI for Geomean. It is statistically sound and "equivalent" in spirit (uncertainty).
# User said: "equivalent of stddev / stderr for geomean".
# GSD matches this best. 
# Let's compute yerr manually and plot.

order = ['0-CFA', '1-kCFA', '2-kCFA', '1,0-HMCFAR', '1,1-HMCFAR', '1,2-HMCFAR']

# Bar chart of Geomean Precision without error bars first
ax = sns.barplot(x='Configuration', y='PrecisionValue', hue='MetricType', data=df_long,
                 order=order,
                 palette="viridis", estimator=geometric_mean, errorbar=None)

# Add error bars manually
# We need to iterate bars and find corresponding GSD
# This depends on the exact order of patches.
# Seaborn plots hue groups together... actually it interleaves them?
# Let's rely on matching coordinates.

# Collect data for simple lookup
lookup = summary.set_index(['Configuration', 'MetricType'])

for i, p in enumerate(ax.patches):
    # Identify bar
    height = p.get_height()
    if height == 0 or np.isnan(height): continue
    
    # Get config from x-tick
    # x-ticks are 0, 1, 2...
    # The patch x position tells us which hue it is.
    # But seaborn behavior varies.
    # Robust way: iterate (Config, Type) in the order seaborn plots them.
    # Seaborn plots all bars for Hue=0, then all bars for Hue=1? No, usually nested.
    pass 

# Actually, standard Seaborn barplot with hue plots:
# Group 1 (Config 1): Bar 1 (Hue 1), Bar 2 (Hue 2)...
# No, Seaborn < 0.12 often plotted all hue 1 bars then all hue 2 bars.
# Seaborn >= 0.12 (check version? assume recent).
# Let's try a safer approach: Calculate error bars and use plt.errorbar based on bar centers.

# Correct iteration:
# Get x locations
# For each patch:
#   cx = p.get_x() + p.get_width()/2
#   cy = height
#   We need to know WHICH config and metric this is.
#   We can deduce MetricType from the patch color or order?
#   If we have 2 hue levels, ax.containers[0] is Hue 0, ax.containers[1] is Hue 1.

hue_order = sorted(df_long['MetricType'].unique()) # Check if seaborn sorts? default is sorted?
# Actually default is appearance order or sorted?
# Let's specify hue_order explicitly to be safe.
hue_order = ['Continuation Precision', 'Value Precision']

# Re-plot to ensure order
plt.clf()
ax = sns.barplot(x='Configuration', y='PrecisionValue', hue='MetricType', data=df_long,
                 order=order, hue_order=hue_order,
                 palette="viridis", estimator=geometric_mean, errorbar=None)

# Add error bars
print(f"Number of containers: {len(ax.containers)}")
print(f"Hue order: {hue_order}")

for j, container in enumerate(ax.containers):
    if j >= len(hue_order): break # Avoid index error if extra containers
    metric = hue_order[j]
    # Container has bars for each config in 'order'
    for k, bar in enumerate(container):
        if k >= len(order): continue
        config = order[k]
        # Look up
        try:
            row = lookup.loc[(config, metric)]
            gm = row['GMean']
            gsd = row['GSD']
            
            lower = gm / gsd
            upper = gm * gsd
            
            yerr_lower = gm - lower
            yerr_upper = upper - gm
            
            ax.errorbar(bar.get_x() + bar.get_width()/2, gm, 
                        yerr=[[yerr_lower], [yerr_upper]],
                        fmt='none', c='black', capsize=5)
            
            # Annotate
            ax.annotate(f'{gm:.2f}', (bar.get_x() + bar.get_width() / 2., gm),
                        ha='center', va='bottom', xytext=(0, 5), textcoords='offset points', fontsize=10)
        except KeyError:
            pass

ax.set_title(f"Geometric Mean Precision (N={len(complex_bench_names)})", fontsize=14)
ax.set_ylabel("Geomean Precision", fontsize=12)
ax.set_ylim(0, 1.15) # More space for annotations
# ax.legend(title="Precision Type") # Already there

plt.tight_layout()
plt.savefig("benchmarks/new_analysis/plot_high_level_precision.png")
print("Saved plot_high_level_precision.png")
