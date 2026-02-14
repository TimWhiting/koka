
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
    precise_val = sm.get('valStrSingletons', 0) + (sm.get('numLitAddresses', 0) - sm.get('literal0CFATopCount', 0))
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
# Define order fixed
order = ['0-CFA', '1-kCFA', '2-kCFA', '1,0-HMCFAR', '1,1-HMCFAR', '1,2-HMCFAR']

# Plotting Function
def plot_precision(data, metric_col, error_col_lower, error_col_upper, title, filename, ylabel):
    plt.figure(figsize=(12, 7))
    sns.set_theme(style="whitegrid")
    
    # We use hue_order corresponding to MetricType
    hue_order = ['Continuation Precision', 'Value Precision']
    
    ax = sns.barplot(x='Configuration', y=metric_col, hue='MetricType', data=data,
                     order=order, hue_order=hue_order,
                     palette="viridis")
    
    # Add error bars
    if error_col_lower and error_col_upper:
        for j, metric in enumerate(hue_order):
            if j >= len(ax.containers): break
            container = ax.containers[j]
            
            for k, bar in enumerate(container):
                if k >= len(order): continue
                config = order[k]
                
                row = data[(data['Configuration'] == config) & (data['MetricType'] == metric)]
                if row.empty: continue
                
                val = row[metric_col].values[0]
                lower = row[error_col_lower].values[0]
                upper = row[error_col_upper].values[0]
                
                # yerr relative to val
                yerr_lower = val - lower
                yerr_upper = upper - val
                
                if pd.isna(yerr_lower) or pd.isna(yerr_upper): continue

                ax.errorbar(bar.get_x() + bar.get_width()/2, val, 
                            yerr=[[yerr_lower], [yerr_upper]],
                            fmt='none', c='black', capsize=5)
                
                # Annotate
                ax.annotate(f'{val:.2f}', (bar.get_x() + bar.get_width() / 2., val),
                            ha='center', va='bottom', xytext=(0, 5), textcoords='offset points', fontsize=10)

    else:
        # Just annotate values
         for j, metric in enumerate(hue_order):
            if j >= len(ax.containers): break
            container = ax.containers[j]
            for k, bar in enumerate(container):
                if k >= len(order): continue
                config = order[k]
                row = data[(data['Configuration'] == config) & (data['MetricType'] == metric)]
                if row.empty: continue
                val = row[metric_col].values[0]
                ax.annotate(f'{val:.2f}', (bar.get_x() + bar.get_width() / 2., val),
                            ha='center', va='bottom', xytext=(0, 5), textcoords='offset points', fontsize=10)

    ax.set_title(title, fontsize=14)
    ax.set_ylabel(ylabel, fontsize=12)
    ax.set_ylim(0, 1.15)
    plt.tight_layout()
    plt.savefig(filename)
    print(f"Saved {filename}")

# 1. Geomean Plot
# Prepare error columns
summary['Lower'] = summary['GMean'] / summary['GSD']
summary['Upper'] = summary['GMean'] * summary['GSD']

plot_precision(summary, 'GMean', 'Lower', 'Upper',
               f"Geometric Mean Precision (N={len(complex_bench_names)})",
               "benchmarks/new_analysis/plot_high_level_precision_geomean.png",
               "Geomean Precision")

# 2. Median Plot
plot_precision(summary_median, 'Median', None, None,
               f"Median Precision (N={len(complex_bench_names)})",
               "benchmarks/new_analysis/plot_high_level_precision_median.png",
               "Median Precision")
