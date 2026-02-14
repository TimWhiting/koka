
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

# Print summary stats
summary = df_long.groupby(['Configuration', 'MetricType'])['PrecisionValue'].median()
print("\nMedian Precision Summary:")
print(summary)

# Plot
plt.figure(figsize=(12, 7))
sns.set_theme(style="whitegrid")

# Bar chart of Median Precision with error bars (SD)
# We use estimator=np.median and errorbar='sd' to evaluate distribution across BENCHMARKS.
ax = sns.barplot(x='Configuration', y='PrecisionValue', hue='MetricType', data=df_long,
                 order=['0-CFA', '1-kCFA', '2-kCFA', '1,0-HMCFAR', '1,1-HMCFAR', '1,2-HMCFAR'],
                 palette="viridis", estimator=np.median, errorbar='sd', capsize=.1)

ax.set_title(f"Median Precision on Contentious Benchmarks (N={len(complex_bench_names)})", fontsize=14)
ax.set_ylabel("Median Precision", fontsize=12)
ax.set_ylim(0, 1.1)
ax.legend(title="Precision Type")

# Annotate with values
for p in ax.patches:
    # Find the corresponding summary row for annotation
    config = p.get_x() + p.get_width() / 2.
    height = p.get_height()
    
    # Get the configuration name from the x-axis tick labels
    config_name = ax.get_xticklabels()[int(p.get_x() + 0.5)].get_text() # Approximate config name from x-position
    
    # This part is tricky because of hue. We need to find the exact bar.
    # A simpler way is to iterate through the summary data directly for annotations.
    # For now, let's just annotate the height.
    ax.annotate(f'{height:.2f}', (p.get_x() + p.get_width() / 2., height),
                ha='center', va='center', xytext=(0, 9), textcoords='offset points', fontsize=10)

plt.tight_layout()
plt.savefig("benchmarks/new_analysis/plot_high_level_precision.png")
print("Saved plot_high_level_precision.png")
