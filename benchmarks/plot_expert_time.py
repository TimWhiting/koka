
import json
import os
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns

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
    times = run.get('analysisTimes', [])
    min_time = min(times) if times else 0.0
    return sm.get('numTotalFixInputStates', 0), prec, min_time

print("Loading cached results...")
data = load_results()

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
        if real_k == 1: label = '1-kCFA'
    elif v == 'dmcfar':
        if m == 1 and d == 1: label = '1,1-HMCFAR'
        
    if label:
        states, prec, time_sec = get_metrics(r)
        if states is not None:
             records.append({
                 'Benchmark': bench,
                 'Configuration': label,
                 'Precision': prec,
                 'States': states,
                 'Time': time_sec * 1000.0 # Convert to ms
             })

df = pd.DataFrame(records)
print(f"Loaded {len(df)} records.")

# Pivot to compare
pivoted = df.pivot(index='Benchmark', columns='Configuration')
pivoted.columns = [f'{c[0]}_{c[1]}' for c in pivoted.columns]
pivoted = pivoted.dropna() # Only keep common benchmarks

print(f"Common benchmarks: {len(pivoted)}")

# Filter for interesting ones
# We are interested if Time differs significantly OR Precision differs significantly
pivoted['Time_Ratio'] = pivoted['Time_1-kCFA'] / pivoted['Time_1,1-HMCFAR']
pivoted['Prec_Diff'] = pivoted['Precision_1,1-HMCFAR'] - pivoted['Precision_1-kCFA']

# Subset for plotting
# Interesting: Time ratio < 0.8 (HMCFAR slower) or > 1.25 (HMCFAR faster) OR Prec Delta > 0.05
subset = pivoted[ (pivoted['Time_Ratio'] < 0.8) | (pivoted['Time_Ratio'] > 1.25) | (pivoted['Prec_Diff'].abs() > 0.05) ]
print(f"Subset size: {len(subset)}")

# Flatten for plotting
plot_data = []
for idx, row in subset.iterrows():
    plot_data.append({'Benchmark': idx, 'Configuration': '1-kCFA', 'Time': row['Time_1-kCFA'], 'Precision': row['Precision_1-kCFA']})
    plot_data.append({'Benchmark': idx, 'Configuration': '1,1-HMCFAR', 'Time': row['Time_1,1-HMCFAR'], 'Precision': row['Precision_1,1-HMCFAR']})

plot_df = pd.DataFrame(plot_data)

plt.figure(figsize=(10, 8))
sns.set_theme(style="whitegrid")

# Scatterplot
sns.scatterplot(data=plot_df, x='Time', y='Precision', hue='Configuration', style='Configuration', s=100, palette="deep")

plt.xscale('log')
plt.xlabel("Analysis Time (ms) - Log Scale", fontsize=12)
plt.ylabel("Continuation Precision", fontsize=12)
plt.title("Time-Precision Tradeoff: 1-kCFA vs 1,1-HMCFAR", fontsize=14)

# Draw lines connecting same benchmarks
for bench in plot_df['Benchmark'].unique():
    subset_b = plot_df[plot_df['Benchmark'] == bench]
    if len(subset_b) == 2:
        k_pt = subset_b[subset_b['Configuration'] == '1-kCFA'].iloc[0]
        d_pt = subset_b[subset_b['Configuration'] == '1,1-HMCFAR'].iloc[0]
        
        # Color based on direction
        # Red: Precision Decreases
        # Green: Precision Increases AND Time Decreases (Win-Win)
        # Blue: Precision Increases BUT Time Increases (Trade-off)
        # Gray: Small change
        
        prec_gain = d_pt['Precision'] - k_pt['Precision']
        time_ratio = d_pt['Time'] / k_pt['Time'] if k_pt['Time'] > 0 else 1.0
        
        color = 'gray'
        alpha = 0.3
        
        if prec_gain < -0.01: # Worse Precision (allow small noise)
            color = 'red'
            alpha = 0.6
        elif prec_gain > 0:
            if time_ratio < 1.0:
                color = 'green' # Faster & Better
            else:
                color = 'blue' # Slower & Better
            alpha = 0.6
            
        plt.plot([k_pt['Time'], d_pt['Time']], [k_pt['Precision'], d_pt['Precision']], color=color, alpha=alpha, linewidth=1)
        
        # Annotate specific interesting cases
        if 'scoped/example2' in bench:
            plt.text(k_pt['Time'], k_pt['Precision'], 'scoped/example2 (kCFA)', fontsize=9, ha='right')
        # if 'complex-layers' in bench: ...

plt.tight_layout()
plt.savefig("benchmarks/new_analysis/plot_expert_time_tradeoff.png")
print("Saved plot_expert_time_tradeoff.png")
