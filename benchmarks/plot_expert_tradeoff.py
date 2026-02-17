
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
    if sm is None: return None, None
    num_cont = sm.get('numContAddresses', 0)
    precise = sm.get('contStrSingletons', 0)
    prec = precise/num_cont if num_cont > 0 else 1.0
    return sm.get('numTotalFixInputStates', 0), prec

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
        states, prec = get_metrics(r)
        if states is not None:
             records.append({
                 'Benchmark': bench,
                 'Configuration': label,
                 'Precision': prec,
                 'States': states
             })

df = pd.DataFrame(records)
print(f"Loaded {len(df)} records.")

# Pivot to compare
pivoted = df.pivot(index='Benchmark', columns='Configuration')
pivoted.columns = [f'{c[0]}_{c[1]}' for c in pivoted.columns]
pivoted = pivoted.dropna() # Only keep common benchmarks

print(f"Common benchmarks: {len(pivoted)}")

# Filter for interesting ones (diff > 0.05 in precision OR ratio < 0.8 in states)
pivoted['State_Ratio'] = pivoted['States_1-kCFA'] / pivoted['States_1,1-HMCFAR']
pivoted['Prec_Diff'] = pivoted['Precision_1,1-HMCFAR'] - pivoted['Precision_1-kCFA']

# Subset for plotting
subset = pivoted[ (pivoted['State_Ratio'] < 0.9) | (pivoted['Prec_Diff'].abs() > 0.05) ]
print(f"Subset size: {len(subset)}")

# Flatten for plotting
plot_data = []
for idx, row in subset.iterrows():
    plot_data.append({'Benchmark': idx, 'Configuration': '1-kCFA', 'States': row['States_1-kCFA'], 'Precision': row['Precision_1-kCFA']})
    plot_data.append({'Benchmark': idx, 'Configuration': '1,1-HMCFAR', 'States': row['States_1,1-HMCFAR'], 'Precision': row['Precision_1,1-HMCFAR']})

plot_df = pd.DataFrame(plot_data)

plt.figure(figsize=(7, 4))
sns.set_theme(style="whitegrid", font_scale=1.4)

# Scatterplot
sns.scatterplot(data=plot_df, x='States', y='Precision', hue='Configuration', style='Configuration', s=100, palette="deep")

# plt.xscale('log')
plt.xlabel("State Space Size", fontsize=12)
plt.ylabel("Continuation Precision", fontsize=12)
plt.title("Cost-Precision Tradeoff: 1-kCFA vs 1,1-HMCFAR", fontsize=14)

# Draw lines connecting same benchmarks
# We iterate through the unique benchmarks in plot_df
for bench in plot_df['Benchmark'].unique():
    subset_b = plot_df[plot_df['Benchmark'] == bench]
    if len(subset_b) == 2:
        k_pt = subset_b[subset_b['Configuration'] == '1-kCFA'].iloc[0]
        d_pt = subset_b[subset_b['Configuration'] == '1,1-HMCFAR'].iloc[0]
        
        # Color based on direction
        # Red: Precision Decreases
        # Green: Precision Increases AND States Decreases (Win-Win)
        # Blue: Precision Increases BUT States Increases (Trade-off)
        # Gray: Small change
        
        prec_gain = d_pt['Precision'] - k_pt['Precision']
        state_ratio = d_pt['States'] / k_pt['States'] if k_pt['States'] > 0 else 1.0
        
        color = 'gray'
        alpha = 0.3
        
        if prec_gain < -0.01: # Worse Precision
            color = 'red'
            alpha = 0.6
        elif prec_gain > 0:
            if state_ratio < 1.0:
                color = 'green' # Smaller & Better
            else:
                color = 'blue' # Larger & Better
            alpha = 0.6
            
        plt.plot([k_pt['States'], d_pt['States']], [k_pt['Precision'], d_pt['Precision']], color=color, alpha=alpha, linewidth=1)
        
        # Annotate specific interesting cases
        if 'scoped/example2' in bench:
            plt.text(k_pt['States'], k_pt['Precision'], 'scoped/example2 (kCFA)', fontsize=9, ha='right')
        if 'complex-layers' in bench:
            plt.text(d_pt['States'], d_pt['Precision'], 'complex-layers (HMCFAR)', fontsize=9, ha='left')

plt.legend(bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0.)
plt.tight_layout(pad=0.2)
plt.savefig("benchmarks/new_analysis/plot_expert_tradeoff.png")
print("Saved plot_expert_tradeoff.png")
