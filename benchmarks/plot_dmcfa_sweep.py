
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
    if sm is None: return None
    num_cont = sm.get('numContAddresses', 0)
    precise = sm.get('contStrSingletons', 0)
    prec = precise/num_cont if num_cont > 0 else 1.0
    return prec

print("Loading cached results...")
data = load_results()

records = []
for r in data:
    v = r.get('variant', '')
    k = r.get('k', 0)
    m = r.get('m', 0)
    d = r.get('d', 0)
    bench = r.get('benchmarkName', '')
    
    if v == 'dmcfar':
        # Filter spurious high values if any
        if m > 5 or d > 5: continue 
        
        prec = get_metrics(r)
        if prec is not None:
             records.append({
                 'Benchmark': bench,
                 'm': m,
                 'd': d,
                 'Precision': prec
             })

df = pd.DataFrame(records)
print(f"Loaded {len(df)} DMCFAR records.")

# Aggregate
# We want Median Precision for each (m,d) pair
heatmap_data = df.groupby(['m', 'd'])['Precision'].median().reset_index()

# Pivot for heatmap? No, user wants to sweep m.
# Line plot: X=m, Y=Precision, Hue=h
# Filter for reasonable ranges
df = df[ (df['m'] <= 5) & (df['d'] <= 2) ]

plt.figure(figsize=(8, 6))
sns.set_theme(style="whitegrid")

# Rename d to h for display
df['h'] = df['d']

sns.lineplot(data=df, x='m', y='Precision', hue='h', style='h', markers=True, palette="viridis", linewidth=1.5)

plt.title("Effect of Call Sensitivity (m)", fontsize=14)
plt.xlabel("Call Context Sensitivity (m)", fontsize=12)
plt.ylabel("Median Continuation Precision", fontsize=12)
plt.xticks(sorted(df['m'].unique()))
plt.ylim(0.5, 1.05)

plt.tight_layout()
plt.savefig("benchmarks/new_analysis/plot_dmcfa_sweep_line.png")
print("Saved plot_dmcfa_sweep_line.png")
