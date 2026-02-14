
import json
import os
import pandas as pd
import numpy as np

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
    return sm.get('numTotalFixInputStates', 0)

data = load_results()

# Group by benchmark
benchmarks = {}
for r in data:
    b = r.get('benchmarkName')
    if b not in benchmarks: benchmarks[b] = {}
    
    v = r.get('variant')
    k = r.get('k', 0)
    m = r.get('m', 0)
    d = r.get('d', 0)
    
    label = None
    if v == 'kcfa':
        real_k = k if k > 0 else m
        if real_k == 1: label = '1-kCFA'
    elif v == 'dmcfar' and m == 1 and d == 1:
        label = '1,1-DMCFAR'
    elif v == 'dmcfae' and m == 1 and d == 1:
        label = '1,1-DMCFAE'
        
    if label:
        benchmarks[b][label] = get_metrics(r)

# Filter for benchmarks having all 3 (or at least kCFA and DMCFAR to identify wins)
records = []
for b, variants in benchmarks.items():
    kcfa = variants.get('1-kCFA')
    dmcfar = variants.get('1,1-DMCFAR')
    dmcfae = variants.get('1,1-DMCFAE')
    
    if kcfa is not None and dmcfar is not None:
        # Check if kCFA wins significantly (Ratio < 0.9)
        ratio = kcfa / dmcfar if dmcfar > 0 else 1.0
        if ratio < 0.9:
            rec = {
                'Benchmark': b,
                '1-kCFA': kcfa,
                '1,1-DMCFAR': dmcfar,
                '1,1-DMCFAE': dmcfae, # Might be None
                'Ratio_k_vs_R': ratio,
            }
            if dmcfae is not None:
                rec['Ratio_E_vs_R'] = dmcfae / dmcfar if dmcfar > 0 else 1.0
                rec['Ratio_k_vs_E'] = kcfa / dmcfae if dmcfae > 0 else 1.0
                rec['Diff_R_vs_E'] = dmcfar - dmcfae
            
            records.append(rec)

df = pd.DataFrame(records)

if df.empty:
    print("No relevant benchmarks found.")
else:
    # Sort by kCFA win ratio
    df = df.sort_values('Ratio_k_vs_R')
    
    # Select columns
    cols = ['Benchmark', '1-kCFA', '1,1-DMCFAE', '1,1-DMCFAR', 'Diff_R_vs_E', 'Ratio_E_vs_R']
    print(df[cols].to_markdown(index=False))

    # Calculate average overhead
    valid_e = df.dropna(subset=['1,1-DMCFAE'])
    avg_reduction = (valid_e['1,1-DMCFAR'] - valid_e['1,1-DMCFAE']).mean()
    print(f"\nAverage State Reduction (R - E): {avg_reduction:.2f}")
    print(f"Median Ratio (E / R): {valid_e['Ratio_E_vs_R'].median():.2f}")
