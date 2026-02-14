
import json
import os
import pandas as pd
import numpy as np

# --- 1. Load Data (Reusing logic from cost_analysis.py) ---
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
                except:
                    pass
    return results

def compute_metrics(run, baseline):
    m = run.get('storeMetrics', {})
    b = baseline.get('storeMetrics', {}) if baseline else {}
    
    # Calculate Absolute Precision (Continuation)
    # Similar logic to cost_analysis.py / new_analysis.py
    # ... (simplified for this script)
    
    # Helper to calculate absolute precision
    def get_abs_prec(metric_map_name, m_data, b_data):
        m_map = m_data.get(metric_map_name, {})
        b_map = b_data.get(metric_map_name, {})
        
        total_vars = 0
        precise_vars = 0
        
        # We iterate over all variables present in EITHER
        all_keys = set(m_map.keys()) | set(b_map.keys())
        
        for k in all_keys:
            m_val = m_map.get(k, 0) # 0 means optimized away/not present
            b_val = b_map.get(k, 0)
            
            # Count towards total? Yes, if it exists in baseline or current
            # (Using a simplified definition for "compare two specific runs")
            # Actually, let's just use the metrics already computed if we can.
            # But cost_analysis.py computes them on the fly.
            
            # Let's use the definition:
            # Precise if size <= 1 OR optimized away (size=0)
            # BUT: If it was ALREADY precise in baseline (size<=1), we credit it.
            # Here we are comparing 1-kCFA vs 1,1-DMCFAR. We want to see their precisions relative to 0-CFA.
            pass
        return 0 # Placeholder
        
    # Re-using strict definition from new_analysis.py is best.
    # I'll just copy the calculate logic inline effectively.
    
    # Actually, simpler: just get the computed metrics from cost_analysis logic if I import it?
    # No, let's just write a targeted analysis of the raw JSONs for the comparisons we care about.
    
    # We want to compare:
    # 1. k-CFA (k=1)
    # 2. DMCFAR (1,1)  (d=1, m=1)
    # 3. Baseline (k=0 / d=0,m=0)
    
    return {} # Placeholder

# --- Real Logic ---

rows = []
all_data = load_results()

# Organize by benchmark
benchmarks = {}
for r in all_data:
    name = r.get('benchmarkName')
    if name not in benchmarks: benchmarks[name] = []
    benchmarks[name].append(r)

analysis_data = []

print(f"Loaded {len(benchmarks)} benchmarks.")

for bname, runs in benchmarks.items():
    # Find relevant runs
    # Baseline: k=0 (kcfa) OR d=0,m=0 (dmcfar)
    # We generally treat 0-CFA as the common baseline. 
    # Let's find a run with k=0 OR (d=0 and m=0).
    
    base = None
    kcfa_1 = None
    dmcfar_1_1 = None
    
    first_bench = True
    for r in runs:
        v = r.get('variant', '')
        k = r.get('k', 0)
        m = r.get('m', 0)
        d = r.get('d', 0)
        
        if first_bench and bname == 'analysis/benchmarks/koka-gen/interp2/err1': # Debug one bench
             print(f"DEBUG: {bname} - v={v}, k={k}, m={m}, d={d}")

        # Correction for k stored in m for kcfa
        if v == 'kcfa':
            real_k = m 
            # if real_k == 0: base = r # potential baseline
            if real_k == 1: kcfa_1 = r
        elif v == 'dmcfar':
            if m == 0 and d == 0: base = r # potential baseline
            if m == 1 and d == 1: dmcfar_1_1 = r
            
    first_bench = False

    if not base or not kcfa_1 or not dmcfar_1_1:
        continue
        
    # Analyze
    def get_metrics(run):
        sm = run.get('storeMetrics')
        if sm is None: return None, None
        states = sm.get('numTotalFixInputStates', 0)
        
        # Calculate simplistic precision for sorting
        # % of singletons in Cont Store
        # structToContStrSizes is empty in some jsons, use aggregate counts
        num_cont = sm.get('numContAddresses', 0)
        precise = sm.get('contStrSingletons', 0)
        return states, (precise/num_cont if num_cont > 0 else 1.0)

    b_states, b_prec = get_metrics(base)
    k_states, k_prec = get_metrics(kcfa_1)
    d_states, d_prec = get_metrics(dmcfar_1_1)
    
    if b_states is None or k_states is None or d_states is None:
        continue
    
    # Wins?
    # kCFA wins on states if k_states < d_states
    # But only interesting if k_prec is comparable to d_prec
    
    row = {
        'Benchmark': bname,
        'Base_States': b_states,
        'kCFA_States': k_states,
        'DMCFAR_States': d_states,
        'kCFA_Prec': k_prec,
        'DMCFAR_Prec': d_prec,
        'State_Ratio_k_vs_d': k_states / d_states if d_states > 0 else 0,
        'Prec_Diff_k_vs_d': k_prec - d_prec
    }
    analysis_data.append(row)

df = pd.DataFrame(analysis_data)
if df.empty:
    print("No matching benchmarks found with all 3 runs.")
    exit()

# Filter for interesting cases
# 1. kCFA wins on states (Ratio < 1.0)
# 2. kCFA has comparable or better precision (Prec Diff > -0.05) or just meaningful precision
kcfa_wins = df[ (df['State_Ratio_k_vs_d'] < 0.9) & (df['Prec_Diff_k_vs_d'] > -0.05) ]

print(f"\nFound {len(kcfa_wins)} benchmarks where kCFA(k=1) is >10% more state-efficient than DMCFAR(1,1) with comparable precision.")
print(kcfa_wins[['Benchmark', 'State_Ratio_k_vs_d', 'kCFA_Prec', 'DMCFAR_Prec', 'kCFA_States', 'DMCFAR_States']].sort_values('State_Ratio_k_vs_d').to_markdown(index=False))

# Also look for where DMCFAR destroys kCFA in precision
dmcfa_wins_prec = df[ df['Prec_Diff_k_vs_d'] < -0.10 ]
print(f"\nFound {len(dmcfa_wins_prec)} benchmarks where DMCFAR(1,1) is >10% more precise than kCFA(k=1).")
print(dmcfa_wins_prec[['Benchmark', 'Prec_Diff_k_vs_d', 'kCFA_Prec', 'DMCFAR_Prec']].sort_values('Prec_Diff_k_vs_d').to_markdown(index=False))

