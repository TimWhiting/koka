
import pandas as pd
import json
import traceback
from plot_utils import load_results_with_baselines, get_complex_benchmarks, prepare_tradeoff_data

# 1. Load Global Results
print("Loading results...")
results = load_results_with_baselines("benchmarks/results-cached")
df = pd.DataFrame(results)

# Filter Complex
complex_bench = get_complex_benchmarks(df, threshold=0.99)
print(f"Complex Benchmarks: {len(complex_bench)}")

# Compare 1-kCFA vs 1,2-HMCFAR
c_kcfa = {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'}
c_hmcfa = {'variant': 'dmcfar', 'd': 1, 'm': 2, 'label': '1,2-HMCFAR'}

metrics = {
    'Cont_Prec_Imp': 'prod_k_str',
    'Abs_Cont_Prec': 'AbsContPrecision',
    'States': 'States'
}

df_comp = prepare_tradeoff_data(results, c_kcfa, c_hmcfa, metrics)

# Filter for complex only
df_comp = df_comp[df_comp['benchmarkName'].isin(complex_bench)]

# Calculate diffs
df_comp['Diff_Cont_Imp'] = df_comp['Cont_Prec_Imp_New'] - df_comp['Cont_Prec_Imp_Base']
df_comp['Diff_Abs_Cont'] = df_comp['Abs_Cont_Prec_New'] - df_comp['Abs_Cont_Prec_Base']

# Global Stats
print("\n--- Statistics (Global) ---")
print(df_comp[['Cont_Prec_Imp_Base', 'Cont_Prec_Imp_New']].describe())

# 2. Deep Dive into mymakefile-example3
target = "analysis/benchmarks/koka-gen/build/mymakefile-example3"
print(f"\n--- Deep Dive: {target} ---")

base_path = "benchmarks/results-cached/kcfa/0/0/analysis/benchmarks/koka-gen/build/mymakefile-example3.json"
new_path = "benchmarks/results-cached/dmcfar/1/2/analysis/benchmarks/koka-gen/build/mymakefile-example3.json"

try:
    with open(base_path, 'r') as f:
        base_run = json.load(f)
    with open(new_path, 'r') as f:
        new_run = json.load(f)
    
    if 'storeMetrics' not in base_run:
        print(f"Base Run Missing storeMetrics! Keys: {list(base_run.keys())}")
    else:
        print(f"Base Run storeMetrics Keys: {list(base_run['storeMetrics'].keys())}")
        
    # Inspect structToContStrSizes (Reverted)
    metric_name = 'structToContStrSizes'
    b_map = base_run.get('storeMetrics', {}).get(metric_name, {})
    n_map = new_run.get('storeMetrics', {}).get(metric_name, {})
    
    print(f"\nMetric: {metric_name}")
    print(f"Baseline Map Keys: {len(b_map)}")
    print(f"New Run Map Keys: {len(n_map)}")
    
    if len(b_map.keys()) > 0:
        print("Baseline Sample keys:", list(b_map.keys())[:5])
        
    common = set(b_map.keys()).intersection(set(n_map.keys()))
    print(f"Common Keys: {len(common)}")
    
    hits = 0
    total = 0
    for x_id, base_vals in b_map.items():
        szs = n_map.get(x_id)
        if isinstance(base_vals, list): base_val = base_vals[0]
        else: base_val = base_vals
        poly_val = szs
        if isinstance(szs, list): poly_val = szs[0]
        
        if base_val == -1:
            if poly_val is not None and poly_val != -1:
                hits += 1
            total += 1
            continue
            
        if poly_val is not None and poly_val != -1 and poly_val < base_val:
            hits += 1
        total += 1
        
    print(f"Manual Calc for {metric_name}: Hits={hits}, Total={total}, Prod={hits/total if total > 0 else 0}")

except Exception:
    import traceback
    traceback.print_exc()
