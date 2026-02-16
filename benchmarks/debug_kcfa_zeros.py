
import os
import json
import pandas as pd
from plot_utils import load_results_with_baselines, get_complex_benchmarks, filter_common_benchmarks, compute_metrics

def inspect_zeros():
    print("Loading results...")
    # Load raw list first to get file paths
    base_dir = "benchmarks/results-cached"
    all_runs = []
    
    for root, _, files in os.walk(base_dir):
        for file in files:
            if file.endswith(".json"):
                try:
                    with open(os.path.join(root, file), 'r') as f:
                        data = json.load(f)
                        data['filePath'] = os.path.join(root, file)
                        all_runs.append(data)
                except: pass
                
    # Convert to standard format via utils to identify zeros
    processed = load_results_with_baselines(base_dir)
    df = pd.DataFrame(processed)
    
    # Filter for complex
    complex_bench = get_complex_benchmarks(df)
    df = df[df['benchmarkName'].isin(complex_bench)]
    
    # Check 1-kCFA prod_k_str
    subset = df[ (df['variant'] == 'kcfa') & (df['d'] == 0) & (df['m'] == 1) ]
    
    # metrics['prod_k_str'] values
    zeros = subset[subset['prod_k_str'] == 0]
    
    print(f"\nFound {len(zeros)} benchmarks with 0.0 Continuation Improvement for 1-kCFA.")
    
    if len(zeros) > 0:
        # Pick top 5 to inspect
        targets = zeros['benchmarkName'].head(5).tolist()
        print(f"Inspecting: {targets}")
        
        for bench in targets:
            print(f"\n=== Inspecting {bench} ===")
            
            # Find Baseline (0-CFA) and 1-kCFA runs in ALL_RUNS (raw)
            base_run = None
            poly_run = None
            
            for r in all_runs:
                if r.get('benchmarkName') != bench: continue
                
                v = r.get('variant')
                d = r.get('d')
                m = r.get('m')
                
                if v == 'kcfa' and d == 0:
                    if m == 0: base_run = r
                    if m == 1: poly_run = r
            
            if not base_run:
                print("  [ERROR] Missing 0-CFA Baseline!")
                continue
                
            if not poly_run:
                print("  [ERROR] Missing 1-kCFA Run (how did it get into df?)")
                continue
                
            # Compare Metrics
            b_m = base_run.get('storeMetrics', {})
            p_m = poly_run.get('storeMetrics', {})
            
            print(f"  Baseline File: {base_run.get('filePath')}")
            print(f"  Poly File:     {poly_run.get('filePath')}")
            
            if not b_m: print("  Baseline Metrics: NONE"); continue
            if not p_m: print("  Poly Metrics: NONE"); continue
            
            # Check Cont Singletons
            b_cnt = b_m.get('numContAddresses', 0)
            b_sng = b_m.get('cont0CFAStrSingletons', 0)
            
            p_cnt = p_m.get('numContAddresses', 0)
            p_sng = p_m.get('cont0CFAStrSingletons', 0)
            
            print(f"  0-CFA Cont: {b_sng}/{b_cnt} ({(b_sng/b_cnt*100 if b_cnt>0 else 100):.1f}%)")
            print(f"  1-kCFA Cont: {p_sng}/{p_cnt} ({(p_sng/p_cnt*100 if p_cnt>0 else 100):.1f}%)")
            
            # Check map improvement directly
            # We need to know if the MAPS are identical or just the counts
            # The JSON doesn't dump the full maps usually unless we check 'structToContStrSizes' key
            
            b_map = b_m.get('structToContStrSizes', {})
            p_map = p_m.get('structToContStrSizes', {})
            
            print(f"  Map Sizes: Base={len(b_map)}, Poly={len(p_map)}")
            
            # Calc diff
            if len(b_map) > 0:
                 # Check logic from calc_prod_stats
                 hits = 0
                 candidates = []
                 for k, b_val in b_map.items():
                     p_val = p_map.get(k, 0)
                     
                     # Check for improvement
                     improved = False
                     if b_val == -1: # Top
                         if p_val != -1: improved = True
                     elif p_val != -1 and p_val < b_val:
                         improved = True
                         
                     if improved:
                         hits += 1
                     
                     # Collect candidates for inspection (Imprecise in Base)
                     if b_val > 1 or b_val == -1:
                        candidates.append((k, b_val, p_val))

                 print(f"  Calculated Hits: {hits}")
                 
                 print("  Sample Imprecise Keys (Base -> Poly):")
                 for k, b, p in candidates[:5]:
                     print(f"    {k}: {b} -> {p}")

if __name__ == "__main__":
    inspect_zeros()
