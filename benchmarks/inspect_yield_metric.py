
import pandas as pd
from plot_utils import load_results_with_baselines, calc_relative_prec_stats

def inspect():
    print("Loading results...")
    results = load_results_with_baselines("benchmarks/results-cached")
    df = pd.DataFrame(results)
    
    # Filter for coop-communication/yield
    # Check 0CFA (kcfa d=0 m=0)
    # Note: variant might be 'dmcfar' for 0CFA if using that config, or 'kcfa'. 
    # Usually we use 'kcfa' variant for 0CFA in these tables? Or 'dmcfar' H(0,0)?
    # The table says '0CFA'.
    
    subset = df[df['benchmarkName'].str.contains("coop-communication/yield")]
    
    # Find the 0CFA row
    # It seems we treat 'dmcfar' d=0 m=0 as 0CFA in the table generator?
    # Or 'kcfa' m=0?
    
    # Let's print all variants for this bench
    print(f"Found {len(subset)} runs for yield")
    
    for _, row in subset.iterrows():
        v = row['variant']
        d = row.get('d')
        m = row.get('m')
        
        is_0cfa = False
        if v == 'kcfa' and m == 0: is_0cfa = True
        if v == 'dmcfar' and d == 0 and m == 0: is_0cfa = True
        
        if is_0cfa:
            print(f"\n--- 0CFA Candidate: {v} d={d} m={m} ---")
            print(f"RIR Strict: {row.get('prec_cont_rir_strict')}")
            print(f"RIR Denom: {row.get('baseline_cont_imprecise')}")
            print(f"RIR Hits: {row.get('prec_cont_rir_strict_hits')}")
            
            # Re-calculate manually to check logic if we can access the maps
            # The maps might be in 'structToContStrSizes'
            # But load_results might have processed them already.
            # If we want to debug the FUNCTION, we need the raw maps.
            # But here we just check what's in the DF.
            
            # Check REAL precision too
            print(f"Real Precision: {row.get('prec_cont_real')}")

if __name__ == "__main__":
    inspect()
