
import pandas as pd
from plot_utils import load_results_with_baselines, get_complex_benchmarks

def debug_anomaly():
    print("Loading results...")
    results = load_results_with_baselines("benchmarks/results-cached")
    df = pd.DataFrame(results)
    
    complex_benchs = get_complex_benchmarks(df)
    df = df[df['benchmarkName'].isin(complex_benchs)]
    
    # Filter for DMCFAR
    df = df[df['variant'] == 'dmcfar']
    
    # Fix h=1 (d=1)
    df = df[df['d'] == 1]
    
    # Compare m=1 vs m=2
    m1 = df[df['m'] == 1][['benchmarkName', 'prec_val_total', 'literalHits', 'numLitAddresses', 'prec_struct']]
    m2 = df[df['m'] == 2][['benchmarkName', 'prec_val_total', 'literalHits', 'numLitAddresses', 'prec_struct']]
    
    merged = pd.merge(m1, m2, on='benchmarkName', suffixes=('_m1', '_m2'))
    
    merged['diff'] = merged['prec_val_total_m2'] - merged['prec_val_total_m1']
    
    # Look for drops
    drops = merged[merged['diff'] < -0.0001]
    
    print(f"Found {len(drops)} benchmarks where m=2 < m=1 for Value Productivity (h=1).")
    
    if len(drops) > 0:
        print("\nTop 10 drops:")
        print(drops[['benchmarkName', 'prec_val_total_m1', 'prec_val_total_m2', 'diff']].head(10))
        
        # Detail on first one
        row = drops.iloc[0]
        print(f"\nDetailed check for {row['benchmarkName']}:")
        print(f"m=1: ValProd={row['prec_val_total_m1']}, LitHits={row['literalHits_m1']}, StructPrec={row['prec_struct_m1']}")
        print(f"m=2: ValProd={row['prec_val_total_m2']}, LitHits={row['literalHits_m2']}, StructPrec={row['prec_struct_m2']}")

if __name__ == "__main__":
    debug_anomaly()
