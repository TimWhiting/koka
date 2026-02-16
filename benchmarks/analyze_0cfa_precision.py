
import os
import json
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, compute_metrics, get_complex_benchmarks, get_benchmark_category

def analyze_0cfa():
    print("Loading 0-CFA results...")
    
    # We need raw loading to ensure we get everything, but load_results_with_baselines helps structure it
    # Let's use the standard loader but map it back to specific metrics
    
    results = load_results_with_baselines("benchmarks/results-cached")
    df = pd.DataFrame(results)
    
    # Filter for 0-CFA (kcfa d=0 m=0)
    baseline = df[(df['variant'] == 'kcfa') & (df['d'] == 0) & (df['m'] == 0)].copy()
    
    if baseline.empty:
        print("No 0-CFA baselines found!")
        return

    print(f"\nTotal 0-CFA Benchmarks Found: {len(baseline)}")
    
    # Debug: Check one row keys
    if not baseline.empty:
        print("\n[DEBUG] Sample Row Keys:")
        print(baseline.iloc[0].index.tolist())
        print(f"[DEBUG] Sample storeMetrics type: {type(baseline.iloc[0].get('storeMetrics'))}")
        # print(baseline.iloc[0].get('storeMetrics')) # Too large to print

    
    # Metrics to check
    # AbsContPrecision is already calculated in compute_metrics
    # AbsStructPrecision is also there
    
    # Ensure Value Precision includes Literals for this check (metrics dict usually separates them)
    # Re-calculate absolute value precision including literals to be sure
    
    def calc_abs_val_full(row):
        m = row.get('storeMetrics', {})
        if not m: return 1.0
        
        num_struct = m.get('numStructAddresses', 0)
        val_single = m.get('val0CFAStrSingletons', 0)
        
        num_lit = m.get('numLitAddresses', 0)
        lit_dead = m.get('numLitAddresses', 0) # Top count usually implies imprecise, but 'Singletons' logic for literals?
        # In 0-CFA, literal is precise if it's not Top.
        # But wait, compute_metrics doesn't put AbsValuePrec including literals in the top level dict
        
        # Let's rely on what compute_metrics gives for "AbsStructPrecision" as a proxy for now, 
        # or calculate it manually if needed.
        return row.get('AbsStructPrecision', 1.0)

    baseline['AbsValuePrecision'] = baseline.apply(calc_abs_val_full, axis=1)
    
    # Stats
    print("\n--- Value Precision (Store Only) (0-CFA) ---")
    # Note: This metric (AbsStructPrecision) only measures Store Address precision.
    # It appears to be 1.0 (perfect) for all 0-CFA benchmarks, implying
    # any "Value Precision" improvement seen in plots comes from Literals.
    print(baseline['AbsValuePrecision'].describe(percentiles=[0.05, 0.1, 0.25, 0.5, 0.75, 0.9, 0.95]))

    
    # Analyze Literals specifically
    # Metric: Use pre-calculated map stats from plot_utils
    # literalMapSize = Total Literals in Map
    # literalPreciseCount = Number of True values (Precise)
    # Top = MapSize - PreciseCount
    
    
    # Analyze Literals specifically
    # Metric: Use pre-calculated map stats from plot_utils
    # literalMapSize = Total Literals in Map
    # literalPreciseCount = Number of True values (Precise)
    # Top = MapSize - PreciseCount
    
    baseline['NumLits'] = baseline['literalMapSize']
    baseline['NumTopLits'] = baseline['literalMapSize'] - baseline['literalPreciseCount']
    
    # Calculate Literal Precision (0.0 - 1.0)
    def calc_lit_prec(row):
        total = row.get('literalMapSize', 0)
        precise = row.get('literalPreciseCount', 0)
        if pd.isna(total) or total == 0: return 1.0
        return precise / total

    baseline['Lit_Prec'] = baseline.apply(calc_lit_prec, axis=1)

    
    # Filter for complex only for this check
    complex_df = baseline[baseline['AbsContPrecision'] < 0.99]
    
    print("\n--- Literal Precision in Complex Benchmarks (0-CFA) ---")
    print(f"Total Literals: {complex_df['NumLits'].sum()}")
    print(f"Total Top Literals: {complex_df['NumTopLits'].sum()}")
    print(f"Benchmarks with Top Literals: {len(complex_df[complex_df['NumTopLits'] > 0])}")
    
    if len(complex_df[complex_df['NumTopLits'] > 0]) > 0:
        print("\nSample Benchmarks with Imprecise Literals (0-CFA):")
        print(complex_df[complex_df['NumTopLits'] > 0][['benchmarkName', 'NumLits', 'NumTopLits', 'Lit_Prec']].sort_values('NumTopLits', ascending=False).head(10))

    
    # Categorization Analysis
    print("\n--- Categorized 0-CFA Precision (All Benchmarks) ---")
    
    def get_category_refined(name):
        cat = get_benchmark_category(name)
        if cat == 'Handlers': return 'Koka-Samples'
        return cat

    baseline['Category'] = baseline['benchmarkName'].apply(get_category_refined)
    
    # Group by Category and calc mean precision
    cat_summary = baseline.groupby('Category')[['AbsContPrecision', 'Lit_Prec', 'NumTopLits']].mean()
    print(cat_summary)
    
    # Full Results Export (for Appendix)
    print("\n--- Generating Appendix Data (All Benchmarks) ---")
    
    # Select columns for Appendix Table A1 (0-CFA Focused)
    # Benchmark Name, Category, Size, Cont Prec, Lit Prec
    
    appendix_df = baseline[['benchmarkName', 'Category', 'States', 'AbsContPrecision', 'Lit_Prec', 'NumTopLits']]
    
    # Shorten Names for CSV
    def shorten_name(row):
        name = row['benchmarkName']
        prefixes = [
            'analysis/benchmarks/koka-gen/', 
            'analysis/benchmarks/handlers/',
            'analysis/benchmarks/rosetta/rosetta/', 
            'analysis/benchmarks/rosetta/',
            'analysis/benchmarks/suite/',
            'analysis/benchmarks/'
        ]
        for p in prefixes:
            if name.startswith(p):
                return name[len(p):]
        return name

    appendix_df['Benchmark'] = appendix_df.apply(shorten_name, axis=1)
    
    # Reorder cols
    appendix_df = appendix_df[['Category', 'Benchmark', 'States', 'AbsContPrecision', 'Lit_Prec']]
    
    # Sort
    cat_order = {'Koka-Gen': 0, 'Rosetta': 1, 'Koka-Samples': 2, 'Micro-Suite': 3, 'Other': 4}
    appendix_df['Cat_Rank'] = appendix_df['Category'].map(cat_order)
    appendix_df = appendix_df.sort_values(by=['Cat_Rank', 'States']) # States ascending
    appendix_df = appendix_df.drop(columns=['Cat_Rank'])
    
    # Round
    appendix_df['AbsContPrecision'] = appendix_df['AbsContPrecision'].round(2)
    appendix_df['Lit_Prec'] = appendix_df['Lit_Prec'].round(2)

    # Save to CSV
    output_path = "benchmarks/appendix_data_0cfa.csv"
    appendix_df.to_csv(output_path, index=False)
    print(f"Saved 0-CFA summary to {output_path}")

    # Check for "Flatness": how many are 1.0?
    perfect_cont = len(baseline[baseline['AbsContPrecision'] >= 0.99])
    total = len(baseline)
    print(f"\nPerfect Cont Precision: {perfect_cont}/{total} ({perfect_cont/total:.1%})")
    
    perfect_val = len(baseline[baseline['NumTopLits'] == 0])
    print(f"Perfect Literal Precision: {perfect_val}/{total} ({perfect_val/total:.1%})")

    # Correlation
    print("\nCorrelation between Cont and Value Precision:")
    print(baseline[['AbsContPrecision', 'AbsValuePrecision']].corr())

if __name__ == "__main__":
    analyze_0cfa()
