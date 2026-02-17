
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, prepare_tradeoff_data, get_benchmark_category

def get_stats():
    print("Loading results...")
    results = load_results_with_baselines()
    df = pd.DataFrame(results)
    
    # Filter for valid runs
    # We are comparing 1-kCFA vs 1,1-HMCFAR
    c_base = {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'}
    c_new = {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': '1,1-HMCFAR'}
    
    print("\n--- Benchmark Counts ---")
    # Get common benchmarks
    # We use prepare_tradeoff_data to get the intersection
    metrics_map = {'Cost': 'States', 'Precision': 'prec_cont_real'} 
    # using valid metrics to ensure filtered correctly
    
    df_tradeoff = prepare_tradeoff_data(results, c_base, c_new, metrics_map)
    
    total = len(df_tradeoff)
    print(f"Total Common Benchmarks: {total}")
    
    # Categorize
    df_tradeoff['Category'] = df_tradeoff['benchmarkName'].apply(get_benchmark_category)
    print(df_tradeoff['Category'].value_counts())
    
    print("\n--- Cost Factor (States) ---")
    # Cost_Ratio is already in df_tradeoff (New / Base)
    median_cost = df_tradeoff['Cost_Ratio'].median()
    print(f"Median Cost Factor (1,1-HMCFAR / 1-kCFA): {median_cost:.2f}x")
    
    # By Category
    print("Median Cost Factor by Category:")
    print(df_tradeoff.groupby('Category')['Cost_Ratio'].median())
    
    print("\n--- Precision (Continuation) ---")
    # Calculate averages/medians for precision
    print(f"Mean Cont Prec (1-kCFA): {df_tradeoff['Precision_Base'].mean():.3f}")
    print(f"Mean Cont Prec (1,1-HMCFAR): {df_tradeoff['Precision_New'].mean():.3f}")
    
    # Absolute Precision Check
    # We need to pull AbsContPrecision from the original results for these benchmarks
    # Map back to find AbsContPrecision for the specific variants
    # df_tradeoff has columns like 'AbsContPrecision_1-kCFA', 'AbsContPrecision_1,1-HMCFAR' if we included them in metrics_map
    
    # Let's re-run prepare_tradeoff with AbsContPrecision
    # We map 'AbsContPrecision' to 'Precision' so prepare_tradeoff_data is happy
    metrics_map_abs = {'Precision': 'AbsContPrecision', 'Cost': 'States'}
    df_abs = prepare_tradeoff_data(results, c_base, c_new, metrics_map_abs)
    
    print(f"\nMean Absolute Cont Prec (1-kCFA): {df_abs['Precision_Base'].mean():.3f}")
    print(f"Mean Absolute Cont Prec (1,1-HMCFAR): {df_abs['Precision_New'].mean():.3f}")
    
    print(f"Median Absolute Cont Prec (1-kCFA): {df_abs['Precision_Base'].median():.3f}")
    print(f"Median Absolute Cont Prec (1,1-HMCFAR): {df_abs['Precision_New'].median():.3f}")
    
    # Koka-Gen specific
    df_abs['Category'] = df_abs['benchmarkName'].apply(get_benchmark_category)
    koka_gen_abs = df_abs[df_abs['Category'] == 'Koka-Gen']
    print(f"\nKoka-Gen Mean Abs Cont Prec (1-kCFA): {koka_gen_abs['Precision_Base'].mean():.3f}")
    print(f"Koka-Gen Mean Abs Cont Prec (1,1-HMCFAR): {koka_gen_abs['Precision_New'].mean():.3f}")

if __name__ == "__main__":
    get_stats()
