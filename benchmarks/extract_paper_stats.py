
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, prepare_tradeoff_data, get_benchmark_category

def shifted_geomean(series):
    """
    Calculates shifted geometric mean: exp(mean(log(1+x))) - 1.
    Handles 0.0 values naturally (log(1)=0).
    """
    vals = pd.to_numeric(series, errors='coerce') + 1.0
    vals = vals[vals > 0] # Filter invalid
    if len(vals) == 0: return 0.0
    return np.exp(np.mean(np.log(vals))) - 1.0

def get_stats():
    print("Loading results...")
    results = load_results_with_baselines()
    df = pd.DataFrame(results)
    
    # Filter for large benchmarks (States > 200)
    from plot_utils import get_large_benchmarks
    
    large_benchmarks = get_large_benchmarks(df, threshold=300)
    print(f"Large Benchmarks (States > 300): {len(large_benchmarks)}")
    
    # Update results to be the FULL LIST for now, we will filter in prepare_tradeoff_data or manually
    results_full = df.to_dict('records')
    
    # Filter for valid runs
    # We are comparing 1-kCFA vs 1,1-HMCFAR
    c_base = {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'}
    c_new = {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': '1,1-HMCFAR'}
    
    print("\n--- Benchmark Counts ---")
    # Get common benchmarks
    # We use prepare_tradeoff_data to get the intersection
    metrics_map = {'Cost': 'States', 'Precision': 'prec_cont_real'} 
    # using valid metrics to ensure filtered correctly
    
    df_tradeoff = prepare_tradeoff_data(results_full, c_base, c_new, metrics_map)
    
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

    print("\n--- 0-CFA Statistics by Category ---")
    c_0cfa = {'variant': 'kcfa', 'd': 0, 'm': 0, 'label': '0-CFA'}
    
    # We can use prepare_tradeoff_data to filter for just 0-CFA (comparing to itself or just extracting)
    # But simpler to just filter the dataframe directly since we loaded it
    df['Category'] = df['benchmarkName'].apply(get_benchmark_category)
    
    # Filter for 0-CFA
    df_0cfa = df[
        (df['variant'] == 'kcfa') & 
        (df['d'] == 0) & 
        (df['m'] == 0)
    ].copy()
    
    if df_0cfa.empty:
        # Fallback if 0-CFA is dmcfar 0,0 (unlikely for kcfa runs but possible)
        df_0cfa = df[
            (df['variant'] == 'dmcfar') & 
            (df['d'] == 0) & 
            (df['m'] == 0)
        ].copy()
        
    print(f"Found {len(df_0cfa)} 0-CFA runs.")
    
    # metrics are already in df: 'AbsContPrecision', 'AbsStructPrecision'
    # Group by category and mean
    stats = df_0cfa.groupby('Category')[['AbsContPrecision', 'AbsStructPrecision']].mean()
    print(stats)

    print("\n--- Shifted Geometric Mean of RIR (Strict) ---")
    # We need to extract the RIR values for 1-kCFA and 1,1-HMCFAR
    # We can use prepare_tradeoff_data to match them up
    
    # 1. Continuation RIR
    # Filter results for large benchmarks
    results_cont = [r for r in results_full if r['benchmarkName'] in large_benchmarks]
    
    metrics_map_rir_cont = {'RIR': 'prec_cont_rir_strict', 'Cost': 'States', 'BaseImprecise': 'baseline_cont_imprecise'}
    df_rir_cont = prepare_tradeoff_data(results_cont, c_base, c_new, metrics_map_rir_cont)
    
    geo_cont_base = shifted_geomean(df_rir_cont['RIR_Base'])
    geo_cont_new = shifted_geomean(df_rir_cont['RIR_New'])
    
    stats_cont = df_rir_cont['RIR_New'].astype(float).describe()
    
    count_gain_cont = (df_rir_cont['RIR_New'] > 0).sum()
    total_cont = len(df_rir_cont)
    max_gain_cont = df_rir_cont['RIR_New'].max()
    
    print(f"\n--- Continuation RIR Summary Table Data ---")
    
    # Calculate 0-CFA Precise Count using the consistent metric from DF
    # Note: 'BaseImprecise' maps to 'BaseImprecise_New' (from new config) and 'BaseImprecise_Base' (from old config)
    # They should be identical as they refer to the same baseline run.
    # We check if BaseImprecise_New == 0
    if 'BaseImprecise_New' in df_rir_cont.columns:
        count_precise_cont = (df_rir_cont['BaseImprecise_New'] == 0).sum()
    else: 
        count_precise_cont = 0
            
    # print(f"Benchmarks with 0-CFA Precise (No Gain Possible): {count_precise_cont} / {total_cont} ({count_precise_cont/total_cont*100:.1f}%)")
    print(f"Benchmarks with Gain: {count_gain_cont} / {total_cont} ({count_gain_cont/total_cont*100:.1f}%)")
    print(f"Max Gain: {max_gain_cont:.4f}")
    print(f"1-kCFA Geomean (Shifted): {geo_cont_base:.4f}")
    print(f"1,1-HMCFAR Geomean (Shifted): {geo_cont_new:.4f}")
    
    # Check if quartiles exist (might be absent if all NaNs, though unlikely here)
    if '25%' in stats_cont:
        print(f"Quartiles (25%, 50%, 75%): {stats_cont['25%']:.4f}, {stats_cont['50%']:.4f}, {stats_cont['75%']:.4f}")
    else:
        print("Quartiles not available in stats.")
    
    # 2. Value RIR
    # Filter results for large benchmarks
    results_val = [r for r in results_full if r['benchmarkName'] in large_benchmarks]
    
    metrics_map_rir_val = {'RIR': 'prec_val_rir_strict', 'Cost': 'States', 'BaseImprecise': 'baseline_val_imprecise'}
    df_rir_val = prepare_tradeoff_data(results_val, c_base, c_new, metrics_map_rir_val)
    
    geo_val_base = shifted_geomean(df_rir_val['RIR_Base'])
    geo_val_new = shifted_geomean(df_rir_val['RIR_New'])
    
    # Force numeric conversion for statistics
    rir_val_clean = pd.to_numeric(df_rir_val['RIR_New'], errors='coerce')
    stats_val = rir_val_clean.describe()
    
    count_gain_val = (rir_val_clean > 0).sum()
    total_val = len(rir_val_clean)
    max_gain_val = rir_val_clean.max()
    
    print(f"\n--- Value RIR Summary Table Data ---")
    
    # Calculate 0-CFA Precise Count
    if 'BaseImprecise_New' in df_rir_val.columns:
        count_precise_val = (df_rir_val['BaseImprecise_New'] == 0).sum()
    else:
        count_precise_val = 0
            
    print(f"Benchmarks with 0-CFA Precise (No Gain Possible): {count_precise_val} / {total_val} ({count_precise_val/total_val*100:.1f}%)")
            
    print(f"Benchmarks with 0-CFA Precise (No Gain Possible): {count_precise_val} / {total_val} ({count_precise_val/total_val*100:.1f}%)")
    print(f"Benchmarks with Gain: {count_gain_val} / {total_val} ({count_gain_val/total_val*100:.1f}%)")
    print(f"Max Gain: {max_gain_val:.4f}")
    print(f"1-kCFA Geomean (Shifted): {geo_val_base:.4f}")
    print(f"1,1-HMCFAR Geomean (Shifted): {geo_val_new:.4f}")
    print(f"Quartiles (25%, 50%, 75%): {stats_val['25%']:.4f}, {stats_val['50%']:.4f}, {stats_val['75%']:.4f}")

if __name__ == "__main__":
    get_stats()
