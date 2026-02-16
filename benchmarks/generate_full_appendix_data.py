
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, get_benchmark_category

def generate_full_data():
    print("Loading all results...")
    results = load_results_with_baselines("benchmarks/results-cached")
    df = pd.DataFrame(results)
    
    # Define configurations to compare
    config_kcfa = {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'}
    config_hmcfar = {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': '1,1-HMCFAR'}
    
    # Filter DF for these configs
    df_compare = df[
        ((df['variant'] == config_kcfa['variant']) & (df['d'] == config_kcfa['d']) & (df['m'] == config_kcfa['m'])) |
        ((df['variant'] == config_hmcfar['variant']) & (df['d'] == config_hmcfar['d']) & (df['m'] == config_hmcfar['m']))
    ].copy()
    
    # Pivot to get side-by-side
    # Metrics: prec_cont_abs_impr (Cont Improvement), prec_val_abs_impr (Val Impr), States (Cost), Time (Cost)
    
    pivot_cols = ['benchmarkName', 'AbsContPrecision'] # Keep 0-CFA baseline prec
    valid_cols = ['benchmarkName', 'variant', 'States', 'Time', 'prec_cont_abs_impr', 'prec_val_abs_impr', 'AbsContPrecision']
    
    # We need to preserve 0-CFA precision attached to the benchmark
    # Let's get 0-CFA stats first
    baseline_df = df[(df['variant'] == 'kcfa') & (df['d'] == 0) & (df['m'] == 0)][['benchmarkName', 'AbsContPrecision', 'States']]
    baseline_df = baseline_df.rename(columns={'States': 'States_0CFA', 'AbsContPrecision': 'Prec_0CFA'})
    
    # Prepare comparison
    df_kcfa = df_compare[df_compare['variant'] == 'kcfa'][['benchmarkName', 'prec_cont_abs_impr', 'prec_val_abs_impr', 'States', 'Time']]
    df_kcfa = df_kcfa.rename(columns={
        'prec_cont_abs_impr': 'Cont_Imp_kCFA', 
        'prec_val_abs_impr': 'Val_Imp_kCFA',
        'States': 'States_kCFA',
        'Time': 'Time_kCFA'
    })
    
    df_hmcfa = df_compare[df_compare['variant'] == 'dmcfar'][['benchmarkName', 'prec_cont_abs_impr', 'prec_val_abs_impr', 'States', 'Time']]
    df_hmcfa = df_hmcfa.rename(columns={
        'prec_cont_abs_impr': 'Cont_Imp_HMCFAR', 
        'prec_val_abs_impr': 'Val_Imp_HMCFAR',
        'States': 'States_HMCFAR',
        'Time': 'Time_HMCFAR'
    })
    
    # Merge
    merged = pd.merge(baseline_df, df_kcfa, on='benchmarkName', how='left')
    merged = pd.merge(merged, df_hmcfa, on='benchmarkName', how='left')
    
    
    # NEW: Add Literal Precision Baseline (Approximate)
    # Use computed metrics from `baseline_df` or `df` directly, as load_results_with_baselines keeps them.
    # We need to look up `literalPreciseCount` and `literalMapSize` from the 0-CFA rows in `df`.
    
    lit_df = df[(df['variant'] == 'kcfa') & (df['d'] == 0) & (df['m'] == 0)][['benchmarkName', 'literalMapSize', 'literalPreciseCount']]
    
    merged = pd.merge(merged, lit_df, on='benchmarkName', how='left')
    
    def get_lit_prec_safe(row):
        total = row.get('literalMapSize', 0)
        precise = row.get('literalPreciseCount', 0)
        if pd.isna(total) or total == 0: return 1.0
        return precise / total

    merged['Lit_Prec_0CFA'] = merged.apply(get_lit_prec_safe, axis=1)

    # Update Category Naming
    def get_category_refined(name):
        cat = get_benchmark_category(name)
        if cat == 'Handlers': return 'Koka-Samples'
        return cat
        
    merged['Category'] = merged['benchmarkName'].apply(get_category_refined)
        
    # Shorten Names
    def shorten_name(row):
        name = row['benchmarkName']
        # Remove common prefixes
        prefixes = [
            'analysis/benchmarks/koka-gen/', 
            'analysis/benchmarks/handlers/',
            'analysis/benchmarks/rosetta/rosetta/', # Double rosetta in path?
            'analysis/benchmarks/rosetta/',
            'analysis/benchmarks/suite/',
            'analysis/benchmarks/'
        ]
        for p in prefixes:
            if name.startswith(p):
                name = name[len(p):]
                break
        
        # Remove Rosetta subdirs
        subdirs = ['m/', 'j/', 'nums0/', 'text/'] # Added text/ just in case, nums0 known
        for s in subdirs:
            if name.startswith(s):
                name = name[len(s):]
                break
        return name

    merged['Benchmark'] = merged.apply(shorten_name, axis=1)

    # Fill N/A with 0 for improvements if missing (though they should be present if run exists)
    merged = merged.dropna(subset=['Cont_Imp_kCFA', 'Cont_Imp_HMCFAR'])
    
    # Cost Factors
    merged['Cost_States'] = merged['States_HMCFAR'] / merged['States_kCFA']
    merged['Cost_Time'] = merged['Time_HMCFAR'] / merged['Time_kCFA']
    
    # Select Final Columns
    final_cols = [
        'Category', 'Benchmark', 'States_0CFA', 
        'Prec_0CFA', 'Lit_Prec_0CFA',
        'Cont_Imp_kCFA', 'Cont_Imp_HMCFAR', 
        'Cost_States'
    ]
    
    final_df = merged[final_cols].copy()
    
    # Sort: Category (Custom Order), then States
    # Order: Koka-Gen, Rosetta, Koka-Samples, Micro-Suite
    cat_order = {'Koka-Gen': 0, 'Rosetta': 1, 'Koka-Samples': 2, 'Micro-Suite': 3, 'Other': 4}
    final_df['Cat_Rank'] = final_df['Category'].map(cat_order)
    
    final_df = final_df.sort_values(by=['Cat_Rank', 'States_0CFA'])
    
    # Insert Averages
    # We will build a new list of dicts
    output_rows = []
    
    # Helper to round
    def r2(x): return round(x, 2)
    
    for cat_name, cat_val in sorted(cat_order.items(), key=lambda x: x[1]):
        cat_group = final_df[final_df['Category'] == cat_name].copy()
        if cat_group.empty: continue
        
        # Content Rows
        for _, row in cat_group.iterrows():
            output_rows.append(row.to_dict())
            
        # Average Row
        avg_row = {
            'Category': cat_name,
            'Benchmark': 'Average',
            'States_0CFA': cat_group['States_0CFA'].mean(),
            'Prec_0CFA': cat_group['Prec_0CFA'].mean(),
            'Lit_Prec_0CFA': cat_group['Lit_Prec_0CFA'].mean(),
            'Cont_Imp_kCFA': cat_group['Cont_Imp_kCFA'].mean(),
            'Cont_Imp_HMCFAR': cat_group['Cont_Imp_HMCFAR'].mean(),
            'Cost_States': cat_group['Cost_States'].mean(),
            'Cat_Rank': cat_val
        }
        output_rows.append(avg_row)
        
    final_df_with_avg = pd.DataFrame(output_rows)
    
    # Drop Rank
    final_df_with_avg = final_df_with_avg.drop(columns=['Cat_Rank'])
    
    # Rounding
    cols_to_round = ['Prec_0CFA', 'Lit_Prec_0CFA', 'Cont_Imp_kCFA', 'Cont_Imp_HMCFAR', 'Cost_States']
    final_df_with_avg[cols_to_round] = final_df_with_avg[cols_to_round].round(2)
    final_df_with_avg['States_0CFA'] = final_df_with_avg['States_0CFA'].round(0).astype(int)

    # Renaming for Table Headers
    final_df_with_avg = final_df_with_avg.rename(columns={
        'States_0CFA': 'Size',
        'Prec_0CFA': 'Cont_Prec',
        'Lit_Prec_0CFA': 'Lit_Prec',
        'Cont_Imp_kCFA': 'kCFA_Imp',
        'Cont_Imp_HMCFAR': 'HMCFAR_Imp',
        'Cost_States': 'Cost_Factor'
    })

    # Save Full Table
    final_df_with_avg.to_csv("benchmarks/appendix_full_comparison.csv", index=False)
    print("Saved clean comparison to benchmarks/appendix_full_comparison.csv")
    
    # Group by Category Summary (Simple check)
    print("\n--- Summary Check ---")
    print(final_df_with_avg[final_df_with_avg['Benchmark'] == 'Average'])

if __name__ == "__main__":
    generate_full_data()
