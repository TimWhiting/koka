
import pandas as pd
from plot_utils import load_results_with_baselines, prepare_tradeoff_data

# Configs
# Configs
c_base = {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'}
c_new = {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': '1,1-HMCFAR'}

# Load
print("Loading results...")
df_list = load_results_with_baselines("benchmarks/results-cached")
print(f"Loaded {len(df_list)} results.")
if len(df_list) > 0:
    print("Example result keys:", df_list[0].keys())
    
df_final = pd.DataFrame(df_list)
print(f"DataFrame shape: {df_final.shape}")
if not df_final.empty:
    print("Columns:", df_final.columns.tolist())
    print("\nUnique Variants:", df_final['variant'].unique())
    print("Unique d:", df_final['d'].unique())
    print("Unique m:", df_final['m'].unique())
    
    # Check Base Config existence
    base_rows = df_final[
        (df_final['variant'] == 'kcfa') & 
        (df_final['d'] == 0) & 
        (df_final['m'] == 1)
    ]
    print(f"\nRows matching Base (kcfa, 0, 1) (Ints): {len(base_rows)}")
    
    base_rows_str = df_final[
        (df_final['variant'] == 'kcfa') & 
        (df_final['d'].astype(str) == '0') & 
        (df_final['m'].astype(str) == '1')
    ]
    print(f"Rows matching Base (kcfa, 0, 1) (Strings): {len(base_rows_str)}")

else:
    print("DataFrame is empty!")
    exit(1)

# Check Value Real Precision
metric_col = 'prec_val_real'
metrics_map = {'Cost': 'Time', 'Precision': metric_col}

try:
    df_tradeoff = prepare_tradeoff_data(df_final, c_base, c_new, metrics_map)
except Exception as e:
    print(f"Error preparing data: {e}")
    exit(1)

# Check for regressions in Real Precision (Val)
if 'Precision_New' not in df_tradeoff.columns:
    print("Column 'Precision_New' not found. columns:", df_tradeoff.columns.tolist())
    exit(1)

df_tradeoff['Prec_Gain_Real'] = df_tradeoff['Precision_New'] - df_tradeoff['Precision_Base']

print(f"Total Benchmarks: {len(df_tradeoff)}")

# Filter regressions (gain < -0.0001 to avoid float noise)
regressions = df_tradeoff[df_tradeoff['Prec_Gain_Real'] < -0.0001].copy()
print(f"Regressions (Real Prec < 0): {len(regressions)}")

if not regressions.empty:
    print("\nTop Regressions (Real Prec):")
    print(regressions[['benchmarkName', 'Precision_Base', 'Precision_New', 'Prec_Gain_Real']].sort_values('Prec_Gain_Real').head(10))
    
    # Detail for worst
    worst = regressions.sort_values('Prec_Gain_Real').iloc[0]
    bench_name = worst['benchmarkName']
    print(f"\nDetails for worst regression: {bench_name}")
    
    # Find rows in original df to get components
    cols = ['variant', 'd', 'm', 'prec_val_real', 'prec_struct_real', 'literal0CFATopCount', 'numLitAddresses']
    print(df_final[df_final['benchmarkName'] == bench_name][cols])
else:
    print("No regressions found.")
