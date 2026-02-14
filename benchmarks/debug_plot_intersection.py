
import pandas as pd
from plot_utils import load_results_with_baselines, prepare_tradeoff_data

print("Loading results...")
results = load_results_with_baselines("benchmarks/results-cached")

c_base = {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'}
c_new = {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': '1,1-HMCFAR'}

# Tradeoff Data (Space)
metrics_space = {'Precision': 'prec_struct', 'Cost': 'States'}
df_space = prepare_tradeoff_data(results, c_base, c_new, metrics_space)
bench_space = set(df_space['benchmarkName'])
print(f"Space Benchmarks: {len(bench_space)}")

# Time Data
metrics_time = {'Precision': 'prec_struct', 'Cost': 'Time'}
df_time = prepare_tradeoff_data(results, c_base, c_new, metrics_time)
bench_time = set(df_time['benchmarkName'])
print(f"Time Benchmarks: {len(bench_time)}")

# Debug Colors
print("\n--- Color Logic check ---")
def get_color_category(row):
    prec_gain = row['Precision_New'] - row['Precision_Base']
    cost_ratio = row['Cost_New'] / row['Cost_Base']
    
    if prec_gain < -0.01: return 'Red'
    elif prec_gain > 0.01:
        if cost_ratio < 1.0: return 'Green'
        else: return 'Blue'
    else:
        if cost_ratio < 1.0: return 'Gray-Green' # Efficient
        elif cost_ratio > 1.0: return 'Gray'
        return 'Gray'

df_space['Color'] = df_space.apply(get_color_category, axis=1)
df_time['Color'] = df_time.apply(get_color_category, axis=1)

print("Space Plot Colors:")
print(df_space['Color'].value_counts())

print("\nTime Plot Colors:")
print(df_time['Color'].value_counts())

# Check if Green+Blue sum is same
space_imp = df_space[df_space['Color'].isin(['Green', 'Blue'])].shape[0]
time_imp = df_time[df_time['Color'].isin(['Green', 'Blue'])].shape[0]

print(f"\nTotal Improved Precision (Green+Blue):")
print(f"Space: {space_imp}")
print(f"Time:  {time_imp}")

if space_imp != time_imp:
    print("MISMATCH IN PRECISION IMPROVEMENT COUNT!")
    # Find mismatch
    s_set = set(df_space[df_space['Color'].isin(['Green', 'Blue'])]['benchmarkName'])
    t_set = set(df_time[df_time['Color'].isin(['Green', 'Blue'])]['benchmarkName'])
    
    print(f"In Space but not Time: {s_set - t_set}")
    print(f"In Time but not Space: {t_set - s_set}")
else:
    print("Matches! The mix might differ, but total improved benchmarks is consistent.")
