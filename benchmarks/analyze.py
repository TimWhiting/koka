import json
import os
import numpy as np
import pandas as pd
from scipy.stats import gmean
import matplotlib.pyplot as plt
import seaborn as sns

def load_hierarchical_data(root_path, baselines_path):
    """Loads results from results/dim1/dim2/suite/benchmark hierarchy."""
    with open(baselines_path, 'r') as f:
        baselines = {b['programName']: b for b in json.load(f)}
    
    all_results = []
    for d1 in os.listdir(root_path):
        d1_p = os.path.join(root_path, d1)
        if not os.path.isdir(d1_p): continue
        for d2 in os.listdir(d1_p):
            d2_p = os.path.join(d1_p, d2)
            if not os.path.isdir(d2_p): continue
            run_id = f"{d1}-{d2}"
            for suite in os.listdir(d2_p):
                s_p = os.path.join(d2_p, suite)
                if not os.path.isdir(s_p): continue
                for bench in os.listdir(s_p):
                    b_p = os.path.join(s_p, bench)
                    if not os.path.isdir(b_p): continue
                    for f_name in [f for f in os.listdir(b_p) if f.endswith('.json')]:
                        with open(os.path.join(b_p, f_name), 'r') as f:
                            data = json.load(f)
                            data.update({'runID': run_id, 'dim1': d1, 'dim2': d2, 'suite': suite})
                            all_results.append(data)
    return all_results, baselines

def compute_metrics(run, baseline):
    """Computes relative and absolute precision metrics."""
    # Handle timeouts per Smaragdakis et al. (2011)
    if run.get('isTimeout') or run.get('storeMetrics') is None:
        return {
            "status": "T/O", 
            "time": np.mean(run['analysisTimes']), 
            "expansion": np.nan, 
            "top_ratio": 0.0,
            "prec_sem": 0.0,
            "prec_str": 0.0,
            "prod_v_str": 0.0,
            "prod_v_sem": 0.0,
            "prod_str": 0.0
        }

    m = run['storeMetrics']
    base_tot = baseline['bValueAddrs'] + baseline['bContAddrs']
    poly_tot = m['numValueAddresses'] + m['numContAddresses']
    
    # Ratios following Van Horn & Might (2010)
    expansion = poly_tot / base_tot if base_tot > 0 else 1.0
    prec_sem = m['valSemSingletons'] / m['numValueAddresses'] if m['numValueAddresses'] > 0 else 1.0
    prec_str = m['valStrSingletons'] / m['numValueAddresses'] if m['numValueAddresses'] > 0 else 1.0
    top_ratio = m['literalTopCount'] / m['numValueAddresses'] if m['numValueAddresses'] > 0 else 0.0

    # Productivity Helper (Smaragdakis et al., 2011)
    def calc_prod(poly_map, base_map):
        if not base_map: return 0.0
        hits = sum(1 for x_id, szs in poly_map.items() 
                  if any(s < base_map.get(x_id, float('inf')) and s != -1 for s in szs))
        return hits / len(base_map)

    return {
        "status": "OK",
        "time": np.mean(run['analysisTimes']),
        "expansion": expansion,
        "prec_sem": prec_sem,
        "prec_str": prec_str,
        "top_ratio": top_ratio,
        "prod_v_sem": calc_prod(m['exprToValSemSizes'], baseline['bExprToValSemSizes']),
        "prod_v_str": calc_prod(m['exprToValStrSizes'], baseline['bExprToValStrSizes']),
        "prod_str": calc_prod(m['structToStrRetSizes'], baseline['bStructToStrRetSizes'])
    }

def generate_icfp_tables(results, baselines):
    """Aggregates data and generates Markdown tables with time metrics."""
    rows = []
    for r in results:
        b = baselines.get(r['benchmarkName'])
        if b:
            m = compute_metrics(r, b)
            m.update({'runID': r['runID'], 'dim1': r['dim1'], 'dim2': r['dim2'], 'bench': r['benchmarkName']})
            rows.append(m)
    
    df = pd.DataFrame(rows)
    
    # 1. Global Summary Table (Geometric Mean for Expansion - Flemming et al., 2010)
    summary = df.groupby('runID').agg({
        'status': lambda x: (x == 'OK').sum(),
        'time': 'mean', # Arithmetic mean for time is common, but gmean is also acceptable
        'expansion': lambda x: gmean(x.dropna()) if not x.dropna().empty else np.nan,
        'prec_sem': 'mean',
        'prec_str': 'mean',
        'top_ratio': 'mean'
    }).rename(columns={'status': 'Solved', 'time': 'Time (s)'})
    
    # 2. Marginal Utility Tables (Kastrinis & Smaragdakis, 2013)
    prec_mu = df[df['status'] == 'OK'].pivot_table(index='dim1', columns='dim2', values='prec_sem', aggfunc='mean')
    time_mu = df[df['status'] == 'OK'].pivot_table(index='dim1', columns='dim2', values='time', aggfunc='mean')

    print("### Table 1: Global Efficiency, Time & Precision Summary")
    print(summary.to_markdown())
    print("\n### Table 2: Marginal Precision Utility (Semantic Precision)")
    print(prec_mu.to_markdown())
    print("\n### Table 3: Marginal Time Cost (Seconds)")
    print(time_mu.to_markdown())
    
    return df, prec_mu, time_mu

def plot_visualizations(df, prec_mu, time_mu):
    """Generates Pareto frontiers for both space and time complexity."""
    sns.set_theme(style="whitegrid")
    
    # Aggregating per runID for the plots
    plot_df = df[df['status'] == 'OK'].groupby('runID').agg({
        'expansion': lambda x: gmean(x.dropna()),
        'time': 'mean',
        'prec_sem': 'mean'
    }).reset_index()

    # A. Pareto Frontier (Expansion vs Precision)
    plt.figure(figsize=(10, 5))
    sns.scatterplot(data=plot_df, x='expansion', y='prec_sem', hue='runID', style='runID', s=150)
    plt.title("Pareto Frontier: State Space Expansion vs Precision")
    plt.xlabel("Expansion Factor (Geometric Mean)")
    plt.ylabel("Semantic Precision (Arithmetic Mean)")
    plt.savefig("pareto_expansion.png")
    
    # B. Pareto Frontier (Time vs Precision)
    plt.figure(figsize=(10, 5))
    sns.scatterplot(data=plot_df, x='time', y='prec_sem', hue='runID', style='runID', s=150)
    plt.title("Pareto Frontier: Execution Time vs Precision")
    plt.xlabel("Execution Time (Seconds)")
    plt.ylabel("Semantic Precision (Arithmetic Mean)")
    plt.savefig("pareto_time.png")
    
    # C. Marginal Precision Heatmap
    plt.figure(figsize=(8, 6))
    sns.heatmap(prec_mu, annot=True, cmap="YlGnBu", fmt=".2f")
    plt.title("Heatmap: Precision across Sensitivity Dimensions")
    plt.savefig("precision_heatmap.png")

    plt.show()

def process_histogram(hist):
    """Separates literals (top) from countable cardinalities."""
    clean_hist = {int(k): v for k, v in hist.items() if int(k) != -1}
    top_count = hist.get("-1", 0)
    return clean_hist, top_count