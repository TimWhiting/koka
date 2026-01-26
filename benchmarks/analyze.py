import json
import os
import numpy as np
import pandas as pd
from scipy.stats import gmean
import matplotlib.pyplot as plt
import seaborn as sns

def load_hierarchical_data(root_path, baselines_path):
    """
    Loads results from results/dim1/dim2/suite/benchmark hierarchy.
    Handles multiple entry points (tests) per benchmark.
    """
    with open(baselines_path, 'r') as f:
        baselines = {b['programName']: b for b in json.load(f)}
    
    all_results = []
    
    # Walk the directory structure
    for dim1 in os.listdir(root_path):
        d1_path = os.path.join(root_path, dim1)
        if not os.path.isdir(d1_path): continue
        
        for dim2 in os.listdir(d1_path):
            d2_path = os.path.join(d1_path, dim2)
            if not os.path.isdir(d2_path): continue
            
            run_id = f"{dim1}-{dim2}"
            
            for suite in os.listdir(d2_path):
                suite_path = os.path.join(d2_path, suite)
                if not os.path.isdir(suite_path): continue
                
                for benchmark in os.listdir(suite_path):
                    bench_path = os.path.join(suite_path, benchmark)
                    if not os.path.isdir(bench_path): continue
                    
                    # Gather all test files (entry points) for this benchmark
                    test_files = [f for f in os.listdir(bench_path) if f.endswith('.json')]
                    for t_file in test_files:
                        with open(os.path.join(bench_path, t_file), 'r') as f:
                            run_data = json.load(f)
                            run_data['runID'] = run_id
                            run_data['dim1'] = dim1
                            run_data['dim2'] = dim2
                            run_data['suite'] = suite
                            all_results.append(run_data)
                            
    return all_results, baselines

def compute_metrics(run, baseline):
    """Computes precision and efficiency relative to baseline."""
    # Penalty for timeouts (Smaragdakis et al., 2011)
    if run.get('isTimeout') or run.get('storeMetrics') is None:
        return {
            "status": 0, # Failure
            "time": np.mean(run['analysisTimes']),
            "expansion": np.nan,
            "precision_val": 0.0,
            "prod_v": 0.0,
            "prod_str": 0.0
        }

    m = run['storeMetrics']
    base_total = baseline['bValueAddrs'] + baseline['bContAddrs']
    poly_total = m['numValueAddresses'] + m['numContAddresses']
    
    # Efficiency: Expansion Factor (Van Horn & Might, 2010)
    expansion = poly_total / base_total if base_total > 0 else 1.0
    
    # Precision: Singleton Ratios
    prec_v = m['valSingletons'] / m['numValueAddresses'] if m['numValueAddresses'] > 0 else 1.0

    # Productivity Calculation (Smaragdakis et al., 2011)
    def calc_prod(poly_map, base_map):
        if not base_map: return 1.0
        hits = sum(1 for x_id, sizes in poly_map.items() 
                  if any(s < base_map.get(x_id, float('inf')) for s in sizes))
        return hits / len(base_map)

    return {
        "status": 1, # Success
        "time": np.mean(run['analysisTimes']),
        "expansion": expansion,
        "precision_val": prec_v,
        "prod_v": calc_prod(m['exprToValSizes'], baseline['bValueFlow']),
        "prod_str": calc_prod(m['transToStrRetSizes'], baseline['bStrReturnFlow'])
    }

def generate_report(results, baselines):
    """Aggregates data and generates Markdown tables."""
    rows = []
    for run in results:
        b = baselines.get(run['benchmarkName'])
        if b:
            metrics = compute_metrics(run, b)
            metrics.update({
                'runID': run['runID'],
                'dim1': run['dim1'],
                'dim2': run['dim2'],
                'benchmark': run['benchmarkName']
            })
            rows.append(metrics)
    
    df = pd.DataFrame(rows)
    
    # 1. Main Aggregate Table (Geometric Mean for Expansion - Flemming et al., 2010)
    summary = df.groupby('runID').agg({
        'status': 'sum',
        'time': 'mean',
        'expansion': lambda x: gmean(x.dropna()) if not x.dropna().empty else np.nan,
        'precision_val': 'mean',
        'prod_str': 'mean'
    }).rename(columns={'status': 'Solved'})

    print("### Global Summary Statistics")
    print(summary.to_markdown())
    
    # 2. Marginal Utility Table (Kastrinis & Smaragdakis, 2013)
    # Rows = dim1, Cols = dim2, Values = Global Precision
    mu_table = df.pivot_table(index='dim1', columns='dim2', values='precision_val', aggfunc='mean')
    print("\n### Marginal Utility: Global Value Precision")
    print(mu_table.to_markdown())
    
    return df, mu_table

def plot_visualizations(df, mu_table):
    """Generates standard CFA evaluation plots."""
    sns.set_theme(style="whitegrid")
    
    # A. Pareto Frontier (Cost vs Quality)
    plt.figure(figsize=(10, 6))
    sns.scatterplot(data=df, x='expansion', y='precision_val', hue='runID', style='runID', s=100)
    plt.title("Pareto Frontier: Expansion vs Value Precision")
    plt.xlabel("Expansion Factor (Geometric Mean)")
    plt.ylabel("Value Precision (Arithmetic Mean)")
    plt.savefig("pareto_frontier.png")
    
    # B. Marginal Utility Heatmap
    plt.figure(figsize=(8, 6))
    sns.heatmap(mu_table, annot=True, cmap="YlGnBu", fmt=".2f")
    plt.title("Marginal Utility of Multi-Dimensional Sensitivity")
    plt.savefig("utility_heatmap.png")
    
    plt.show()

# Execution Example:
# results, baselines = load_hierarchical_data('results/', 'baselines.json')
# df, mu = generate_report(results, baselines)
# plot_visualizations(df, mu)