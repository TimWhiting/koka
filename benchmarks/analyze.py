import json
import os
import numpy as np
import pandas as pd
from scipy.stats import gmean
import matplotlib.pyplot as plt
import seaborn as sns

def load_hierarchical_data(root_path):
    """Loads results from results/dim1/dim2/suite/benchmark hierarchy."""
    all_results = []
    for d in os.listdir(root_path):
        d_p = os.path.join(root_path, d)
        if not os.path.isdir(d_p): continue
        for m in os.listdir(d_p):
            m_p = os.path.join(d_p, m)
            if not os.path.isdir(m_p): continue
            run_id = f"{d}-{m}"
            for root, _, files in os.walk(m_p):
                for f_name in files:
                    if f_name.endswith('.json'):
                        with open(os.path.join(root, f_name), 'r') as f:
                            try:
                                data = json.load(f)
                                data.update({'runID': run_id, 'd': d, 'm': m})
                                all_results.append(data)
                            except json.JSONDecodeError:
                                print(f"Warning: Failed to decode {f_name}")
    return all_results

def compute_metrics(run, baseline):
    """Computes relative and absolute precision metrics using explicit store sizes."""
    analysis_times = run.get('analysisTimes', [])
    avg_time = np.mean(analysis_times) if analysis_times else 0.0

    if run.get('isTimeout') or run.get('storeMetrics') is None:
        return {
            "status": "T/O", 
            "time": avg_time, 
            "expansion": np.nan, 
            "prec_struct": 0.0,
            "prec_lit": 0.0,
            "prod_v_sem": 0.0,
            "prod_v_str": 0.0,
            "prod_k_str": 0.0,
            "prod_sem": 0.0,
            "prod_str": 0.0
        }

    m = run['storeMetrics']
    
    # Expansion Factor (Van Horn & Might, 2010)
    # Uses explicit store addresses to handle overlaps between partitions
    base_tot = baseline['numStoreAddresses']
    poly_tot = m['numStoreAddresses']
    expansion = poly_tot / base_tot if base_tot > 0 else 1.0
    
    # Relative Structural Precision (Improvement over baseline)
    # Measures how many singletons were found relative to the original program's baseline size
    # This prevents the 'expansion' from diluting the precision score.
    base_total = baseline['numStructAddresses']
    base_prec_struct = baseline['valStrSingletons'] / base_total if base_total > 0 else 1.0
    poly_prec_struct = m['valStrSingletons'] / base_total if base_total > 0 else 1.0
    prec_struct = poly_prec_struct / base_prec_struct if base_prec_struct > 0 else 1.0
    
    # Relative Semantic Precision (Data-Flow Improvement)
    base_prec_sem = baseline['valSemSingletons'] / base_total if base_total > 0 else 1.0
    poly_prec_sem = m['valSemSingletons'] / base_total if base_total > 0 else 1.0
    prec_sem = poly_prec_sem / base_prec_sem if base_prec_sem > 0 else 1.0

    # Literal Precision (Data-Flow Resolution)
    # Measures how many literal addresses avoided hitting 'Top' (-1)
    prec_lit = (m['numLitAddresses'] - m['literalTopCount']) / m['numLitAddresses'] if m['numLitAddresses'] > 0 else 1.0

    # Productivity Helper (Smaragdakis et al., 2011)
    def calc_prod(poly_map, base_map):
        if not base_map: return 0.0
        hits = 0
        for x_id, szs in poly_map.items():
            base_vals = base_map.get(x_id)
            if base_vals is None: continue
            
            # Filter out -1 (Top) from baseline and get min
            filtered_base = [v for v in base_vals if v != -1]
            if not filtered_base:
                # Baseline was Top, any non-Top size in poly is a hit
                if any(s != -1 for s in szs):
                    hits += 1
                continue
            
            base_min = min(filtered_base)
            if any(s < base_min and s != -1 for s in szs):
                hits += 1
        return hits / len(base_map)

    return {
        "status": "OK",
        "time": avg_time,
        "expansion": expansion,
        "prec_struct": prec_struct,
        "prec_sem": prec_sem,
        "prec_lit": prec_lit,
        "prod_v_sem": calc_prod(m['exprToValSemSizes'], baseline['exprToValSemSizes']),
        "prod_v_str": calc_prod(m['exprToValStrSizes'], baseline['exprToValStrSizes']),
        "prod_k_str": calc_prod(m['structToContStrSizes'], baseline['structToContStrSizes']),
        "prod_sem": calc_prod(m['callToSemRetSizes'], baseline['callToSemRetSizes']),
        "prod_str": calc_prod(m['structToStrRetSizes'], baseline['structToStrRetSizes'])
    }

def generate_icfp_tables(results, baselines):
    """Aggregates data and generates Markdown tables with segmented precision."""
    rows = []
    for r in results:
        b = baselines.get(r['benchmarkName'])
        if b:
            m = compute_metrics(r, b)
            m.update({'runID': r['runID'], 'd': r['d'], 'm': r['m'], 'bench': r['benchmarkName']})
            rows.append(m)
    
    df = pd.DataFrame(rows)
    # Ensure dimensions are numeric for proper sorting in tables and plots
    df['d'] = pd.to_numeric(df['d'], errors='coerce')
    df['m'] = pd.to_numeric(df['m'], errors='coerce')
    
    # Global Summary Table (Geometric Mean for Expansion - Flemming et al., 2010)
    summary = df.groupby('runID').agg({
        'status': lambda x: (x == 'OK').sum(),
        'time': 'mean',
        'expansion': lambda x: gmean(x.dropna()) if not x.dropna().empty else np.nan,
        'prec_struct': 'mean',
        'prec_sem': 'mean',
        'prec_lit': 'mean',
        'prod_v_str': 'mean',
        'prod_k_str': 'mean',
        'prod_str': 'mean'
    }).rename(columns={
        'status': 'Solved', 
        'time': 'Time (s)', 
        'prec_struct': 'Rel Struct Prec',
        'prec_sem': 'Rel Sem Prec',
        'prec_lit': 'Literal Prec',
        'prod_v_str': 'Val Prod',
        'prod_k_str': 'Cont Prod',
        'prod_str': 'Ret Prod'
    })
    
    # Marginal Utility Tables (Kastrinis & Smaragdakis, 2013)
    struct_mu = df[df['status'] == 'OK'].pivot_table(index='d', columns='m', values='prec_struct', aggfunc='mean')
    sem_mu = df[df['status'] == 'OK'].pivot_table(index='d', columns='m', values='prec_sem', aggfunc='mean')
    time_mu = df[df['status'] == 'OK'].pivot_table(index='d', columns='m', values='time', aggfunc='mean')

    print("### Table 1: Global Efficiency, Time & Relative Precision")
    print(summary.to_markdown())
    print("\n### Table 2: Marginal Structural Improvement (Relative to Baseline)")
    print(struct_mu.to_markdown())
    print("\n### Table 3: Marginal Semantic Improvement (Relative to Baseline)")
    print(sem_mu.to_markdown())
    print("\n### Table 4: Marginal Time Cost (Seconds)")
    print(time_mu.to_markdown())
    
    return df, struct_mu, sem_mu, time_mu

def plot_visualizations(df, struct_mu, sem_mu, time_mu):
    """Generates Pareto frontiers for both space and time complexity."""
    sns.set_theme(style="whitegrid")
    
    # Group by both dimensions to preserve them in the aggregated dataframe
    plot_df = df[df['status'] == 'OK'].groupby(['runID', 'd', 'm']).agg({
        'expansion': lambda x: gmean(x.dropna()),
        'time': 'mean',
        'prec_struct': 'mean',
        'prec_sem': 'mean'
    }).reset_index()
    
    # Sort by numerical values first
    plot_df = plot_df.sort_values(['d', 'm'])
    
    # Convert to string for categorical plotting to handle non-linear gaps (0, 1, 2, 20, 100)
    # Re-using names 'd' and 'm' so they appear correctly in the legend
    plot_df['d'] = plot_df['d'].astype(str)
    plot_df['m'] = plot_df['m'].astype(str)

    # Plot Pareto Frontiers (Expansion vs Precisions)
    for metric, label, filename_pfx in [
        ('prec_struct', 'Structural Improvement', 'expansion_struct'),
        ('prec_sem', 'Semantic Improvement', 'expansion_sem')
    ]:
        fig, ax = plt.subplots(figsize=(12, 7))
        sns.scatterplot(data=plot_df, x='expansion', y=metric, 
                        hue='d', style='m', s=200, 
                        palette="bright", edgecolor="black", alpha=0.8, ax=ax)
        ax.set_title(f"Pareto Frontier: State Space Expansion vs {label}", fontsize=15, pad=20)
        ax.set_xlabel("Expansion Factor (Geometric Mean, Log Scale)")
        ax.set_xscale('log')
        ax.set_ylabel(f"Relative Precision (Baseline = 1.0)")
        ax.legend(title="Sensitivity (d, m)", bbox_to_anchor=(1.05, 1), loc='upper left')
        plt.tight_layout()
        plt.savefig(f"pareto_{filename_pfx}.png", bbox_inches='tight')
    
    # Plot Pareto Frontiers (Time vs Precisions)
    for metric, label, filename_pfx in [
        ('prec_struct', 'Structural Improvement', 'time_struct'),
        ('prec_sem', 'Semantic Improvement', 'time_sem')
    ]:
        fig, ax = plt.subplots(figsize=(12, 7))
        sns.scatterplot(data=plot_df, x='time', y=metric, 
                        hue='d', style='m', s=200, 
                        palette="bright", edgecolor="black", alpha=0.8, ax=ax)
        ax.set_title(f"Pareto Frontier: Execution Time vs {label}", fontsize=15, pad=20)
        ax.set_xlabel("Execution Time (Seconds, Log Scale)")
        ax.set_xscale('log')
        ax.set_ylabel(f"Relative Precision (Baseline = 1.0)")
        ax.legend(title="Sensitivity (d, m)", bbox_to_anchor=(1.05, 1), loc='upper left')
        plt.tight_layout()
        plt.savefig(f"pareto_{filename_pfx}.png", bbox_inches='tight')
    
    # Heatmaps
    for data, title, filename in [
        (struct_mu, "Heatmap: Structural Improvement", "heatmap_struct.png"),
        (sem_mu, "Heatmap: Semantic Improvement", "heatmap_sem.png")
    ]:
        fig, ax = plt.subplots(figsize=(10, 8))
        sns.heatmap(data, annot=True, cmap="YlGnBu", fmt=".2f", ax=ax)
        ax.set_title(title, fontsize=15, pad=20)
        ax.set_xlabel("Sensitivity m")
        ax.set_ylabel("Sensitivity d")
        plt.tight_layout()
        plt.savefig(filename, bbox_inches='tight')

    plt.show()

def process_histogram(hist):
    """Separates literals (top) from countable cardinalities."""
    clean_hist = {int(k): v for k, v in hist.items() if int(k) != -1}
    top_count = hist.get("-1", 0)
    return clean_hist, top_count

def main():
    results_path = "benchmarks/results"
    if not os.path.exists(results_path):
        print(f"Error: Path '{results_path}' does not exist.")
        return

    results = load_hierarchical_data(results_path)
    if not results:
        print("Error: No data found in benchmarks/results.")
        return
    
    # Identify baselines (typically the 0-sensitivity configuration: d=0, m=0)
    baselines = {
        r['benchmarkName']: r['storeMetrics']
        for r in results
        if str(r['d']) == '0' and str(r['m']) == '0' and r.get('storeMetrics')
    }

    if not baselines:
        print("Warning: No baseline results (d=0, m=0) found. Comparisons may be limited.")

    df, struct_mu, sem_mu, time_mu = generate_icfp_tables(results, baselines)
    plot_visualizations(df, struct_mu, sem_mu, time_mu)

if __name__ == "__main__":
    main()