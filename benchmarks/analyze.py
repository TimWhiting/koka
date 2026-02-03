import json
import os
import numpy as np
import pandas as pd
from scipy.stats import gmean
import matplotlib.pyplot as plt
import seaborn as sns

def safe_gmean(x):
    """Computes geometric mean safely, handling zeros, negatives, and empty sets."""
    if x is None: return np.nan
    clean = pd.to_numeric(x, errors='coerce').dropna()
    # gmean requires strictly positive values
    pos = clean[clean > 0]
    if pos.empty:
        return np.nan
    return gmean(pos)

def load_hierarchical_data(root_path):
    """Loads results from results/variant/d/m hierarchy recursively."""
    all_results = []
    print(f"Scanning {root_path}...")
    for root, dirs, files in os.walk(root_path):
        for f_name in files:
            if f_name.endswith('.json'):
                # Try to infer variant, d, m from the path relative to root_path
                rel_path = os.path.relpath(root, root_path)
                parts = rel_path.split(os.sep)
                # Structure: variant/d/m/...
                if len(parts) >= 3:
                    variant = parts[0]
                    d = parts[1]
                    m = parts[2]
                    
                    file_path = os.path.join(root, f_name)
                    with open(file_path, 'r') as f:
                        try:
                            # Use a more robust check for file size
                            if os.path.getsize(file_path) == 0:
                                continue
                            data = json.load(f)
                            # Ensure we have a dictionary
                            if isinstance(data, dict):
                                data.update({
                                    'variant': variant, 
                                    'runID': f"{d}-{m}", 
                                    'd': d, 
                                    'm': m,
                                    'filePath': file_path
                                })
                                all_results.append(data)
                        except (json.JSONDecodeError, ValueError):
                            print(f"Warning: Failed to decode {file_path}")
    
    print(f"Loaded {len(all_results)} valid result files.")
    return all_results

def compute_metrics(run, baseline_run):
    """Computes relative and absolute precision metrics using explicit store sizes."""
    analysis_times = run.get('analysisTimes', [])
    avg_time = np.mean(analysis_times) if analysis_times else 0.0
    
    base_times = baseline_run.get('analysisTimes', [])
    base_avg_time = np.mean(base_times) if base_times else 0.0
    rel_time = avg_time / base_avg_time if base_avg_time > 0 else 1.0

    if run.get('isTimeout') or run.get('storeMetrics') is None:
        return {
            "status": "T/O", 
            "time": avg_time, 
            "rel_time": rel_time,
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
    baseline = baseline_run['storeMetrics']
    
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
            # if len(base_vals) > 1: raise Exception(f"Unexpected list length in base map {base_vals} {x_id}")
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
        "rel_time": rel_time,
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

def generate_icfp_tables(results, baselines, variant_name):
    """Aggregates data and generates Markdown tables with segmented precision."""
    rows = []
    for r in results:
        b = baselines.get(r['benchmarkName'])
        if b:
            # compute_metrics now takes the full baseline run object
            m = compute_metrics(r, b)
            m.update({
                'runID': r['runID'], 
                'd': r['d'], 
                'm': r['m'], 
                'bench': r['benchmarkName'],
                'variant': r['variant']
            })
            rows.append(m)
    
    if not rows:
        return pd.DataFrame(), None, None, None

    df = pd.DataFrame(rows)
    # Ensure dimensions are numeric for proper sorting in tables and plots
    df['d'] = pd.to_numeric(df['d'], errors='coerce')
    df['m'] = pd.to_numeric(df['m'], errors='coerce')
    
    # Global Summary Table (Geometric Mean for Expansion - Flemming et al., 2010)
    summary = df.groupby('runID').agg({
        'status': lambda x: (x == 'OK').sum(),
        'time': 'mean',
        'rel_time': safe_gmean,
        'expansion': safe_gmean,
        'prec_struct': 'mean',
        'prec_sem': 'mean',
        'prec_lit': 'mean',
        'prod_v_str': 'mean',
        'prod_k_str': 'mean',
        'prod_str': 'mean'
    }).rename(columns={
        'status': 'Solved', 
        'time': 'Time (s)', 
        'rel_time': 'Rel Time',
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
    time_mu = df[df['status'] == 'OK'].pivot_table(index='d', columns='m', values='rel_time', aggfunc=safe_gmean)

    print(f"\n## Variant: {variant_name}")
    print("### Table 1: Global Efficiency, Time & Relative Precision")
    print(summary.to_markdown())
    print("\n### Table 2: Marginal Structural Improvement (Relative to Baseline)")
    print(struct_mu.to_markdown())
    print("\n### Table 3: Marginal Semantic Improvement (Relative to Baseline)")
    print(sem_mu.to_markdown())
    print("\n### Table 4: Marginal Time Overhead (Relative to Baseline)")
    print(time_mu.to_markdown())
    
    return df, struct_mu, sem_mu, time_mu

def plot_visualizations(df, struct_mu, sem_mu, time_mu, variant_name):
    """Generates Pareto frontiers for both space and time complexity."""
    sns.set_theme(style="whitegrid")
    
    output_dir = os.path.join("benchmarks/analysis", variant_name)
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    
    # Count timeouts per runID for annotations
    timeout_counts = df[df['status'] == 'T/O'].groupby('runID').size().to_dict()
    total_counts = df.groupby('runID').size().to_dict()
    
    # Group by both dimensions to preserve them in the aggregated dataframe
    plot_df = df[df['status'] == 'OK'].groupby(['runID', 'd', 'm']).agg({
        'expansion': safe_gmean,
        'rel_time': safe_gmean,
        'prec_struct': 'mean',
        'prec_sem': 'mean'
    }).reset_index()
    
    if plot_df.empty:
        print(f"Warning: No successful results to plot for variant {variant_name}.")
        return

    print(f"Plotting {len(plot_df)} points for variant {variant_name}.")
    
    # Sort by numerical values first
    plot_df = plot_df.sort_values(['d', 'm'])
    
    # Add timeout info to plot_df for annotations
    plot_df['timeouts'] = plot_df['runID'].map(lambda x: timeout_counts.get(x, 0))
    plot_df['total'] = plot_df['runID'].map(lambda x: total_counts.get(x, 0))
    
    # Convert to string for categorical plotting to handle non-linear gaps (0, 1, 2, 20, 100)
    # Re-using names 'd' and 'm' so they appear correctly in the legend
    plot_df['d'] = plot_df['d'].astype(str)
    plot_df['m'] = plot_df['m'].astype(str)

    def add_timeout_annotations(ax, plot_df, x_col, y_col):
        """Add timeout count annotations to points that have timeouts."""
        for _, row in plot_df[plot_df['timeouts'] > 0].iterrows():
            ax.annotate(
                f"⚠{int(row['timeouts'])}",
                xy=(row[x_col], row[y_col]),
                xytext=(5, 5),
                textcoords='offset points',
                fontsize=9,
                color='red',
                fontweight='bold'
            )

    # Plot Pareto Frontiers (Expansion vs Precisions)
    for metric, label, filename_pfx in [
        ('prec_struct', 'Structural Improvement', 'expansion_struct'),
        ('prec_sem', 'Semantic Improvement', 'expansion_sem')
    ]:
        fig, ax = plt.subplots(figsize=(12, 7))
        sns.scatterplot(data=plot_df, x='expansion', y=metric, 
                        hue='d', style='m', s=200, 
                        palette="bright", edgecolor="black", alpha=0.8, ax=ax)
        add_timeout_annotations(ax, plot_df, 'expansion', metric)
        ax.set_title(f"[{variant_name}] Pareto: Space vs {label}", fontsize=15, pad=20)
        ax.set_xlabel("Expansion Factor (Geometric Mean, Log Scale)")
        ax.set_xscale('log')
        ax.set_ylabel(f"Relative Precision (Baseline = 1.0)")
        # Add timeout legend note
        handles, labels = ax.get_legend_handles_labels()
        ax.legend(handles, labels, title="Sensitivity (d, m)\n⚠N = N timeouts", 
                  bbox_to_anchor=(1.05, 1), loc='upper left')
        plt.tight_layout()
        print(f"Saving Pareto Space: {os.path.join(output_dir, f'pareto_{filename_pfx}.png')}")
        plt.savefig(os.path.join(output_dir, f"pareto_{filename_pfx}.png"), bbox_inches='tight')
        plt.show()
        plt.close()
    
    # Plot Pareto Frontiers (Rel Time vs Precisions)
    for metric, label, filename_pfx in [
        ('prec_struct', 'Structural Improvement', 'time_struct'),
        ('prec_sem', 'Semantic Improvement', 'time_sem')
    ]:
        fig, ax = plt.subplots(figsize=(12, 7))
        sns.scatterplot(data=plot_df, x='rel_time', y=metric, 
                        hue='d', style='m', s=200, 
                        palette="bright", edgecolor="black", alpha=0.8, ax=ax)
        add_timeout_annotations(ax, plot_df, 'rel_time', metric)
        ax.set_title(f"[{variant_name}] Pareto: Relative Time vs {label}", fontsize=15, pad=20)
        ax.set_xlabel("Time Overhead (Geometric Mean, Log Scale)")
        ax.set_xscale('log')
        ax.set_ylabel(f"Relative Precision (Baseline = 1.0)")
        # Add timeout legend note
        handles, labels = ax.get_legend_handles_labels()
        ax.legend(handles, labels, title="Sensitivity (d, m)\n⚠N = N timeouts", 
                  bbox_to_anchor=(1.05, 1), loc='upper left')
        plt.tight_layout()
        print(f"Saving Pareto Time: {os.path.join(output_dir, f'pareto_{filename_pfx}.png')}")
        plt.savefig(os.path.join(output_dir, f"pareto_{filename_pfx}.png"), bbox_inches='tight')
        plt.show()
        plt.close()
    
    # Heatmaps
    for data, title, filename in [
        (struct_mu, "Heatmap: Structural Improvement", "heatmap_struct.png"),
        (sem_mu, "Heatmap: Semantic Improvement", "heatmap_sem.png"),
        (time_mu, "Heatmap: Time Overhead (Relative)", "heatmap_time.png")
    ]:
        # Skip if data is empty or all NaN
        if data is None or data.empty or data.isna().all().all():
            print(f"Warning: Skipping heatmap '{filename}' for variant {variant_name} - no valid data.")
            continue
        fig, ax = plt.subplots(figsize=(10, 8))
        sns.heatmap(data, annot=True, cmap="YlGnBu", fmt=".2f", ax=ax)
        ax.set_title(f"[{variant_name}] {title}", fontsize=15, pad=20)
        ax.set_xlabel("Sensitivity m")
        ax.set_ylabel("Sensitivity d")
        plt.tight_layout()
        print(f"Saving Heatmap: {os.path.join(output_dir, filename)}")
        plt.savefig(os.path.join(output_dir, filename), bbox_inches='tight')
        plt.show()
        plt.close()

def plot_histograms(results, variant_name):
    """Plots the distribution of set sizes for semantic and structural precision."""
    output_dir = os.path.join("benchmarks/analysis", variant_name)
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    # Select representative runIDs (e.g., d=0, m=0 and some higher ones)
    available_ids = sorted(list(set(r['runID'] for r in results)), key=lambda x: [int(v) for v in x.split('-')])
    target_ids = [tid for tid in ['0-0', '1-1', '2-2', '3-3', '100-100'] if tid in available_ids]
    if not target_ids:
        target_ids = available_ids[:3]

    fig, axes = plt.subplots(len(target_ids), 2, figsize=(14, 4 * len(target_ids)))
    if len(target_ids) == 1:
        axes = [axes]

    for i, run_id in enumerate(target_ids):
        sem_counts = {}
        str_counts = {}
        
        for r in results:
            if r['runID'] == run_id and r.get('storeMetrics'):
                m = r['storeMetrics']
                # Aggregate across all program points for more stable histograms
                for sizes in m.get('exprToValSemSizes', {}).values():
                    for s in sizes:
                        s_val = s if s != -1 else "Top"
                        sem_counts[s_val] = sem_counts.get(s_val, 0) + 1
                for sizes in m.get('exprToValStrSizes', {}).values():
                    for s in sizes:
                        s_val = s if s != -1 else "Top"
                        str_counts[s_val] = str_counts.get(s_val, 0) + 1

        for j, (counts, title, color) in enumerate([
            (sem_counts, f"Semantic Val Cardinality ({run_id})", "skyblue"),
            (str_counts, f"Structural Val Cardinality ({run_id})", "salmon")
        ]):
            ax = axes[i][j]
            if not counts: 
                ax.text(0.5, 0.5, "No Data", ha='center')
                continue
            
            # Sort keys: numbers first, then "Top"
            sorted_keys = sorted([k for k in counts.keys() if k != "Top"]) + (["Top"] if "Top" in counts else [])
            vals = [counts[k] for k in sorted_keys]
            
            sns.barplot(x=[str(k) for k in sorted_keys], y=vals, ax=ax, color=color, edgecolor="black")
            ax.set_title(f"[{variant_name}] {title}", fontsize=12)
            ax.set_xlabel("Set Size (Card)")
            ax.set_ylabel("Frequency (Program Points)")

    plt.tight_layout()
    plt.savefig(os.path.join(output_dir, "cardinality_histograms.png"), bbox_inches='tight')
    plt.close()

def main():
    results_path = "benchmarks/results"
    if not os.path.exists(results_path):
        print(f"Error: Path '{results_path}' does not exist.")
        return

    all_results = load_hierarchical_data(results_path)
    if not all_results:
        print("Error: No data found in benchmarks/results.")
        return
    
    # Group results by variant
    variants = {}
    for r in all_results:
        v = r['variant']
        if v not in variants:
            variants[v] = []
        variants[v].append(r)
    
    for v_name, v_results in variants.items():
        # Identify baselines (typically the 0-sensitivity configuration: d=0, m=0) for THIS variant
        baselines = {
            r['benchmarkName']: r
            for r in v_results
            if str(r['d']) == '0' and str(r['m']) == '0' and r.get('storeMetrics')
        }

        if not baselines:
            print(f"Warning: No baseline results (d=0, m=0) found for variant '{v_name}'.")

        df, struct_mu, sem_mu, time_mu = generate_icfp_tables(v_results, baselines, v_name)
        if not df.empty:
            plot_visualizations(df, struct_mu, sem_mu, time_mu, v_name)
            plot_histograms(v_results, v_name)

if __name__ == "__main__":
    main()