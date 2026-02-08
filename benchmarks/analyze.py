import json
import os

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns
from scipy.stats import gmean


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

def plot_size_vs_time_comparison(all_results, min_size=100):
    """
    Plots program size (configurations visited from 0CFA) vs analysis time for different analyses and sensitivities.
    Shows d=0,1,2 in rows with KCFA baseline on left, includes timeout counts.
    Program size = numTotalFixInputStates - numStoreAddresses (number of configurations/Step states visited)
    
    Args:
        all_results: List of all benchmark results
        min_size: Minimum program size (configurations visited) to include (default: 100)
    """
    sns.set_theme(style="whitegrid")
    
    # Get program sizes from KCFA d=0, m=0 (this is 0CFA)
    program_sizes = {}
    for r in all_results:
        if r['variant'] == 'kcfa' and str(r['d']) == '0' and str(r['m']) == '0':
            if r.get('storeMetrics'):
                bench = r['benchmarkName']
                # Filter out benchmarks/suite programs (smallest benchmarks)
                if '/suite/' in bench:
                    continue
                m = r['storeMetrics']
                # Use configurations visited as program size proxy
                total_states = m.get('numTotalFixInputStates', 0)
                store_addrs = m.get('numStoreAddresses', 0)
                configs_visited = total_states - store_addrs
                if configs_visited > 0 and configs_visited >= min_size:
                    program_sizes[bench] = configs_visited
    
    if not program_sizes:
        print("Warning: No KCFA 0-0 results found to determine program sizes.")
        return
    
    print(f"Found {len(program_sizes)} benchmarks with program size data")
    
    # Collect data for plotting (including timeout info)
    plot_data = []
    timeout_data = []
    timeout_counts = {}
    
    # Define which configurations to plot: d=0,1,2 for DMCFAR/DMCFAE, always KCFA
    d_values = ['0', '1', '2']
    m_values = ['0', '1', '2', '3']
    
    for r in all_results:
        bench = r['benchmarkName']
        if bench not in program_sizes:
            continue
            
        variant = r['variant']
        d = str(r['d'])
        m = str(r['m'])
        
        # Track timeouts
        config_key = (variant, d, m)
        if config_key not in timeout_counts:
            timeout_counts[config_key] = {'total': 0, 'timeout': 0}
        timeout_counts[config_key]['total'] += 1
        
        # KCFA: d is always 0, m is the k parameter
        if variant == 'kcfa' and d == '0' and m in m_values:
            times = r.get('analysisTimes', [])
            is_timeout = r.get('isTimeout', False)
            
            if is_timeout:
                timeout_counts[config_key]['timeout'] += 1
                # Add timeout point for visualization
                timeout_data.append({
                    'benchmark': bench,
                    'programSize': program_sizes[bench],
                    'variant': variant,
                    'd': d,
                    'm': m
                })
                # Add timeout to plot_data with penalty time for trendline fitting
                plot_data.append({
                    'benchmark': bench,
                    'programSize': program_sizes[bench],
                    'time': 600,  # Penalty: slightly above 500s timeout
                    'variant': variant,
                    'd': d,
                    'm': m,
                    'is_timeout': True
                })
            elif times:
                avg_time = np.mean(times)
                plot_data.append({
                    'benchmark': bench,
                    'programSize': program_sizes[bench],
                    'time': avg_time,
                    'variant': variant,
                    'd': d,
                    'm': m,
                    'is_timeout': False
                })
        
        # DMCFAR/DMCFAE: both d and m vary
        elif variant in ['dmcfar', 'dmcfae'] and d in d_values and m in m_values:
            times = r.get('analysisTimes', [])
            is_timeout = r.get('isTimeout', False)
            
            if is_timeout:
                timeout_counts[config_key]['timeout'] += 1
                # Add timeout point for visualization
                timeout_data.append({
                    'benchmark': bench,
                    'programSize': program_sizes[bench],
                    'variant': variant,
                    'd': d,
                    'm': m
                })
                # Add timeout to plot_data with penalty time for trendline fitting
                plot_data.append({
                    'benchmark': bench,
                    'programSize': program_sizes[bench],
                    'time': 600,  # Penalty: slightly above 500s timeout
                    'variant': variant,
                    'd': d,
                    'm': m,
                    'is_timeout': True
                })
            elif times:
                avg_time = np.mean(times)
                plot_data.append({
                    'benchmark': bench,
                    'programSize': program_sizes[bench],
                    'time': avg_time,
                    'variant': variant,
                    'd': d,
                    'm': m,
                    'is_timeout': False
                })
    
    if not plot_data:
        print("Warning: No matching data found for size vs time plot.")
        return
    
    df = pd.DataFrame(plot_data)
    df_timeout = pd.DataFrame(timeout_data) if timeout_data else pd.DataFrame()
    print(f"Plotting {len(df)} data points and {len(df_timeout)} timeout points")
    
    # Create grid: rows=d values (0,1,2), columns=variants (KCFA, DMCFAR, DMCFAE)
    d_values = ['0', '1', '2']
    fig, axes = plt.subplots(3, 3, figsize=(18, 14), sharex=True, sharey=True)
    
    # Define styling
    sensitivity_styles = {
        '0': {'linestyle': '-', 'linewidth': 2.5, 'marker': 'o', 'markersize': 5},
        '1': {'linestyle': '--', 'linewidth': 2, 'marker': 's', 'markersize': 4},
        '2': {'linestyle': ':', 'linewidth': 2, 'marker': '^', 'markersize': 4},
        '3': {'linestyle': '-.', 'linewidth': 2, 'marker': 'D', 'markersize': 3},
    }
    
    variant_info = [
        ('kcfa', 'KCFA', '#1f77b4'),
        ('dmcfar', 'DMCFAR', '#ff7f0e'),
        ('dmcfae', 'DMCFAE', '#2ca02c')
    ]
    
    for row_idx, d_val in enumerate(d_values):
        for col_idx, (variant, variant_name, color) in enumerate(variant_info):
            ax = axes[row_idx, col_idx]
            
            # For KCFA, d is always 0 (only k/m varies)
            if variant == 'kcfa':
                variant_df = df[df['variant'] == variant].copy()
                title_d = "k-CFA"
            else:
                variant_df = df[(df['variant'] == variant) & (df['d'] == d_val)].copy()
                title_d = f"d={d_val}"
            
            if variant_df.empty:
                ax.text(0.5, 0.5, 'No data', ha='center', va='center', 
                       transform=ax.transAxes, fontsize=11)
            else:
                # Find max time for timeout marker placement
                max_time = variant_df['time'].max() if not variant_df.empty else 100
                timeout_marker_y = max_time * 1.5  # Place timeouts above the data
                
                # Plot each sensitivity level
                for m_val in sorted(variant_df['m'].unique()):
                    subset = variant_df[variant_df['m'] == m_val].sort_values('programSize')
                    style = sensitivity_styles.get(m_val, sensitivity_styles['0'])
                    
                    # Get timeout count for legend
                    config_key = (variant, d_val if variant != 'kcfa' else '0', m_val)
                    t_info = timeout_counts.get(config_key, {'total': 0, 'timeout': 0})
                    n_timeout = t_info['timeout']
                    
                    # Fit trendline using ALL points including timeouts
                    # DMCFAR: polynomial (log-log space), KCFA/DMCFAE: exponential (log-linear space)
                    slope_str = ""
                    if len(subset) >= 2:
                        x_vals = subset['programSize'].values
                        y_vals = subset['time'].values
                        
                        if variant == 'dmcfar':
                            # Polynomial fit: y = a * x^b (linear in log-log space)
                            log_x = np.log10(x_vals)
                            log_y = np.log10(y_vals)
                            coeffs = np.polyfit(log_x, log_y, 1)
                            slope = coeffs[0]  # exponent in y = x^slope relationship
                            slope_str = f' [x^{slope:.2f}]'
                        else:  # kcfa or dmcfae
                            # Exponential fit: y = a * exp(b*x) (linear in log-linear space)
                            log_y = np.log10(y_vals)
                            coeffs = np.polyfit(x_vals, log_y, 1)
                            slope = coeffs[0]  # coefficient in exp(slope*x)
                            slope_str = f' [exp({slope:.2e}*x)]'
                    
                    if variant == 'kcfa':
                        label = f'k={m_val}{slope_str}' + (f' (T/O:{n_timeout})' if n_timeout > 0 else '')
                    else:
                        label = f'm={m_val}{slope_str}' + (f' (T/O:{n_timeout})' if n_timeout > 0 else '')
                    
                    # Plot scatter points only for non-timeout data
                    non_timeout_subset = subset[~subset['is_timeout']]
                    ax.scatter(non_timeout_subset['programSize'], non_timeout_subset['time'], 
                              color=color, alpha=0.7, label=label, 
                              marker=style['marker'], s=style['markersize']**2, zorder=5)
                    
                    # Plot trendline using all data (including timeouts)
                    if len(subset) >= 2:
                        x_range = np.linspace(subset['programSize'].min(), 
                                             subset['programSize'].max(), 100)
                        
                        if variant == 'dmcfar':
                            # Polynomial trendline
                            poly = np.poly1d(coeffs)
                            y_trend = 10 ** poly(np.log10(x_range))
                        else:  # kcfa or dmcfae
                            # Exponential trendline
                            poly = np.poly1d(coeffs)
                            y_trend = 10 ** poly(x_range)
                        
                        # Plot trendline with same color but more transparent
                        ax.plot(x_range, y_trend, color=color, alpha=0.4, 
                               linestyle=style['linestyle'], linewidth=2, zorder=2)
                    
                    # Plot timeout markers for this m_val
                    if not df_timeout.empty:
                        if variant == 'kcfa':
                            timeout_subset = df_timeout[(df_timeout['variant'] == variant) & 
                                                       (df_timeout['m'] == m_val)]
                        else:
                            timeout_subset = df_timeout[(df_timeout['variant'] == variant) & 
                                                       (df_timeout['d'] == d_val) & 
                                                       (df_timeout['m'] == m_val)]
                        
                        if not timeout_subset.empty:
                            ax.scatter(timeout_subset['programSize'], 
                                     [timeout_marker_y] * len(timeout_subset),
                                     marker='x', s=100, color='red', alpha=0.8, 
                                     linewidths=2, zorder=10)
            
            # Labels and formatting
            if row_idx == 2:
                ax.set_xlabel('Program Size (0CFA Configs)', fontsize=10)
            if col_idx == 0:
                ax.set_ylabel('Time (seconds)', fontsize=10)
            
            # Title
            if row_idx == 0:
                ax.set_title(f'{variant_name}\n{title_d}', fontsize=12, fontweight='bold', pad=8)
            else:
                ax.set_title(title_d, fontsize=11, pad=5)
            
            ax.set_xscale('log')
            ax.set_yscale('log')
            ax.legend(fontsize=8, loc='best', framealpha=0.9)
            ax.grid(True, alpha=0.3, which='both')
            ax.set_axisbelow(True)
    
    fig.suptitle('Program Size vs Analysis Time: KCFA Baseline (left) vs DMCFAR vs DMCFAE\n' + 
                 'Rows: Delimiter Depth d | T/O = Timeout Count', 
                 fontsize=14, fontweight='bold', y=0.995)
    plt.tight_layout(rect=[0, 0, 1, 0.99])
    
    output_path = "benchmarks/analysis/size_vs_time_comparison.png"
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    plt.savefig(output_path, bbox_inches='tight', dpi=150)
    print(f"Saved: {output_path}")
    
    plt.show()
    plt.close('all')

def plot_size_vs_cont_precision(all_results, min_size=100):
    """Plot program size vs continuation precision (contStrSingletons / numCont) across variants.
    
    Args:
        all_results: List of all benchmark results
        min_size: Minimum program size (configurations visited) to include (default: 100)
    """
    
    # Get program sizes from KCFA 0-0 baseline
    program_sizes = {}
    for r in all_results:
        if r['variant'] == 'kcfa' and str(r['d']) == '0' and str(r['m']) == '0':
            bench = r['benchmarkName']
            # Filter out benchmarks/suite programs (smallest benchmarks)
            if '/suite/' in bench:
                continue
            if r.get('storeMetrics'):
                m = r['storeMetrics']
                total_states = m.get('numTotalFixInputStates', 0)
                store_addrs = m.get('numStoreAddresses', 0)
                configs_visited = total_states - store_addrs
                if configs_visited > 0 and configs_visited >= min_size:
                    program_sizes[bench] = configs_visited
    
    if not program_sizes:
        print("Warning: No KCFA 0-0 results found to determine program sizes.")
        return
    
    print(f"Found {len(program_sizes)} benchmarks with program size data")
    
    # Collect data for plotting
    plot_data = []
    timeout_counts = {}
    
    d_values = ['0', '1', '2']
    m_values = ['0', '1', '2', '3']
    
    for r in all_results:
        bench = r['benchmarkName']
        if bench not in program_sizes:
            continue
            
        variant = r['variant']
        d = str(r['d'])
        m = str(r['m'])
        
        config_key = (variant, d, m)
        if config_key not in timeout_counts:
            timeout_counts[config_key] = {'total': 0, 'timeout': 0}
        timeout_counts[config_key]['total'] += 1
        
        # Skip timeouts and entries without metrics
        is_timeout = r.get('isTimeout', False)
        if is_timeout:
            timeout_counts[config_key]['timeout'] += 1
            continue
        
        if not r.get('storeMetrics'):
            continue
            
        metrics = r['storeMetrics']
        num_cont = metrics.get('numContAddresses', 0)
        cont_str_singletons = metrics.get('contStrSingletons', 0)
        
        # Calculate continuation precision (avoid division by zero)
        if num_cont > 0:
            cont_precision = cont_str_singletons / num_cont
        else:
            continue  # Skip if no continuations
        
        # KCFA: d is always 0, m is the k parameter
        if variant == 'kcfa' and d == '0' and m in m_values:
            plot_data.append({
                'benchmark': bench,
                'programSize': program_sizes[bench],
                'contPrecision': cont_precision,
                'variant': variant,
                'd': d,
                'm': m
            })
        
        # DMCFAR/DMCFAE: both d and m vary
        elif variant in ['dmcfar', 'dmcfae'] and d in d_values and m in m_values:
            plot_data.append({
                'benchmark': bench,
                'programSize': program_sizes[bench],
                'contPrecision': cont_precision,
                'variant': variant,
                'd': d,
                'm': m
            })
    
    if not plot_data:
        print("Warning: No matching data found for size vs continuation precision plot.")
        return
    
    df = pd.DataFrame(plot_data)
    print(f"Plotting {len(df)} data points for continuation precision")
    
    # Create grid: rows=d values (0,1,2), columns=variants (KCFA, DMCFAR, DMCFAE)
    d_values = ['0', '1', '2']
    fig, axes = plt.subplots(3, 3, figsize=(18, 14), sharex=True, sharey=True)
    
    # Define styling
    sensitivity_styles = {
        '0': {'linestyle': '-', 'linewidth': 2.5, 'marker': 'o', 'markersize': 5},
        '1': {'linestyle': '--', 'linewidth': 2, 'marker': 's', 'markersize': 4},
        '2': {'linestyle': ':', 'linewidth': 2, 'marker': '^', 'markersize': 4},
        '3': {'linestyle': '-.', 'linewidth': 2, 'marker': 'D', 'markersize': 3},
    }
    
    variant_info = [
        ('kcfa', 'KCFA', '#1f77b4'),
        ('dmcfar', 'DMCFAR', '#ff7f0e'),
        ('dmcfae', 'DMCFAE', '#2ca02c')
    ]
    
    for row_idx, d_val in enumerate(d_values):
        for col_idx, (variant, variant_name, color) in enumerate(variant_info):
            ax = axes[row_idx, col_idx]
            
            # For KCFA, d is always 0 (only k/m varies)
            if variant == 'kcfa':
                variant_df = df[df['variant'] == variant].copy()
                title_d = "k-CFA"
            else:
                variant_df = df[(df['variant'] == variant) & (df['d'] == d_val)].copy()
                title_d = f"d={d_val}"
            
            if variant_df.empty:
                ax.text(0.5, 0.5, 'No data', ha='center', va='center', 
                       transform=ax.transAxes, fontsize=11)
            else:
                # Plot each sensitivity level
                for m_val in sorted(variant_df['m'].unique()):
                    subset = variant_df[variant_df['m'] == m_val].sort_values('programSize')
                    style = sensitivity_styles.get(m_val, sensitivity_styles['0'])
                    
                    # Get timeout count for legend
                    config_key = (variant, d_val if variant != 'kcfa' else '0', m_val)
                    t_info = timeout_counts.get(config_key, {'total': 0, 'timeout': 0})
                    n_timeout = t_info['timeout']
                    
                    # Fit trendline using ALL points
                    # Continuation precision: polynomial fit makes more sense (log-log space)
                    slope_str = ""
                    if len(subset) >= 2:
                        x_vals = subset['programSize'].values
                        y_vals = subset['contPrecision'].values
                        
                        # Use log-log fit for all variants
                        log_x = np.log10(x_vals)
                        log_y = np.log10(y_vals)
                        coeffs = np.polyfit(log_x, log_y, 1)
                        slope = coeffs[0]  # exponent in y = x^slope relationship
                        slope_str = f' [x^{slope:.2f}]'
                    
                    if variant == 'kcfa':
                        label = f'k={m_val}{slope_str}' + (f' (T/O:{n_timeout})' if n_timeout > 0 else '')
                    else:
                        label = f'm={m_val}{slope_str}' + (f' (T/O:{n_timeout})' if n_timeout > 0 else '')
                    
                    # Plot scatter points
                    ax.scatter(subset['programSize'], subset['contPrecision'], 
                              color=color, alpha=0.7, label=label, 
                              marker=style['marker'], s=style['markersize']**2, zorder=5)
                    
                    # Plot trendline
                    if len(subset) >= 2:
                        poly = np.poly1d(coeffs)
                        
                        # Generate smooth trendline in log-log space
                        x_range = np.logspace(np.log10(subset['programSize'].min()), 
                                             np.log10(subset['programSize'].max()), 100)
                        y_trend = 10 ** poly(np.log10(x_range))
                        
                        # Plot trendline with same color but more transparent
                        ax.plot(x_range, y_trend, color=color, alpha=0.4, 
                               linestyle=style['linestyle'], linewidth=2, zorder=2)
            
            # Labels and formatting
            if row_idx == 2:
                ax.set_xlabel('Program Size (0CFA Configs)', fontsize=10)
            if col_idx == 0:
                ax.set_ylabel('Continuation Precision', fontsize=10)
            
            # Title
            if row_idx == 0:
                ax.set_title(f'{variant_name}\n{title_d}', fontsize=12, fontweight='bold', pad=8)
            else:
                ax.set_title(title_d, fontsize=11, pad=5)
            
            ax.set_xscale('log')
            ax.set_yscale('log')
            ax.legend(fontsize=8, loc='best', framealpha=0.9)
            ax.grid(True, alpha=0.3, which='both')
            ax.set_axisbelow(True)
    
    fig.suptitle('Program Size vs Continuation Precision (contStrSingletons / numCont)\n' + 
                 'Rows: Delimiter Depth d | T/O = Timeout Count', 
                 fontsize=14, fontweight='bold', y=0.995)
    plt.tight_layout(rect=[0, 0, 1, 0.99])
    
    output_path = "benchmarks/analysis/size_vs_cont_precision.png"
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    plt.savefig(output_path, bbox_inches='tight', dpi=150)
    print(f"Saved: {output_path}")
    
    plt.show()
    plt.close('all')

def print_top_programs_by_size(all_results, top_n=10):
    """Print the top N programs by size (0CFA configurations visited)."""
    
    # Get program sizes from KCFA 0-0 baseline
    program_sizes = {}
    for r in all_results:
        if r['variant'] == 'kcfa' and str(r['d']) == '0' and str(r['m']) == '0':
            bench = r['benchmarkName']
            # Filter out benchmarks/suite programs (smallest benchmarks)
            if '/suite/' in bench:
                continue
            if r.get('storeMetrics'):
                m = r['storeMetrics']
                total_states = m.get('numTotalFixInputStates', 0)
                store_addrs = m.get('numStoreAddresses', 0)
                configs_visited = total_states - store_addrs
                if configs_visited > 0:
                    program_sizes[bench] = configs_visited
    
    if not program_sizes:
        print("No program size data found.")
        return
    
    # Sort by size descending and get top N
    sorted_programs = sorted(program_sizes.items(), key=lambda x: x[1], reverse=True)
    
    print(f"\nTop {top_n} Programs by Size (0CFA Configurations Visited):")
    print("-" * 70)
    for i, (benchmark, size) in enumerate(sorted_programs[:top_n], 1):
        print(f"{i:2d}. {benchmark:50s} {size:10,d}")
    print("-" * 70)

def main():
    results_path = "benchmarks/results"
    if not os.path.exists(results_path):
        print(f"Error: Path '{results_path}' does not exist.")
        return

    all_results = load_hierarchical_data(results_path)
    if not all_results:
        print("Error: No data found in benchmarks/results.")
        return
    
    # Print top 10 programs by size
    print_top_programs_by_size(all_results, top_n=10)
    
    # Generate size vs time comparison plot (min_size=100 to filter small programs)
    plot_size_vs_time_comparison(all_results, min_size=350)
    
    # Generate size vs continuation precision plot (min_size=100 to filter small programs)
    plot_size_vs_cont_precision(all_results, min_size=350)
    
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