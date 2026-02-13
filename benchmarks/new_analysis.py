
import json
import os
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns
from matplotlib.ticker import PercentFormatter

# Set style for publication-quality plots
sns.set_theme(style="whitegrid", context="paper", font_scale=1.2)

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
                    # Skip empty files
                    if os.path.getsize(file_path) == 0:
                        continue
                        
                    with open(file_path, 'r') as f:
                        try:
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

def categorize_benchmark(bench_name):
    """Categorizes benchmarks into Micro, Mid-sized, and Generated."""
    if 'koka-gen' in bench_name:
        return 'Generated'
    elif 'suite' in bench_name:
        return 'Micro (Suite)'
    elif 'rosetta' in bench_name or 'handlers' in bench_name:
        return 'Mid-sized (Programs)'
    else:
        return 'Other'

def calc_prod(metric, poly, base):
    """Calculates productivity: fraction of base keys that are improved in poly."""
    poly_map = poly.get(metric)
    base_map = base.get(metric)
    
    if not base_map or not poly_map:
        return np.nan
        
    hits = 0
    total_valid = 0
    
    for x_id, base_val in base_map.items():
        base_sz = base_val
        if base_sz == -1: # Top in baseline? Assume imprecise.
            # If base is Top, any non-Top poly is improvement?
            # Or just skip? User said "value smaller than the base is also improvement".
            # Let's assume -1 means "infinity" or "Top".
            base_sz = float('inf')
        elif base_sz == 0:
             continue # Empty?
             
        # Definition: "fraction of precise value sets that were imprecise in baseline"
        # No, user said: "intent ... is to count improvement"
        # 1. Key missing in poly = improvement (dead code)
        if x_id not in poly_map:
            hits += 1
            total_valid += 1
            continue
            
        poly_sz = poly_map.get(x_id)
        if poly_sz == -1: poly_sz = float('inf')
        
        # 2. Value smaller than base
        if poly_sz < base_sz:
            hits += 1
            
        total_valid += 1
            
    return hits / total_valid if total_valid > 0 else 0.0

def calc_absolute_precision(metric, run_data, baseline_run_data):
    """Calculates absolute precision: fraction of baseline keys that are precise (size 1) in EITHER baseline OR poly, or improved to dead."""
    m = run_data.get(metric)
    if not baseline_run_data:
        base_map = None # Should not happen based on user request "Do not have a fallback" 
        # But if passed None, we return NaN
        return np.nan
    else:
        base_map = baseline_run_data.get(metric)
    
    if not m or not base_map:
        return np.nan
        
    hits = 0
    total = 0
    
    for x_id, base_val in base_map.items():
        base_sz = base_val
        if base_sz == 0: continue
        
        total += 1
        
        # Case 1: Missing in poly (Dead code) -> Precise
        if x_id not in m:
            hits += 1
            continue
            
        poly_sz = m.get(x_id)
        if poly_sz == -1: poly_sz = float('inf')
        if base_sz == -1: base_sz = float('inf')
        
        # Case 2: Size 1 in EITHER poly OR baseline -> Precise
        # User: "if it is size == 1 in either poly or baseline that is precise"
        if poly_sz == 1 or base_sz == 1:
            hits += 1
            
    return hits / total if total > 0 else 0.0

def compute_metrics(run, baseline_run):
    """Computes relative precision metrics."""
    if run.get('isTimeout') or not run.get('storeMetrics'):
        return None

    m = run['storeMetrics']
    baseline = baseline_run.get('storeMetrics')
    
    if not baseline:
        return None
    
    # Relative Structural Precision (Singleton Ratio Improvement)
    # How many more singletons do we have relative to baseline?
    # Or just raw singleton ratio? Let's use the one from analyze.py
    # But user wants "prec_struct" as defined in analyze.py
    
    # In analyze.py: 
    # prec_struct = calc_prod('storeToStrSizes', m, baseline)
    
    metrics = {
        "prec_struct": calc_prod('storeToStrSizes', m, baseline),
        "prec_struct_abs": calc_absolute_precision('storeToStrSizes', m, baseline),
        "prec_struct_gain": calc_prod('storeToStrSizes', m, baseline), # Alias for clarity
        "prec_cont_struct": calc_prod('structToContStrSizes', m, baseline),
        "prec_cont_struct_gain": calc_prod('structToContStrSizes', m, baseline), # Alias
        "prec_cont_struct_abs": calc_absolute_precision('structToContStrSizes', m, baseline),
        "prec_lit": (m.get('numLitAddresses', 1) - m.get('literalTopCount', 0)) / m.get('numLitAddresses', 1) if m.get('numLitAddresses', 0) > 0 else 1.0,
        "prec_lit_gain": ((m.get('numLitAddresses', 1) - m.get('literalTopCount', 0)) / m.get('numLitAddresses', 1)) - ((baseline.get('numLitAddresses', 1) - baseline.get('literalTopCount', 0)) / baseline.get('numLitAddresses', 1)),
        "calc_prod": calc_prod('exprToValSemSizes', m, baseline), 
        "size_0cfa": baseline.get('numTotalFixpointStates', 0)
    }
    return metrics

def analyze_benchmarks():
    results_path = "benchmarks/results"
    output_dir = "benchmarks/new_analysis"
    os.makedirs(output_dir, exist_ok=True)
    
    all_data = load_hierarchical_data(results_path)
    if not all_data:
        print("No data found.")
        return

    # Group by variant (kcfa, dmcfar, dmcfae)
    # We need to find the specific baseline (d=0, m=0) for each benchmark *per variant* 
    # (though usually 0CFA is the same for all, let's be safe and use the variant's own 0-0)
    
    processed_rows = []
    
    # 1. First pass: Index baselines
    baselines = {} # (variant, benchmarkName) -> run_data
    # We specifically need checking if 0CFA finished for filtering
    baseline_timeouts = {} # benchmarkName -> bool
    
    for run in all_data:
        if str(run['d']) == '0' and str(run['m']) == '0':
            key = (run['variant'], run['benchmarkName'])
            baselines[key] = run
            # Check timeout for filtering. 
            # We assume if ANY variant's 0CFA timed out, we should ignore the benchmark?
            # Or just if the specific variant's 0CFA timed out?
            # User said "omit results from all configurations where 0CFA didn't finish".
            # Usually we use k-CFA k=0 as the canonical "0CFA".
            if run['variant'] == 'kcfa':
                 baseline_timeouts[run['benchmarkName']] = run.get('isTimeout', False)

    # 2. Second pass: Compute metrics
    for run in all_data:
        variant = run['variant']
        bench_name = run['benchmarkName']
        
        # Filter if 0CFA timed out
        if baseline_timeouts.get(bench_name, False):
            continue
        
        # Skip if no baseline
        base_run = baselines.get((variant, bench_name))
        # If not finding specific variant baseline, try fallback to KCFA 0-0 (true 0CFA)
        if not base_run:
            base_run = baselines.get(('kcfa', bench_name))
            
        if not base_run:
            continue
            
        metrics = compute_metrics(run, base_run)
        
        category = categorize_benchmark(bench_name)
        
        row = {
            'Variant': variant,
            'Benchmark': bench_name,
            'Category': category,
            'd': str(run['d']),
            'm': str(run['m']),
            'Config': f"{variant} (d={run['d']}, m={run['m']})" if variant != 'kcfa' else f"k-CFA (k={run['m']})",
            'IsTimeout': run.get('isTimeout', False),
            'Time': np.mean(run.get('analysisTimes', [600])) if not run.get('isTimeout') else 600,
        }
        
        if metrics:
            row.update(metrics)
        else:
            # Propagate 0CFA size even if this run failed/timed out
            row['size_0cfa'] = base_run['storeMetrics'].get('numTotalFixpointStates', 0) if base_run.get('storeMetrics') else 0
            
        processed_rows.append(row)
        
    df = pd.DataFrame(processed_rows)
    df['d'] = pd.to_numeric(df['d'])
    df['m'] = pd.to_numeric(df['m'])
    
    # --- Visualizations ---
    
    # 1. Scalability: Cactus Plot
    # X-axis: Number of benches solved <= T
    # Y-axis: Time T
    plt.figure(figsize=(10, 6))
    
    # Select key configurations to plot
    key_configs = [
        ('kcfa', 1, 0, 'k-CFA k=1'),
        ('kcfa', 2, 0, 'k-CFA k=2'),
        ('dmcfar', 1, 1, 'DMCFAR (1,1)'),
        ('dmcfar', 2, 2, 'DMCFAR (2,2)'),
        ('dmcfae', 1, 1, 'DMCFAE (1,1)'),
    ]
    
    for variant, m_val, d_val, label in key_configs:
        # Filter data
        if variant == 'kcfa':
            subset = df[(df['Variant'] == variant) & (df['m'] == m_val)]
        else:
            subset = df[(df['Variant'] == variant) & (df['m'] == m_val) & (df['d'] == d_val)]
            
        # Get times for solved instances
        times = sorted([t for t, is_to in zip(subset['Time'], subset['IsTimeout']) if not is_to])
        # X-axis is just 1..N
        x_axis = range(1, len(times) + 1)
        
        if times:
            plt.plot(x_axis, times, label=f"{label} ({len(times)} solved)", linewidth=2, marker='o', markersize=4, alpha=0.8)
            
    plt.yscale('log')
    plt.xlabel('Number of Benchmarks Solved')
    plt.ylabel('Analysis Time (s) [Log Scale]')
    plt.title('Scalability (Cactus Plot)')
    plt.legend()
    plt.grid(True, which="both", ls="-", alpha=0.2)
    plt.tight_layout()
    plt.savefig(os.path.join(output_dir, 'cactus_plot.png'))
    plt.close()
    
    # 2. Precision Scatter Plot
    # Faceted by Configuration, colored by Category
    # X: Size (0CFA), Y: prec_struct
    
    plot_configs = [
        ('1,1 vs k=1', [
            ('kcfa', 1, 0),
            ('dmcfar', 1, 1),
            ('dmcfae', 1, 1)
        ]),
        ('2,2 vs k=2', [
            ('kcfa', 2, 0),
            ('dmcfar', 2, 2)
        ])
    ]
    
    # 4 Variations of scatter plots
    # (Name, Metric Key, Y-Limit, Absolute Metric Key for Filtering)
    metrics_to_plot = [
        ('Absolute Continuation Precision', 'prec_cont_struct_abs', (0.5, 1.05), None),
        ('Absolute Value Precision', 'prec_struct_abs', (0.0, 1.05), None),
        ('Continuation Precision Improvement', 'prec_cont_struct_gain', (-0.02, 0.22), 'prec_cont_struct_abs'),
        ('Value Precision Improvement', 'prec_struct_gain', (-0.02, 0.22), 'prec_struct_abs')
    ]

    for metric_name, metric_key, ylim, filter_abs_key in metrics_to_plot:
        for group_name, configs in plot_configs:
            
            # If filtering is enabled, identify benchmarks effectively perfect in ALL configs of this group
            exclude_benches = set()
            if filter_abs_key:
                # 1. Collect all benchmarks for this group
                # We need to check if *every* variant in the group has near 1.0 precision
                # This is tricky because data is in rows.
                # Let's count how many variants have prec=1.0 per benchmark
                
                # First, extract relevant rows for this group
                group_data = pd.DataFrame()
                for var, m_val, d_val in configs:
                    if var == 'kcfa':
                         subset = df[(df['Variant'] == var) & (df['m'] == m_val)]
                    else:
                         subset = df[(df['Variant'] == var) & (df['m'] == m_val) & (df['d'] == d_val)]
                    subset = subset[subset['Category'] != 'Micro (Suite)'] # We exclude micro anyway
                    group_data = pd.concat([group_data, subset])
                
                if not group_data.empty:
                    # Pivot to see precision per benchmark per config
                    # We want benchmarks where ALL present configs have prec >= 0.999
                    # Note: Need to handle benchmarks that might rely on 0CFA baseline causing NaN? 
                    # If prec_abs is NaN, it's not 1.0.
                    
                    # Group by Benchmark and check min(prec_abs)
                    # But we only care about the configs IN THIS GROUP
                    # So for each benchmark, count how many configs are present
                    # And count how many have prec >= 0.999
                    
                    # This implies we only filter if ALL configs in the group are present AND precise?
                    # Or just: for all configs *available* for this benchmark in this group, are they all precise?
                    # User said "filters out any that are fully precise in both [all analyses in graph]".
                    
                    grouped = group_data.groupby('Benchmark')[filter_abs_key].min()
                    # If min precision across all variants is 1.0, then all are 1.0.
                    exclude_benches = set(grouped[grouped >= 0.9999].index)
            
    for metric_name, metric_key, ylim, filter_abs_key in metrics_to_plot:
        for group_name, configs in plot_configs:
            
            # If filtering is enabled... (omitted for brevity, keep existing logic)
            # ...
            
            # Use sharex=True to ensure X-axis scale matches across subplots
            fig, axes = plt.subplots(1, len(configs), figsize=(6 * len(configs), 5), sharey=True, sharex=True)
            if len(configs) == 1: axes = [axes]
            
            points_plotted = False
            
            for ax, (var, m_val, d_val) in zip(axes, configs):
                if var == 'kcfa':
                    data = df[(df['Variant'] == var) & (df['m'] == m_val) & (~df['IsTimeout']) & (df[metric_key].notna())]
                    title = f"k-CFA k={m_val}"
                else:
                    data = df[(df['Variant'] == var) & (df['m'] == m_val) & (df['d'] == d_val) & (~df['IsTimeout']) & (df[metric_key].notna())]
                    title = f"{var.upper()} ({d_val},{m_val})"
                
                if data.empty:
                    continue

                # Filter out Micro benchmarks for scatter plot
                data = data[data['Category'] != 'Micro (Suite)']
                
                # Filter out fully precise if requested
                if filter_abs_key:
                    data = data[~data['Benchmark'].isin(exclude_benches)]
                    
                if data.empty: continue
                
                points_plotted = True
                    
                sns.scatterplot(
                    data=data, 
                    x='size_0cfa', 
                    y=metric_key, 
                    hue='Category',
                    style='Category',
                    palette='deep',
                    s=100,
                    alpha=0.8,
                    ax=ax
                )
                
                ax.set_xscale('log')
                ax.set_title(title)
                ax.set_xlabel('Program Size (0CFA States)')
                ax.set_ylabel(metric_name)
                ax.set_ylim(ylim) 
                # Only use PercentFormatter for Improvement if it makes sense, or Absolute?
                # Usually for both 0.0-1.0 and -0.1-0.2 it makes sense.
                try:
                    ax.yaxis.set_major_formatter(PercentFormatter(1.0))
                except:
                    pass
            
            if not points_plotted:
                plt.close()
                continue
                
            plt.suptitle(f'{metric_name} vs Size ({group_name})', y=1.05)
            plt.tight_layout()
            safe_metric_name = metric_name.lower().replace(' ', '_')
            group_suffix = group_name.replace(" ", "_")
            plt.savefig(os.path.join(output_dir, f'scatter_{safe_metric_name}_{group_suffix}.png'))
            plt.close()

    # 3. Summary Tables
    # Aggregated by Category and Configuration
    # Columns: Config, Category, Count, Solved, Median Time, Median Prec Struct
    
    # Define interesting configs
    # Define interesting configs
    interesting = [
        ('kcfa', 0, 0), ('kcfa', 1, 0), ('kcfa', 2, 0),
        ('dmcfar', 1, 1), ('dmcfar', 2, 2),
        ('dmcfae', 1, 1), ('dmcfae', 2, 2)
    ]
    
    summary_rows = []
    for var, m_val, d_val in interesting:
        if var == 'kcfa':
            subset = df[(df['Variant'] == var) & (df['m'] == m_val)]
            cfg_name = f"k-CFA k={m_val}"
        else:
            subset = df[(df['Variant'] == var) & (df['m'] == m_val) & (df['d'] == d_val)]
            cfg_name = f"{var.upper()} ({d_val},{m_val})"
            
        # Group by category
        for cat in df['Category'].unique():
            cat_data = subset[subset['Category'] == cat]
            if cat_data.empty: continue
            
            solved = cat_data[~cat_data['IsTimeout']]
            
            summary_rows.append({
                'Configuration': cfg_name,
                'Category': cat,
                'Total': len(cat_data),
                'Solved': len(solved),
                'Success Rate': f"{len(solved)/len(cat_data):.1%}",
                'Median Time': solved['Time'].median() if not solved.empty else np.nan,
                'Median Prec Struct Gain': solved['prec_struct'].median() if not solved.empty else np.nan,
                'Median Prec Struct Abs': solved['prec_struct_abs'].median() if not solved.empty else np.nan,
                'Median Prec Cont Abs': solved['prec_cont_struct_abs'].median() if not solved.empty else np.nan,
                'Median Prec Lit Gain': solved['prec_lit_gain'].median() if not solved.empty else np.nan,
                'Max Prec Struct Gain': solved['prec_struct'].max() if not solved.empty else np.nan
            })
            
    summary_df = pd.DataFrame(summary_rows)
    summary_df = summary_df.sort_values(['Category', 'Configuration'])
    
    print("\n## Stratified Results Summary")
    print(summary_df.to_markdown(index=False, floatfmt=".3f"))
    
    # Save to CSV
    summary_df.to_csv(os.path.join(output_dir, 'summary_table.csv'), index=False)
    
    # 4. Differences Table
    # Compare DMCFAR (1,1) vs KCFA (1) and (2,2) vs (2)
    # Focus on where they DIFFER in outcome or precision
    
    diff_rows = []
    comparisons = [
        ('DMCFAR 1,1 vs KCFA 1', 'dmcfar', 1, 1, 'kcfa', 1, 0),
        ('DMCFAR 2,2 vs KCFA 2', 'dmcfar', 2, 2, 'kcfa', 2, 0),
        ('DMCFAE 1,1 vs KCFA 1', 'dmcfae', 1, 1, 'kcfa', 1, 0),
        ('DMCFAE 2,2 vs KCFA 2', 'dmcfae', 2, 2, 'kcfa', 2, 0)
    ]
    
    print("\n## Key Differences")
    
    summary_stats = []
    
    for label, var_a, ma, da, var_b, mb, db in comparisons:
        # Get data for both
        df_a = df[(df['Variant'] == var_a) & (df['m'] == ma) & (df['d'] == da)]
        df_b = df[(df['Variant'] == var_b) & (df['m'] == mb)]
        
        # Merge on Benchmark
        merged = pd.merge(df_a, df_b, on='Benchmark', suffixes=('_A', '_B'), how='outer')
        
        metrics_to_track = [
            ('Abs Cont Prec', 'prec_cont_struct_abs_A', 'prec_cont_struct_abs_B'),
            ('Abs Value Prec', 'prec_struct_abs_A', 'prec_struct_abs_B'),
            ('Cont Improv', 'prec_cont_struct_gain_A', 'prec_cont_struct_gain_B'),
            ('Value Improv', 'prec_struct_gain_A', 'prec_struct_gain_B')
        ]
        
        # Store deltas per metric
        metric_deltas = {m[0]: [] for m in metrics_to_track}
        
        success_wins = 0
        success_losses = 0
        
        for _, row in merged.iterrows():
            bench = row['Benchmark']
            cat = categorize_benchmark(bench)
            if cat == 'Micro (Suite)': continue 
            
            # Check for Success/Fail diff
            succ_a = not row['IsTimeout_A'] if pd.notna(row['IsTimeout_A']) else False
            succ_b = not row['IsTimeout_B'] if pd.notna(row['IsTimeout_B']) else False
            
            if succ_a != succ_b:
                if succ_a: 
                    success_wins += 1 
                else: 
                    success_losses += 1
                
                diff_rows.append({
                    'Comparison': label,
                    'Benchmark': bench,
                    'Category': cat,
                    'Difference Type': 'Success/Fail',
                    'DMCFAR Detail': 'Success' if succ_a else 'Timeout',
                    'KCFA Detail': 'Success' if succ_b else 'Timeout',
                    'Delta': np.nan
                })
                continue
                
            if not succ_a: continue # Both timed out
            
            # Collect Deltas for each metric
            for m_label, col_a, col_b in metrics_to_track:
                val_a = row[col_a]
                val_b = row[col_b]
                
                if pd.notna(val_a) and pd.notna(val_b):
                    delta = val_a - val_b
                    # Store significant deltas for stats? Or all deltas?
                    # User asked for "Win Percentage" and "Loss Percentage".
                    # Win = delta > 0.001?
                    if abs(delta) > 0.001:
                        metric_deltas[m_label].append(delta)

            # Add diff rows (as before, just repeating logic or using loop?)
            # Reusing the loop logic for adding to Diff Table
            p_cont_a = row['prec_cont_struct_abs_A']
            p_cont_b = row['prec_cont_struct_abs_B']
            if pd.notna(p_cont_a) and pd.notna(p_cont_b) and abs(p_cont_a - p_cont_b) > 0.001:
                diff_rows.append({
                    'Comparison': label,
                    'Benchmark': bench,
                    'Category': cat,
                    'Difference Type': 'Abs Cont Prec',
                    'DMCFAR Detail': f"{p_cont_a:.3f}",
                    'KCFA Detail': f"{p_cont_b:.3f}",
                    'Delta': p_cont_a - p_cont_b
                })
            
            g_cont_a = row['prec_cont_struct_gain_A']
            g_cont_b = row['prec_cont_struct_gain_B']
            if pd.notna(g_cont_a) and pd.notna(g_cont_b) and abs(g_cont_a - g_cont_b) > 0.001:
                diff_rows.append({
                    'Comparison': label,
                    'Benchmark': bench,
                    'Category': cat,
                    'Difference Type': 'Cont Improv',
                    'DMCFAR Detail': f"{g_cont_a:.3f}",
                    'KCFA Detail': f"{g_cont_b:.3f}",
                    'Delta': g_cont_a - g_cont_b
                })

            p_val_a = row['prec_struct_abs_A']
            p_val_b = row['prec_struct_abs_B']
            if pd.notna(p_val_a) and pd.notna(p_val_b) and abs(p_val_a - p_val_b) > 0.001:
                diff_rows.append({
                    'Comparison': label,
                    'Benchmark': bench,
                    'Category': cat,
                    'Difference Type': 'Abs Value Prec',
                    'DMCFAR Detail': f"{p_val_a:.3f}",
                    'KCFA Detail': f"{p_val_b:.3f}",
                    'Delta': p_val_a - p_val_b
                })

            g_val_a = row['prec_struct_gain_A']
            g_val_b = row['prec_struct_gain_B']
            if pd.notna(g_val_a) and pd.notna(g_val_b) and abs(g_val_a - g_val_b) > 0.001:
                diff_rows.append({
                    'Comparison': label,
                    'Benchmark': bench,
                    'Category': cat,
                    'Difference Type': 'Value Improv',
                    'DMCFAR Detail': f"{g_val_a:.3f}",
                    'KCFA Detail': f"{g_val_b:.3f}",
                    'Delta': g_val_a - g_val_b
                })
        
        # Aggregate Stats per Metric
        # Add Success/Fail row first
        summary_stats.append({
            'Comparison': label,
            'Metric': 'Success/Fail',
            'Wins': success_wins,
            'Losses': success_losses,
            'Avg Win %': '-',
            'Avg Loss %': '-'
        })
        
        for m_label in ['Abs Cont Prec', 'Abs Value Prec', 'Cont Improv', 'Value Improv']:
            deltas = metric_deltas[m_label]
            wins = [d for d in deltas if d > 0]
            losses = [d for d in deltas if d < 0]
            
            avg_win = (sum(wins) / len(wins)) * 100 if wins else 0.0
            avg_loss = (sum(losses) / len(losses)) * 100 if losses else 0.0
            
            summary_stats.append({
                'Comparison': label,
                'Metric': m_label,
                'Wins': len(wins),
                'Losses': len(losses),
                'Avg Win %': f"+{avg_win:.1f}%",
                'Avg Loss %': f"{avg_loss:.1f}%"
            })

                
    diff_df = pd.DataFrame(diff_rows)
    if not diff_df.empty:
        # Sort by Comparison, Difference Type, then Delta (descending)
        diff_df = diff_df.sort_values(['Comparison', 'Difference Type', 'Delta'], ascending=[True, True, False])
        diff_df.to_csv(os.path.join(output_dir, 'differences.csv'), index=False)
        # print(diff_df.to_markdown(index=False)) # Use summary stats instead of printing massive table
    
    print("\n## Win/Loss Summary")
    summary_df = pd.DataFrame(summary_stats)
    print(summary_df.to_markdown(index=False))
    summary_df.to_csv(os.path.join(output_dir, 'differences_summary.csv'), index=False)

if __name__ == "__main__":
    analyze_benchmarks()
