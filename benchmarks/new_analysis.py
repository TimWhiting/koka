
import json
import os
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns

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
    """Calculates productivity metric: fraction of precise value sets that were imprecise in baseline."""
    poly_map = poly.get(metric)
    base_map = base.get(metric)
    
    if not base_map or not poly_map:
        return np.nan
        
    hits = 0
    total_valid = 0
    
    for x_id, base_vals in base_map.items():
        if x_id not in poly_map:
            continue # Variable optimized away or dead code?
            
        if isinstance(base_vals, list):
             base_sz_list = [v for v in base_vals if v != -1]
        else:
             base_sz_list = [base_vals] if base_vals != -1 else []
        if not base_sz_list:
            continue # Baseline was purely Top or empty
            
        base_min = min(base_sz_list)
        
        # If baseline is already singleton (size 1), no room for improvement
        # Unless we want to count preserving precision? Usually productivity is about *increasing* precision.
        # But for now let's stick to the definition: "more precise than baseline"
        # Actually, let's just check if we are smaller than baseline's smallest set
        
        poly_sz = poly_map.get(x_id)
        if poly_sz is None:
            continue
            
        total_valid += 1
        
        # If poly size is smaller than base min (and not Top), it's an improvement
        # Note: poly_sz is a single integer (size), base_vals is list of sizes (due to context insensitivity merging)
        if poly_sz != -1 and poly_sz < base_min:
            hits += 1
            
    return hits / total_valid if total_valid > 0 else 0.0

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
        "time": np.mean(run.get('analysisTimes', [0])),
        "prec_struct": calc_prod('storeToStrSizes', m, baseline),
        "prec_lit": (m.get('numLitAddresses', 1) - m.get('literalTopCount', 0)) / m.get('numLitAddresses', 1) if m.get('numLitAddresses', 0) > 0 else 1.0,
        "prec_lit_gain": ((m.get('numLitAddresses', 1) - m.get('literalTopCount', 0)) / m.get('numLitAddresses', 1)) - ((baseline.get('numLitAddresses', 1) - baseline.get('literalTopCount', 0)) / baseline.get('numLitAddresses', 1)),
        "calc_prod": calc_prod('exprToValSemSizes', m, baseline), # "Productivity" usually refers to values
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
    for run in all_data:
        if str(run['d']) == '0' and str(run['m']) == '0':
            key = (run['variant'], run['benchmarkName'])
            baselines[key] = run
            
    # 2. Second pass: Compute metrics
    for run in all_data:
        variant = run['variant']
        bench_name = run['benchmarkName']
        
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
    
    for group_name, configs in plot_configs:
        fig, axes = plt.subplots(1, len(configs), figsize=(6 * len(configs), 5), sharey=True)
        if len(configs) == 1: axes = [axes]
        
        for ax, (var, m_val, d_val) in zip(axes, configs):
            if var == 'kcfa':
                data = df[(df['Variant'] == var) & (df['m'] == m_val) & (~df['IsTimeout']) & (df['prec_struct'].notna())]
                title = f"k-CFA k={m_val}"
            else:
                data = df[(df['Variant'] == var) & (df['m'] == m_val) & (df['d'] == d_val) & (~df['IsTimeout']) & (df['prec_struct'].notna())]
                title = f"{var.upper()} ({d_val},{m_val})"
            
            if data.empty:
                continue
                
            sns.scatterplot(
                data=data, 
                x='size_0cfa', 
                y='prec_struct', 
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
            ax.set_ylabel('Structural Precision Improvement')
            ax.set_ylim(-0.05, 1.05) # Metric is 0.0 to 1.0
            
        plt.suptitle(f'Precision Improvement vs Size ({group_name})', y=1.05)
        plt.tight_layout()
        plt.savefig(os.path.join(output_dir, f'scatter_precision_{group_name.replace(" ", "_")}.png'))
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
                'Median Prec Struct': solved['prec_struct'].median() if not solved.empty else np.nan,
                'Median Prec Lit Gain': solved['prec_lit_gain'].median() if not solved.empty else np.nan,
                'Max Prec Struct': solved['prec_struct'].max() if not solved.empty else np.nan
            })
            
    summary_df = pd.DataFrame(summary_rows)
    summary_df = summary_df.sort_values(['Category', 'Configuration'])
    
    print("\n## Stratified Results Summary")
    print(summary_df.to_markdown(index=False, floatfmt=".3f"))
    
    # Save to CSV
    summary_df.to_csv(os.path.join(output_dir, 'summary_table.csv'), index=False)

if __name__ == "__main__":
    analyze_benchmarks()
