import os
import json
import pandas as pd
import numpy as np
import seaborn as sns
import matplotlib.pyplot as plt
import matplotlib.ticker as mtick

# --- Reusing Metric Logic from new_analysis.py ---

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
        if base_sz == -1: base_sz = float('inf')
        elif base_sz == 0: continue
             
        if x_id not in poly_map:
            hits += 1
            total_valid += 1
            continue
            
        poly_sz = poly_map.get(x_id)
        if poly_sz == -1: poly_sz = float('inf')
        
        if poly_sz < base_sz:
            hits += 1
            
        total_valid += 1
            
    return hits / total_valid if total_valid > 0 else 0.0

def calc_absolute_precision(metric, run_data, baseline_run_data):
    """Calculates absolute precision: fraction of baseline keys that are precise (size 1) in EITHER baseline OR poly, or improved to dead."""
    m = run_data.get(metric)
    if not baseline_run_data:
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
        
        if x_id not in m:
            hits += 1
            continue
            
        poly_sz = m.get(x_id)
        if poly_sz == -1: poly_sz = float('inf')
        if base_sz == -1: base_sz = float('inf')
        
        if poly_sz == 1 or base_sz == 1:
            hits += 1
            
    return hits / total if total > 0 else 0.0

def compute_metrics(run, baseline_run):
    """Computes relative precision metrics."""
    # Use storeMetrics directly as in new_analysis.py
    m = run.get('storeMetrics', {})
    baseline = baseline_run.get('storeMetrics', {}) if baseline_run else {}
    
    metrics = {
        "time": np.mean(run.get('analysisTimes', [0])),
        "states": m.get('numTotalFixInputStates', 0), # Total state space size (including store)
        "prec_struct": calc_prod('storeToStrSizes', m, baseline),
        "prec_struct_abs": calc_absolute_precision('storeToStrSizes', m, baseline),
        "prec_struct_gain": calc_prod('storeToStrSizes', m, baseline), 
        "prec_cont_struct": calc_prod('structToContStrSizes', m, baseline),
        "prec_cont_struct_gain": calc_prod('structToContStrSizes', m, baseline), 
        "prec_cont_struct_abs": calc_absolute_precision('structToContStrSizes', m, baseline),
        "prec_lit": (m.get('numLitAddresses', 1) - m.get('literalTopCount', 0)) / m.get('numLitAddresses', 1) if m.get('numLitAddresses', 0) > 0 else 1.0,
        "prec_lit_gain": ((m.get('numLitAddresses', 1) - m.get('literalTopCount', 0)) / m.get('numLitAddresses', 1)) - ((baseline.get('numLitAddresses', 1) - baseline.get('literalTopCount', 0)) / baseline.get('numLitAddresses', 1)),
        "calc_prod": calc_prod('exprToValSemSizes', m, baseline), 
    }
    return metrics

def categorize_benchmark(bench_name):
    if "interp" in bench_name or "mini-ppl" in bench_name or "koka-gen" in bench_name:
        return "Generated"
    elif "rosetta" in bench_name or "handlers" in bench_name:
        return "Mid-sized (Programs)"
    else:
        return "Micro (Suite)"

def load_all_results(results_dir="benchmarks/results"):
    data = []
    all_results = []
    baselines = {} # Map 'benchmark_name' -> result dict (for 0-CFA)

    # Pass 1: Load everything
    for root, _, files in os.walk(results_dir):
        for file in files:
            if file.endswith(".json"):
                 try:
                    with open(os.path.join(root, file), 'r') as f:
                        res = json.load(f)
                        if not res.get('benchmarkName'): continue
                        all_results.append(res)
                        
                        # Identify baseline
                        variant = res.get('variant', 'unknown')
                        m = res.get('m', 0)
                        
                        if variant == 'kcfa' and m == 0:
                            baselines[res.get('benchmarkName')] = res
                 except: pass

    print(f"DEBUG: Found {len(all_results)} total result files.")
    print(f"DEBUG: Found {len(baselines)} baselines.")

    # Pass 2: Calculate metrics
    for res in all_results:
        try:
            bench = res.get('benchmarkName', '')
            variant = res.get('variant', 'unknown')
            
            m = res.get('m', 0)
            d = res.get('d', 0)
            
            baseline = baselines.get(bench)
            
            # If no baseline, skip relative metrics (and absolute precision if it depends on baseline)
            # Actually, calculate what we can.
            if not baseline: 
                continue
            
            metrics = compute_metrics(res, baseline)
            metrics['Benchmark'] = bench
            metrics['Variant'] = variant
            metrics['k'] = m
            metrics['m'] = m
            metrics['d'] = d
            metrics['Category'] = categorize_benchmark(bench)
            metrics['IsTimeout'] = metrics['time'] >= 60.0
            
            # Label
            if variant == 'kcfa':
                label = f"k-CFA k={m}"
            else:
                label = f"{variant.upper()} ({m},{d})"
            metrics['Label'] = label
            metrics['AnalysisFamily'] = 'k-CFA' if variant == 'kcfa' else 'DMCFAR/E'
            
            data.append(metrics)
        except Exception as e:
            pass
            
    return pd.DataFrame(data)

def analyze_cost():
    df = load_all_results()
    if df.empty:
        print("No data found.")
        return

    # Filter out Micro benchmarks for this analysis (too fast/precise to show interesting cost tradeoffs)
    df = df[df['Category'] != 'Micro (Suite)']
    
    # Filter out Timeouts for Pareto analysis (Time needs to be valid)
    df_valid = df[~df['IsTimeout']]
    
    # Add Complexity Level for visualization
    # KCFA: Level = k
    # DMCFA: Level = m (assuming m is the dominant factor comparable to k)
    def get_level(row):
        val = row['m']
        return f"k/m={val}"
            
    df_valid['ComplexityLevel'] = df_valid.apply(get_level, axis=1)
    
    print(f"Loaded {len(df_valid)} valid runs for Cost Analysis.")
    if not df_valid.empty:
       print("Complexity Levels:", sorted(df_valid['ComplexityLevel'].unique()))

    # Consistent plotting settings
    unique_levels = sorted(df_valid['ComplexityLevel'].unique(), key=lambda x: int(x.split('=')[1]))
    marker_list = ['o', 'X', 's', '^', 'D', 'v', '*', 'p']
    markers = {lvl: marker_list[i % len(marker_list)] for i, lvl in enumerate(unique_levels)}
    hue_order = ['k-CFA', 'DMCFAR/E']
    
    def plot_scatter(x_metric, y_metric, filename, title, x_label, y_label):
        plt.figure(figsize=(12, 8))
        sns.scatterplot(
            data=df_valid, 
            x=x_metric, 
            y=y_metric, 
            hue='AnalysisFamily', 
            style='ComplexityLevel',
            size='ComplexityLevel',
            sizes=(50, 200),
            palette={'k-CFA': 'tab:blue', 'DMCFAR/E': 'tab:red'},
            markers=markers,
            hue_order=hue_order,
            style_order=unique_levels,
            size_order=unique_levels,
            alpha=0.7
        )
        plt.yscale('log')
        plt.xlabel(x_label)
        plt.ylabel(y_label)
        plt.title(title)
        plt.grid(True, which="both", ls="--", alpha=0.3)
        plt.legend(bbox_to_anchor=(1.05, 1), loc='upper left', borderaxespad=0.)
        plt.gca().xaxis.set_major_formatter(mtick.PercentFormatter(1.0))
        plt.tight_layout()
        plt.savefig(filename)
        print(f"Saved {filename}")

    plot_scatter('prec_cont_struct_abs', 'time', 'benchmarks/new_analysis/cost_precision_time.png', 
                 "Cost of Precision: Time vs Continuation Accuracy (Color=Family, Shape/Size=k/m)", 
                 "Absolute Continuation Precision", "Analysis Time (s) [Log Scale]")

    plot_scatter('prec_cont_struct_abs', 'states', 'benchmarks/new_analysis/cost_precision_states.png', 
                 "Cost of Precision: States vs Continuation Accuracy (Color=Family, Shape/Size=k/m)", 
                 "Absolute Continuation Precision", "State Space Size [Log Scale]")

    plot_scatter('prec_struct_abs', 'time', 'benchmarks/new_analysis/cost_value_precision_time.png', 
                 "Cost of Precision: Time vs Value Accuracy (Color=Family, Shape/Size=k/m)", 
                 "Absolute Value Precision", "Analysis Time (s) [Log Scale]")

    plot_scatter('prec_struct_abs', 'states', 'benchmarks/new_analysis/cost_value_precision_states.png', 
                 "Cost of Precision: States vs Value Accuracy (Color=Family, Shape/Size=k/m)", 
                 "Absolute Value Precision", "State Space Size [Log Scale]")
    
    # --- Analysis: Cheapest Configuration for Target ---
    targets = [0.90, 0.95, 0.99, 1.00]
    
    def analyze_cheapest(metric_key, metric_name, cost_key='time', cost_name='Time'):
        results = []
        print(f"\n## Cheapest Analysis for Target Precision ({metric_name}) - Best {cost_name}")
        
        for bench_name, group in df_valid.groupby('Benchmark'):
            for t in targets:
                passed = group[group[metric_key] >= t]
                if passed.empty:
                    pass
                else:
                    best = passed.nsmallest(1, cost_key).iloc[0]
                    results.append({
                        'Benchmark': bench_name,
                        'Target': t,
                        'CheapestVariant': best['Label'],
                        'Time': best['time'],
                        'States': best['states'],
                        'Family': best['AnalysisFamily']
                    })
        
        summary_df = pd.DataFrame(results)
        if summary_df.empty:
            print("No benchmarks met any target precision.")
            return

        stats = []
        for t in targets:
            subset = summary_df[summary_df['Target'] == t]
            family_counts = subset['Family'].value_counts()
            
            row = {'Target Precision': f"{t*100:.0f}%", 'Solved Cases': len(subset)}
            row['DMCFAR/E Wins'] = family_counts.get('DMCFAR/E', 0)
            row['k-CFA Wins'] = family_counts.get('k-CFA', 0)
            
            stats.append(row)
            
        stats_df = pd.DataFrame(stats)
        print(stats_df.to_markdown(index=False))

    # Time-based Cheapest
    analyze_cheapest('prec_cont_struct_abs', 'Continuation', 'time', 'Time')
    analyze_cheapest('prec_struct_abs', 'Value', 'time', 'Time')

    # State-based Cheapest
    analyze_cheapest('prec_cont_struct_abs', 'Continuation', 'states', 'States')
    analyze_cheapest('prec_struct_abs', 'Value', 'states', 'States')

if __name__ == "__main__":
    analyze_cost()
