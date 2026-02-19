
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, get_benchmark_category, geometric_mean, shifted_geometric_mean

def generate_markdown():
    print("Loading all results...")
    results = load_results_with_baselines("benchmarks/results-cached")
    df = pd.DataFrame(results)

    # 1. Identify Configurations
    # Group by variant, d, m to see what exists
    # Filter out invalid or failed runs, but KEEP timeouts
    # We check if AbsContPrecision exists OR status is T/O
    valid_df = df.copy()
    if 'status' not in valid_df.columns:
        valid_df['status'] = 'OK' # Default
        
    # Filter out invalid or failed runs, but KEEP timeouts
    # We check if 'prec_cont_rir_strict' OR 'prec_cont_real' exists OR status is T/O
    # Note: 'prec_cont_real' is absolute precision relative to 0CFA base addresses, so it should exist if 0CFA exists
    valid_df = valid_df[valid_df['prec_cont_rir_strict'].notna() | valid_df['prec_cont_real'].notna() | (valid_df['status'] == 'T/O')]

    
    # Create a "Config Label" column for sorting/display

    # Create a "Config Label" column for sorting/display
    def get_config_label(row):
        v = row['variant']
        d = row['d']
        m = row['m']
        if v == 'kcfa':
            if m == 0: return "0CFA"
            return f"kCFA({m})"
        elif v == 'dmcfar':
            if d == 0 and m == 0: return "H(0,0)"
            return f"H({d},{m})"
        return v # Fallback

    valid_df['Config'] = valid_df.apply(get_config_label, axis=1)
    
    # Filter out 'dmcfae' or other variants if they slipped through mapping
    valid_df = valid_df[valid_df['variant'].isin(['kcfa', 'dmcfar'])]
    # Filter out H(0,0) to keep table clean? Or keep it?
    # User said "Use KCFA(0) as baseline", implying 0CFA column should be KCFA.
    # We can drop H(0,0) if it's redundant (Superset of 0CFA).
    # valid_df = valid_df[valid_df['Config'] != 'H(0,0)']


    # Get unique configs and sort them
    configs = sorted(valid_df['Config'].unique())
    
    def config_sort_key(c):
        if c == '0CFA': return (-1, 0)
        # Prioritize kCFA
        # kCFA(k) -> (0, k)
        # H(h,k) -> (1, h, k)
        if c.startswith('kCFA'):
            k = int(c.split('(')[1].split(')')[0])
            return (0, k)
        elif c.startswith('H'):
            # H(d,m)
            parts = c.split('(')[1].split(')')[0].split(',')
            d = int(parts[0])
            m = int(parts[1])
            return (1, d, m)
        return (2, 0)

    configs = sorted(configs, key=config_sort_key)
    print(f"Found Configurations: {configs}")

    # 2. Extract Metrics for each Config
    # We want: Cont Prec, maybe Lit Prec, maybe States?
    # User said "split out results", implying detailed breakdown.
    # A single table with 5 configs * 3 metrics = 15 columns is too wide.
    # Maybe one table for Cont Prec, one for States?
    # Let's do Cont Precision Table first, as it's the main metric.
    
    # Add Lit Prec to valid_df first using the safe logic
    # We need to look up `literalPreciseCount` and `literalMapSize`
    def get_lit_prec_safe(row):
        m = row.get('storeMetrics', {}) if isinstance(row.get('storeMetrics'), dict) else {}
        # If storeMetrics is None or empty, try top level cols if available (load_results might flatten)
        # Actually load_results puts them in top level if available?
        # Let's fallback to row.get
        total = row.get('literalMapSize', 0)
        precise = row.get('literalPreciseCount', 0)
        if pd.isna(total) or total == 0: return 1.0
        return precise / total

    valid_df['Lit_Prec'] = valid_df.apply(get_lit_prec_safe, axis=1)
    
    # Pivot Data
    # Index: Benchmark
    # Columns: Config
    # Values: RIR Metrics & Real Metrics
    
    pivot_cont_rir = valid_df.pivot_table(index='benchmarkName', columns='Config', values='prec_cont_rir_strict', aggfunc='mean')
    pivot_val_rir = valid_df.pivot_table(index='benchmarkName', columns='Config', values='prec_val_rir_strict', aggfunc='mean')
    
    pivot_cont_real = valid_df.pivot_table(index='benchmarkName', columns='Config', values='prec_cont_real', aggfunc='mean')
    pivot_val_real = valid_df.pivot_table(index='benchmarkName', columns='Config', values='prec_val_real', aggfunc='mean')
    
    pivot_states = valid_df.pivot_table(index='benchmarkName', columns='Config', values='States', aggfunc='mean')
    pivot_time = valid_df.pivot_table(index='benchmarkName', columns='Config', values='Time', aggfunc='min')
    pivot_time = pivot_time * 1000 # Convert Seconds to Milliseconds
    pivot_status = valid_df.pivot_table(index='benchmarkName', columns='Config', values='status', aggfunc='first')
    
    # 3. Format & Output
    # We need to process benchmarks in our standard sorted order
    
    # Get list of benchmarks from pivot (should be same)
    benchmarks = pivot_cont_rir.index.tolist()
    
    # Categorize
    bs_data = []
    for b in benchmarks:
        cat = get_benchmark_category(b)
        if cat == 'Handlers': cat_refined = 'Koka-Samples'
        else: cat_refined = cat
        bs_data.append({'Benchmark': b, 'Category': cat_refined})
    
    meta_df = pd.DataFrame(bs_data)
    
    # Shorten Names
    def shorten_name(name):
        prefixes = [
            'analysis/benchmarks/koka-gen/', 
            'analysis/benchmarks/handlers/',
            'analysis/benchmarks/rosetta/rosetta/', 
            'analysis/benchmarks/rosetta/',
            'analysis/benchmarks/suite/',
            'analysis/benchmarks/'
        ]
        for p in prefixes:
            if name.startswith(p):
                name = name[len(p):]
                break
        subdirs = ['m/', 'j/', 'nums0/', 'text/'] 
        for s in subdirs:
            if name.startswith(s):
                name = name[len(s):]
                break
        return name

    meta_df['ShortName'] = meta_df['Benchmark'].apply(shorten_name)
    
    # Sorting
    cat_order = {'Koka-Gen': 0, 'Rosetta': 1, 'Koka-Samples': 2, 'Micro-Suite': 3, 'Other': 4}
    meta_df['Cat_Rank'] = meta_df['Category'].map(cat_order)
    
    # Sort by Cat, then Name (or Size? Let's use Name for stability or Size if available)
    # To sort by size we need 0-CFA size.
    baseline_cfg = configs[0] # Assume first is 0-CFA/k=0
    
    def get_size(row):
        try:
            return pivot_states.loc[row['Benchmark'], baseline_cfg]
        except: return 0
        
    meta_df['SortSize'] = meta_df.apply(get_size, axis=1)
    meta_df = meta_df.sort_values(by=['Cat_Rank', 'SortSize'])
    
    # --- Helper Function for Table Generation ---
    def generate_table(title, pivot_data, metric_type="max", precision=2, use_int=False, prec_check_df=None, avg_func='mean'):
        """
        Generates markdown lines for a table.
        metric_type: "max" (higher is better) or "min" (lower is better)
        prec_check_df: Optional DF to check 0CFA precision (for RIR tables)
        avg_func: 'mean', 'geomean', or 'shifted_geomean'
        """
        lines = []
        lines.append(f"\n## {title}\n")
        
        # Filter configs for display
        display_configs = configs.copy()
        if "RIR" in title and "0CFA" in display_configs:
            display_configs.remove("0CFA")
            
        # Header
        cols = ["Category", "Benchmark"] + display_configs
        header = "| " + " | ".join(cols) + " |"
        sep = "| " + " | ".join(["---"] * len(cols)) + " |"
        lines.append(header)
        lines.append(sep)
        
        current_cat = None
        
        # Identify comparison columns
        col_h = 'H(1,1)'
        col_k = 'kCFA(1)'
        
        has_comparison = col_h in configs and col_k in configs

        for _, row in meta_df.iterrows():
            bench_full = row['Benchmark']
            cat = row['Category']
            name = f"`{row['ShortName']}`"
            cat_str = f"**{cat}**" if cat != current_cat else ""
            current_cat = cat
            
            # Check for 0CFA Precision Special Case
            is_already_precise = False
            if prec_check_df is not None and '0CFA' in prec_check_df.columns:
                try:
                    p0 = prec_check_df.loc[bench_full, '0CFA']
                    if pd.notna(p0) and p0 >= 0.999999:
                        is_already_precise = True
                except: pass
            
            if is_already_precise:
                # Output special row
                # User requested: | 0CFA Already Precise |||||| (no spaces between bars for Madoko merge)
                # We format the first cell with space, then tight bars for the rest
                special_val_str = " *0CFA Precise* " + "|" * (len(display_configs) - 1)
                lines.append(f"| {cat_str} | {name} |{special_val_str}|")
                continue

            # Get values for this row
            row_vals = {}
            for c in display_configs:
                val = pivot_data.loc[bench_full, c]
                if pd.notna(val):
                    row_vals[c] = val
            
            # Find best value (among displayed configs? Or all? User probably wants comparison among displayed)
            # Actually we should compare among all meaningful configs, but for RIR 0CFA is 0 so it doesn't matter for max.
            # Let's stick to display_configs for row_vals to keep it consistent with the view.
            
            best_val = None
            # Filter candidates for best value (Exclude 0CFA and H(0,0))
            candidate_vals = []
            for c, v in row_vals.items():
                if c not in ['0CFA', 'H(0,0)']:
                    candidate_vals.append(v)
            
            if candidate_vals:
                if metric_type == "max":
                    best_val = max(candidate_vals)
                else:
                    best_val = min(candidate_vals)
            
            # Determine winner for H(1,1) vs kCFA(1)
            h_wins = False
            
            # Check status of comparison columns
            stat_h = pivot_status.loc[bench_full, col_h] if col_h in configs else 'Missing'
            stat_k = pivot_status.loc[bench_full, col_k] if col_k in configs else 'Missing'
            
            if col_h in display_configs and col_k in display_configs:
                # If H is OK and K is T/O -> Win
                if stat_h == 'OK' and stat_k == 'T/O':
                    h_wins = True
                # If Both OK, compare values
                elif stat_h == 'OK' and stat_k == 'OK':
                    if col_h in row_vals and col_k in row_vals:
                         val_h = row_vals[col_h]
                         val_k = row_vals[col_k]
                         
                         # Check strict inequality
                         is_better = False
                         if metric_type == "max":
                             if val_h > val_k: is_better = True
                         else: # min
                             if val_h < val_k: is_better = True
                             
                         # Check visual difference
                         # Helper to format a single value
                         def fmt(v):
                             if use_int: return f"{v:.0f}"
                             return f"{v:.{precision}f}"
                             
                         if is_better and fmt(val_h) != fmt(val_k):
                             h_wins = True

            # Format cells
            formatted_vals = []
            for c in display_configs:
                # Check status first
                stat = None
                try:
                    stat = pivot_status.loc[bench_full, c]
                except: pass
                
                if stat == 'T/O':
                    formatted_vals.append("T/O")
                    continue
                
                if c not in row_vals:
                    formatted_vals.append("-")
                    continue
                
                val = row_vals[c]
                
                # Special Case: '0CFA' RIR should be 0.00 (Baseline)
                if c == '0CFA' and "RIR" in title:
                    val = 0.0
                
                # Format string
                if use_int:
                    s_val = f"{val:.0f}"
                else:
                    s_val = f"{val:.{precision}f}"
                
                # Bold if best
                is_best = False
                # Float comparison with tolerance
                if best_val is not None and c not in ['0CFA', 'H(0,0)']:
                    if abs(val - best_val) < 1e-9:
                        is_best = True
                
                if is_best:
                    # Ignore 0.00 as "best" if all are 0.00? No, if none improved, all are best (tied).
                    # But if we have 0CFA Precise case handled above, here it means 0CFA was imprecise but we failed to improve.
                    s_val = f"**{s_val}**"
                
                # Red if H(1,1) winner
                if c == col_h and h_wins:
                    s_val = f"[{s_val}]{{.red}}"
                
                formatted_vals.append(s_val)
                
            lines.append(f"| {cat_str} | {name} | " + " | ".join(formatted_vals) + " |")
            
        # Averages Row
        lines.append("| | **Averages** | " + " | ".join([""] * len(display_configs)) + " |")
        
        for cat_name, _ in sorted(cat_order.items(), key=lambda x: x[1]):
            cat_benches = meta_df[meta_df['Category'] == cat_name]['Benchmark']
            # Filter benchmarks present in pivot_data
            valid_benches = [b for b in cat_benches if b in pivot_data.index]
            
            if not valid_benches: continue
            
            avg_vals = []
            # Calculate averages 
            cat_means = {}
            for c in display_configs:
                try:
                    if c not in pivot_data.columns: continue
                    
                    series = pivot_data.loc[valid_benches, c]
                    m = np.nan
                    
                    if avg_func == 'geomean':
                         m = geometric_mean(series)
                    elif avg_func == 'shifted_geomean':
                         m = shifted_geometric_mean(series)
                    else:
                         m = series.mean()
                         
                    if pd.notna(m): cat_means[c] = m
                except: pass
            
            # Find best average
            # Find best average
            best_avg = None
            # Filter candidates for best average
            candidate_avgs = []
            for c, v in cat_means.items():
                if c not in ['0CFA', 'H(0,0)']:
                    candidate_avgs.append(v)
            
            if candidate_avgs:
                if metric_type == "max": best_avg = max(candidate_avgs)
                else: best_avg = min(candidate_avgs)
            
            # Determine winner for H(1,1) vs kCFA(1) in averages
            avg_h_wins = False
            
            if col_h in display_configs and col_k in display_configs:
                if col_h in cat_means and col_k in cat_means:
                     val_h = cat_means[col_h]
                     val_k = cat_means[col_k]
                     
                     is_better = False
                     if metric_type == "max":
                         if val_h > val_k: is_better = True
                     else:
                         if val_h < val_k: is_better = True
                     
                     def fmt(v):
                         if use_int: return f"{v:.0f}"
                         return f"{v:.{precision}f}"
                         
                     if is_better and fmt(val_h) != fmt(val_k):
                         avg_h_wins = True

            for c in display_configs:
                if c not in cat_means:
                    avg_vals.append("-")
                    continue
                
                val = cat_means[c]
                if use_int: s_val = f"{val:.0f}"
                else: s_val = f"{val:.{precision}f}"
                
                # Bold best average
                if best_avg is not None and c not in ['0CFA', 'H(0,0)']:
                    if abs(val - best_avg) < 1e-9:
                        s_val = f"**{s_val}**"
                
                # Red if H(1,1) winner
                if c == col_h and avg_h_wins:
                    s_val = f"[{s_val}]{{.red}}"
                
                avg_vals.append(s_val)
                
            avg_label = "Mean"
            if avg_func == 'geomean': avg_label = "Geomean"
            elif avg_func == 'shifted_geomean': avg_label = "Shifted Geomean"

            lines.append(f"| **{cat_name}** | {avg_label} | " + " | ".join(avg_vals) + " |")
            
        return lines

    # Generate Markdown Lines
    lines = []
    lines.append("# Appendix Tables\n")
    
    # Table 1: Continuation RIR (Max is best) -> Shifted Geomean
    # Pass pivot_cont_real to check for 0CFA precision
    lines.extend(generate_table("Table B1: Continuation RIR (Strict) by Configuration", pivot_cont_rir, "max", 2, prec_check_df=pivot_cont_real, avg_func='shifted_geomean'))
    
    # Table 2: Value RIR (Max is best) -> Shifted Geomean
    # Pass pivot_val_real to check for 0CFA precision
    lines.extend(generate_table("Table B2: Value RIR (Strict) by Configuration", pivot_val_rir, "max", 2, prec_check_df=pivot_val_real, avg_func='shifted_geomean'))
    
    # Table 3: Continuation Real Precision (Base: 0CFA Addresses) -> Shifted Geomean
    lines.extend(generate_table("Table B3: Continuation Precision by Configuration (Base: 0CFA)", pivot_cont_real, "max", 2, avg_func='shifted_geomean'))

    # Table 4: Value Real Precision (Base: 0CFA Addresses) -> Shifted Geomean
    lines.extend(generate_table("Table B4: Value Precision by Configuration (Base: 0CFA)", pivot_val_real, "max", 2, avg_func='shifted_geomean'))

    # Table 5: State Count (Min is best) -> Geomean
    lines.extend(generate_table("Table B5: State Count (Complexity) by Configuration", pivot_states, "min", 0, True, avg_func='geomean'))
    
    # Table 6: Time (Min is best) -> Geomean
    lines.extend(generate_table("Table B6: Analysis Time (ms) by Configuration", pivot_time, "min", 0, True, avg_func='geomean'))

    # Write to file
    with open("benchmarks/appendix_tables.md", "w") as f:
        f.write("\n".join(lines))
    print("Saved benchmarks/appendix_tables.md")

if __name__ == "__main__":
    generate_markdown()
