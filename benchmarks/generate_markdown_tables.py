
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, get_benchmark_category

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
        
    valid_df = valid_df[valid_df['AbsContPrecision'].notna() | (valid_df['status'] == 'T/O')]
    
    # Create a "Config Label" column for sorting/display
    def get_config_label(row):
        v = row['variant']
        d = row['d']
        m = row['m']
        if v == 'kcfa':
            return f"kCFA({m})"
        elif v == 'dmcfar':
            if d == 0 and m == 0: return "0CFA"
            return f"H({d},{m})"
        return v # Fallback

    valid_df['Config'] = valid_df.apply(get_config_label, axis=1)
    
    # Filter out 'dmcfae' or other variants if they slipped through mapping
    valid_df = valid_df[valid_df['variant'].isin(['kcfa', 'dmcfar'])]
    # Filter out kCFA(0) explicitly as we used H(0,0) -> 0CFA
    valid_df = valid_df[valid_df['Config'] != 'kCFA(0)']

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
    # Values: AbsContPrecision
    
    pivot_cont = valid_df.pivot_table(index='benchmarkName', columns='Config', values='AbsContPrecision', aggfunc='first')
    pivot_lit = valid_df.pivot_table(index='benchmarkName', columns='Config', values='Lit_Prec', aggfunc='first')
    pivot_states = valid_df.pivot_table(index='benchmarkName', columns='Config', values='States', aggfunc='first')
    pivot_time = valid_df.pivot_table(index='benchmarkName', columns='Config', values='Time', aggfunc='first')
    pivot_time = pivot_time * 1000 # Convert Seconds to Milliseconds
    pivot_status = valid_df.pivot_table(index='benchmarkName', columns='Config', values='status', aggfunc='first')
    
    # 3. Format & Output
    # We need to process benchmarks in our standard sorted order
    
    # Get list of benchmarks from pivot (should be same)
    benchmarks = pivot_cont.index.tolist()
    
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
    def generate_table(title, pivot_data, metric_type="max", precision=2, use_int=False):
        """
        Generates markdown lines for a table.
        metric_type: "max" (higher is better) or "min" (lower is better)
        """
        lines = []
        lines.append(f"\n## {title}\n")
        
        # Header
        cols = ["Category", "Benchmark"] + configs
        header = "| " + " | ".join(cols) + " |"
        sep = "| " + " | ".join(["---"] * len(cols)) + " |"
        lines.append(header)
        lines.append(sep)
        
        current_cat = None
        
        # Identify comparison columns
        # We want to highlight H(1,1) if it beats kCFA(1)
        # Assuming format 'H(1,1)' and 'kCFA(1)' from earlier
        col_h = 'H(1,1)'
        col_k = 'kCFA(1)'
        
        has_comparison = col_h in configs and col_k in configs

        for _, row in meta_df.iterrows():
            bench_full = row['Benchmark']
            cat = row['Category']
            name = f"`{row['ShortName']}`"
            cat_str = f"**{cat}**" if cat != current_cat else ""
            current_cat = cat
            
            # Get values for this row
            row_vals = {}
            for c in configs:
                val = pivot_data.loc[bench_full, c]
                if pd.notna(val):
                    row_vals[c] = val
            
            # Find best value
            best_val = None
            if row_vals:
                vals = list(row_vals.values())
                if metric_type == "max":
                    best_val = max(vals)
                else:
                    best_val = min(vals)
            
            # Determine winner for H(1,1) vs kCFA(1)
            h_wins = False
            
            # Check status of comparison columns
            stat_h = pivot_status.loc[bench_full, col_h] if col_h in configs else 'Missing'
            stat_k = pivot_status.loc[bench_full, col_k] if col_k in configs else 'Missing'
            
            if col_h in configs and col_k in configs:
                # If H is OK and K is T/O -> Win
                if stat_h == 'OK' and stat_k == 'T/O':
                    h_wins = True
                # If Both OK, compare values
                elif stat_h == 'OK' and stat_k == 'OK':
                    if col_h in row_vals and col_k in row_vals:
                         val_h = row_vals[col_h]
                         val_k = row_vals[col_k]
                         if metric_type == "max":
                             if val_h > val_k: h_wins = True
                         else: # min
                             if val_h < val_k: h_wins = True

            # Format cells
            formatted_vals = []
            for c in configs:
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
                
                # Format string
                if use_int:
                    s_val = f"{val:.0f}"
                else:
                    s_val = f"{val:.{precision}f}"
                
                # Bold if best
                is_best = False
                # Float comparison with tolerance
                if best_val is not None:
                    if abs(val - best_val) < 1e-9:
                        is_best = True
                
                if is_best:
                    s_val = f"**{s_val}**"
                
                # Red if H(1,1) winner
                if c == col_h and h_wins:
                    s_val = f"[{s_val}]{{.red}}"
                
                formatted_vals.append(s_val)
                
            lines.append(f"| {cat_str} | {name} | " + " | ".join(formatted_vals) + " |")
            
        # Averages Row
        lines.append("| | **Averages** | " + " | ".join([""] * len(configs)) + " |")
        
        for cat_name, _ in sorted(cat_order.items(), key=lambda x: x[1]):
            cat_benches = meta_df[meta_df['Category'] == cat_name]['Benchmark']
            if cat_benches.empty: continue
            
            avg_vals = []
            # Calculate averages 
            # Note: We don't bold/red averages usually, but user said "highlight best result".
            # Usually strict formatting applies to data rows. I'll stick to bolding max average.
            
            # First calculate all averages
            cat_means = {}
            for c in configs:
                try:
                    m = pivot_data.loc[cat_benches, c].mean()
                    if pd.notna(m): cat_means[c] = m
                except: pass
            
            # Find best average
            best_avg = None
            if cat_means:
                vals = list(cat_means.values())
                if metric_type == "max": best_avg = max(vals)
                else: best_avg = min(vals)
            
            for c in configs:
                if c not in cat_means:
                    avg_vals.append("-")
                    continue
                
                val = cat_means[c]
                if use_int: s_val = f"{val:.0f}"
                else: s_val = f"{val:.{precision}f}"
                
                # Bold best average
                if best_avg is not None and abs(val - best_avg) < 1e-9:
                    s_val = f"**{s_val}**"
                
                avg_vals.append(s_val)
                
            lines.append(f"| **{cat_name}** | Average | " + " | ".join(avg_vals) + " |")
            
        return lines

    # Generate Markdown Lines
    lines = []
    lines.append("# Appendix Tables\n")
    
    # Table 1: Continuation Precision (Max is best)
    lines.extend(generate_table("Table B1: Continuation Precision by Configuration", pivot_cont, "max", 2))
    
    # Table 2: Literal Precision (Max is best)
    lines.extend(generate_table("Table B2: Literal Precision by Configuration", pivot_lit, "max", 2))
    
    # Table 3: State Count (Min is best)
    lines.extend(generate_table("Table B3: State Count (Complexity) by Configuration", pivot_states, "min", 0, True))
    
    # Table 4: Time (Min is best)
    lines.extend(generate_table("Table B4: Analysis Time (ms) by Configuration", pivot_time, "min", 0, True))

    # Write to file
    with open("benchmarks/appendix_tables.md", "w") as f:
        f.write("\n".join(lines))
    print("Saved benchmarks/appendix_tables.md")

if __name__ == "__main__":
    generate_markdown()
