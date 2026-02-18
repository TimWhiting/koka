
import os
import json
import numpy as np
import pandas as pd
from scipy.stats import gmean

def geometric_mean(data):
    # Add epsilon
    pos = pd.Series(data).copy()
    pos = pos[pos > 0]
    if len(pos) == 0:
        return np.nan
    return gmean(pos)

def calc_precise_stats(metric, poly, base):
    """Calculates number of precise items (size <= 1) in poly map, relative to base keys."""
    base_map = base.get(metric)
    if not base_map:
        return 0, 0
    
    poly_map = poly.get(metric, {})
    
    hits = 0
    total = 0
    
    for x_id, base_val in base_map.items():
        # Check poly value
        # If missing in poly -> Dead code -> Precise (size 0)
        # If present and <= 1 -> Precise
        
        poly_val = poly_map.get(x_id)
        
        # Note: poly_val could be None if missing
        if poly_val is None:
             hits += 1
        elif poly_val != -1 and poly_val <= 1:
             hits += 1
             
        total += 1
        
    return hits, total

def calc_literal_stats(poly, base):
    """
    Calculates literal precision stats (hits, total) relative to baseline.
    Uses 'literal0CFAPrecise' map (Addr -> Bool).
    Hit = Literal is Precise (True) OR Literal is Dead (Missing in Poly).
    """
    poly_map = poly.get('literal0CFAPrecise', {})
    base_map = base.get('literal0CFAPrecise')
    
    if not base_map:
        return 0, 0
    
    hits = 0
    total = 0
    
    for k, base_val in base_map.items():
        total += 1
        
        # If missing in poly -> Dead Code -> Precise
        if k not in poly_map:
            hits += 1
            continue
            
        # If present, check if precise (True)
        if poly_map[k]:
            hits += 1
            
    return hits, total

def calc_literal_prod_stats(poly, base):
    """
    Calculates literal productivity (improvement) relative to baseline.
    Only considers literals present in the baseline.
    Hit = Literal was Imprecise in Base (False) AND is Precise (True) or Dead (Missing) in Poly.
    """
    poly_map = poly.get('literal0CFAPrecise', {})
    base_map = base.get('literal0CFAPrecise')
    
    if not base_map:
        return 0, 0
    
    hits = 0
    total = 0
    
    for k, base_val in base_map.items():
        total += 1
        
        # We only count hits if there was room for improvement (Base was Imprecise)
        if base_val is False: 
            # Check if now Precise (True) or Dead (Missing)
            if k not in poly_map or poly_map[k] is True:
                hits += 1
                
    return hits, total

def calc_prod_stats(metric, poly, base):
    """Calculates productivity stats (hits, total) relative to baseline."""
    poly_map = poly.get(metric)
    base_map = base.get(metric)
    
    if not base_map: 
        if not poly_map:
            return 0, 0
        raise Exception("Do not call with empty baseline")
    
    hits = 0
    total_relevant = 0
    
    for x_id, base_val in base_map.items():
        # Poly not there means that we found spurious / dead code in base -> always max improvement (0)
        poly_val = poly_map.get(x_id, 0) 
    
        # Logic matches calc_prod
        if base_val == -1:
            if poly_val is not None and poly_val != -1:
                hits += 1
            total_relevant += 1
            continue

        if poly_val is not None and poly_val != -1 and poly_val < base_val:
            hits += 1
        
        total_relevant += 1
            
    return hits, total_relevant

def calc_prod(metric, poly, base):
    """Calculates productivity fraction."""
    hits, total = calc_prod_stats(metric, poly, base)
    if total == 0: return 0.0
    return hits / total

def calc_abs_impr_stats(metric, poly, base):
    """
    Calculates Absolute Precision Improvement stats (hits, total) relative to baseline.
    
    A "hit" is defined as an item that is EITHER:
    1. Precise in the baseline (size <= 1)
    2. Improved in the polyvariant analysis (poly < base)
    
    This metric aims to show "Baseline Precision + Gain", effectively the union of precise items.
    """
    poly_map = poly.get(metric)
    base_map = base.get(metric)
    
    if not base_map: 
        if not poly_map:
            return 0, 0
        raise Exception("Do not call with empty baseline")
    
    hits = 0
    total_relevant = 0
    
    for x_id, base_val in base_map.items():
        # Iterate over keys in BASELINE to ensure comparable set
        
        if base_val == -1: # Base is Top
            # Check if Poly improved
            p_val = poly_map.get(x_id, 0) # Default 0 (dead) if missing
            if p_val != -1:
                hits += 1
        else: # Base is Value
            # Base is precise if <= 1
            is_base_precise = (base_val <= 1)
            
            # Check if Poly improved strictly
            p_val = poly_map.get(x_id, 0)
            # Note: if p_val is None (missing), it is 0. 
            # 0 < b_val (since b_val >= 0 for non-top) is true if b_val > 0.
            
            is_improved = False
            if p_val is not None and p_val != -1 and p_val < base_val:
                is_improved = True
                
            if is_base_precise or is_improved:
                hits += 1
        
        total_relevant += 1
            
    return hits, total_relevant

def calc_relative_prod_stats(metric, poly, base):
    """
    Calculates relative productivity stats (hits, total_imprecise) relative to baseline.
    Denominator is only the number of IMPRECISE items in the baseline.
    """
    poly_map = poly.get(metric)
    base_map = base.get(metric)
    
    if not base_map: 
        if not poly_map:
            return 0, 0
        raise Exception("Do not call with empty baseline")
    
    hits = 0
    total_imprecise = 0
    
    for x_id, base_val in base_map.items():
        # Check if Base is Imprecise
        if base_val == -1 or base_val > 1:
            total_imprecise += 1
            
            # Check for improvement
            poly_val = poly_map.get(x_id, 0)
            
            if base_val == -1:
                if poly_val is not None and poly_val != -1:
                    hits += 1
            elif poly_val is not None and poly_val != -1 and poly_val < base_val:
                hits += 1
            
    return hits, total_imprecise

def calc_literal_relative_prod_stats(poly, base):
    """
    Calculates literal relative productivity.
    Denominator is number of IMPRECISE literals in baseline.
    """
    poly_map = poly.get('literal0CFAPrecise', {})
    base_map = base.get('literal0CFAPrecise')
    
    if not base_map:
        return 0, 0
    
    hits = 0
    total_imprecise = 0
    
    for k, base_val in base_map.items():
        if base_val is False: # Imprecise in Base
            total_imprecise += 1
            
            # Check if now Precise (True) or Dead (Missing)
            if k not in poly_map or poly_map[k] is True:
                hits += 1
                
    return hits, total_imprecise

def calc_relative_prec_stats(metric, poly, base):
    """
    Calculates relative precision stats (hits, total_imprecise) relative to baseline.
    Hit = Item was Imprecise in Base -> Became Strictly Precise (size <= 1) in Poly.
    """
    poly_map = poly.get(metric)
    base_map = base.get(metric)
    
    if not base_map: 
        if not poly_map:
            return 0, 0
        raise Exception("Do not call with empty baseline")
    
    hits = 0
    total_imprecise = 0
    
    for x_id, base_val in base_map.items():
        # Check if Base is Imprecise
        if base_val == -1 or base_val > 1:
            total_imprecise += 1
            
            # Check for Strict Precision (<= 1 or Missing/Dead)
            poly_val = poly_map.get(x_id)
            
            if poly_val is None: # Dead
                hits += 1
            elif poly_val != -1 and poly_val <= 1:
                hits += 1
            
    return hits, total_imprecise

def calc_literal_relative_prec_stats(poly, base):
    """
    Calculates literal relative strict precision.
    Hit = Literal Imprecise in Base -> Precise in Poly.
    """
    poly_map = poly.get('literal0CFAPrecise', {})
    base_map = base.get('literal0CFAPrecise')
    
    if not base_map:
        return 0, 0
    
    hits = 0
    total_imprecise = 0
    
    for k, base_val in base_map.items():
        if base_val is False: # Imprecise in Base
            total_imprecise += 1
            
            # Check if now Precise (True) or Dead (Missing)
            if k not in poly_map or poly_map[k] is True:
                hits += 1
                
    return hits, total_imprecise

def compute_metrics(run, baseline_run=None):
    """Computes precision metrics relative to baseline."""
    
    # Basic info
    metrics = {
        'isTimeout': run.get('isTimeout', False),
        'status': "OK" if not run.get('isTimeout') else "T/O",
        'analysisTimes': run.get('analysisTimes', []),
        'Time': np.mean(run.get('analysisTimes', [0])) if run.get('analysisTimes') else 0.0,
        'variant': run.get('variant'),
        'd': run.get('d'),
        'm': run.get('m'),
        'benchmarkName': run.get('benchmarkName', 'unknown')
    }

    m = run.get('storeMetrics')
    if not m:
        
        # Pass through raw literal counts for debugging
        metrics['literal0CFATopCount'] = 0
        metrics['numLitAddresses'] = 0
        
        return metrics

    # Absolute Precision (for filtering)
    num_cont = m.get('numContAddresses', 0)
    cont_single = m.get('contStrSingletons', 0)
    metrics['AbsContPrecision'] = cont_single / num_cont if num_cont > 0 else 1.0
    
    num_struct = m.get('numStructAddresses', 0)
    val_single = m.get('val0CFAStrSingletons', 0)
    metrics['AbsStructPrecision'] = val_single / num_struct if num_struct > 0 else 1.0
    
    metrics['States'] = m.get('numTotalFixInputStates', 0)

    # Absolute Literal Stats (using map)
    lit_map = m.get('literal0CFAPrecise', {})
    metrics['literalMapSize'] = len(lit_map)
    metrics['literalPreciseCount'] = sum(1 for v in lit_map.values() if v is True)


    # Relative Metrics
    if baseline_run and baseline_run.get('storeMetrics'):
        baseline = baseline_run['storeMetrics']
        
        # prec_struct: Improvement in Store Structure (UNUSED)
        # s_hits, s_total = calc_prod_stats('storeToStrSizes', m, baseline)
        # metrics['prec_struct'] = s_hits / s_total if s_total > 0 else 0.0
        
        # prod_k_str: Improvement in Continuation Structure (Used in Sweep Productivity)
        metrics['prod_k_str'] = calc_prod('structToContStrSizes', m, baseline)
        
        # prec_val_total: Combined Store + Literal Improvement (Standard Productivity)
        # Fix: Use map-based calculation to ensure we only look at baseline scope
        l_hits, l_total = calc_literal_prod_stats(m, baseline)
        
        # We need s_hits/s_total for prec_val_total, so calculate them if not done above
        s_hits, s_total = calc_prod_stats('storeToStrSizes', m, baseline)

        total_hits = s_hits + l_hits
        total_items = s_total + l_total
        
        metrics['prec_val_total'] = total_hits / total_items if total_items > 0 else 0.0
        metrics['prec_val_total_hits'] = total_hits
        metrics['prec_val_total_total'] = total_items
        
        # --- NEW METRICS: RELATIVE IMPROVEMENT (Effective Resolution Rate) ---
        # (UNUSED - We use RIR Strict now)
        
        # Store Relative
        # s_rel_hits, s_rel_denom = calc_relative_prod_stats('storeToStrSizes', m, baseline)
        
        # Literal Relative
        # l_rel_hits, l_rel_denom = calc_literal_relative_prod_stats(m, baseline)
        
        # Combined Value Relative
        # total_rel_hits = s_rel_hits + l_rel_hits
        # total_rel_denom = s_rel_denom + l_rel_denom
        # metrics['prec_val_relative'] = total_rel_hits / total_rel_denom if total_rel_denom > 0 else 0.0
        # metrics['prec_val_relative_hits'] = total_rel_hits
        # metrics['prec_val_relative_total'] = total_rel_denom
        
        # Continuation Relative
        # c_rel_hits, c_rel_denom = calc_relative_prod_stats('structToContStrSizes', m, baseline)
        # metrics['prec_cont_relative'] = c_rel_hits / c_rel_denom if c_rel_denom > 0 else 0.0
        # metrics['prec_cont_relative_hits'] = c_rel_hits
        # metrics['prec_cont_relative_total'] = c_rel_denom
        
        
        # metrics['prec_val_relative_impr'] = metrics['prec_val_relative'] # Alias for clarity
        # metrics['prec_val_relative_impr_hits'] = total_rel_hits
        
        # metrics['prec_cont_relative_impr'] = metrics['prec_cont_relative'] # Alias for clarity
        # metrics['prec_cont_relative_impr_hits'] = c_rel_hits
        
        # --- Strict RIR (Recovery of Precision) ---
        # Hit = Was Imprecise in Base -> Became Strictly Precise (size <= 1)
        
        # Store Relative Strict
        s_rir_hits, s_rir_denom = calc_relative_prec_stats('storeToStrSizes', m, baseline)
        
        # Literal Relative Strict
        l_rir_hits, l_rir_denom = calc_literal_relative_prec_stats(m, baseline)
        
        # Combined Value Strict RIR
        total_rir_hits = s_rir_hits + l_rir_hits
        total_rir_denom = s_rir_denom + l_rir_denom 
        metrics['prec_val_rir_strict'] = total_rir_hits / total_rir_denom if total_rir_denom > 0 else 0.0
        metrics['prec_val_rir_strict_hits'] = total_rir_hits
        metrics['baseline_val_imprecise'] = total_rir_denom
        
        # Continuation Strict RIR
        c_rir_hits, c_rir_denom = calc_relative_prec_stats('structToContStrSizes', m, baseline)
        metrics['prec_cont_rir_strict'] = c_rir_hits / c_rir_denom if c_rir_denom > 0 else 0.0
        metrics['prec_cont_rir_strict_hits'] = c_rir_hits
        metrics['baseline_cont_imprecise'] = c_rir_denom
        
        # --- NEW METRICS ---
        
        # 1. Real Precision (Count <= 1 or Missing, relative to Baseline)
        
        # Store Real
        s_real_hits, s_real_total = calc_precise_stats('storeToStrSizes', m, baseline)
        
        # Literals Real
        # Use new map-based calculation
        l_real_hits, l_total = calc_literal_stats(m, baseline)
        
        # Combined Value Real (Store + Literals)
        total_real_hits = s_real_hits + l_real_hits
        total_real_denom = s_real_total + l_total
        metrics['prec_val_real'] = total_real_hits / total_real_denom if total_real_denom > 0 else 0.0
        metrics['prec_val_real_hits'] = total_real_hits
        metrics['prec_val_real_total'] = total_real_denom
        
        # 2. Absolute Improvement (Baseline Precision + Gain) (UNUSED)
        
        # Store Abs Impr
        # s_abs_impr_hits, s_total_abs = calc_abs_impr_stats('storeToStrSizes', m, baseline)
        
        # Literal Abs Impr
        # For Literals, "Real Precision" IS "Absolute Improvement" logic
        # (Precise now means improved or already precise)
        # l_abs_impr_hits = l_real_hits
        
        # Combined Value Abs Impr (Store + Literals)
        # total_abs_impr_hits = s_abs_impr_hits + l_abs_impr_hits
        # total_abs_denom = s_total_abs + l_total
        # metrics['prec_val_abs_impr'] = total_abs_impr_hits / total_abs_denom if total_abs_denom > 0 else 0.0
        # metrics['prec_val_abs_impr_hits'] = total_abs_impr_hits
        # metrics['prec_val_abs_impr_total'] = total_abs_denom

        # Continuation Real
        c_real_hits, c_real_total = calc_precise_stats('structToContStrSizes', m, baseline)
        metrics['prec_cont_real'] = c_real_hits / c_real_total if c_real_total > 0 else 0.0
        metrics['prec_cont_real_hits'] = c_real_hits
        metrics['prec_cont_real_total'] = c_real_total

        # Continuation Absolute Improvement (UNUSED)
        # c_abs_impr_hits, c_total = calc_abs_impr_stats('structToContStrSizes', m, baseline)
        # metrics['prec_cont_abs_impr'] = c_abs_impr_hits / c_total if c_total > 0 else 0.0
        # metrics['prec_cont_abs_impr_hits'] = c_abs_impr_hits
        # metrics['prec_cont_abs_impr_total'] = c_total
        
        # Continuation Productivity (Structure)
        # Note: 'prod_k_str' was calculated earlier, we need to add the counts
        k_hits, k_total = calc_prod_stats('structToContStrSizes', m, baseline)
        metrics['prod_k_str_hits'] = k_hits
        metrics['prod_k_str_total'] = k_total
        
        # Remove/Zero out intermediate single-component metrics to avoid confusion if not needed
        # metrics['prec_struct_real'] = s_real_hits / s_real_total if s_real_total > 0 else 0.0
        # metrics['prec_struct_abs_impr'] = s_abs_impr_hits / s_total_abs if s_total_abs > 0 else 0.0
        
        
        # Add raw literal counts for debugging (Optional, now covered above)
        # metrics['numLitAddresses'] = l_total # Redundant
        # metrics['literalHits'] = l_real_hits # Relative hits (should match precise count if baseline is self)

        # --- NEW METRICS: IMPROVEMENT RATIOS (Factor over Baseline Hits) ---
        # 1. Precise Ratio: Hits(New) / Hits(Base)
        # Measures expansion of the "Fully Resolved" set.
        
        # Store + Lit Precise Hits (Base)
        s_base_hits, _ = calc_precise_stats('storeToStrSizes', baseline, baseline)
        l_base_hits, _ = calc_literal_stats(baseline, baseline)
        val_base_hits = s_base_hits + l_base_hits
        
        c_base_hits, _ = calc_precise_stats('structToContStrSizes', baseline, baseline)
        
        # Precise Ratio
        metrics['impr_precise_val'] = total_real_hits / val_base_hits if val_base_hits > 0 else np.nan
        metrics['impr_precise_cont'] = c_real_hits / c_base_hits if c_base_hits > 0 else np.nan
        
        # 2. Any Improvement Ratio: (PreciseNew + ImprovedNew) / Hits(Base)
        # Measures expansion of "Useful Information" set relative to original useful set.
        
        # USE: Real Hits + RIR Hits? No. 'Any Improvement' was defined as 'Absolute Improvement' (BasePrecise + Gained)
        # Since we commented out 'Absolute Improvement', we need to recalculate it locally or uncomment if used here.
        # 'prec_val_abs_impr' was used for 'impr_any_val'.
        
        # Recalculate 'Any Improvement' hits just for this metric (without storing the full metric if unused elsewhere)
        # Store Abs Impr Hits
        s_abs_impr_hits, _ = calc_abs_impr_stats('storeToStrSizes', m, baseline)
        # Literal Abs Impr Hits (= Real Hits)
        l_abs_impr_hits = l_real_hits
        
        total_abs_impr_hits = s_abs_impr_hits + l_abs_impr_hits
        
        # Cont Abs Impr Hits
        c_abs_impr_hits, _ = calc_abs_impr_stats('structToContStrSizes', m, baseline)

        metrics['impr_any_val'] = total_abs_impr_hits / val_base_hits if val_base_hits > 0 else np.nan
        metrics['impr_any_cont'] = c_abs_impr_hits / c_base_hits if c_base_hits > 0 else np.nan

    else:
        # metrics['prec_struct'] = 0.0
        metrics['prod_k_str'] = 0.0
        metrics['prec_val_total'] = 0.0
        metrics['prec_val_real'] = 0.0
        # metrics['prec_val_abs_impr'] = 0.0
        metrics['prec_cont_real'] = 0.0
        # metrics['prec_cont_abs_impr'] = 0.0
        # metrics['prec_val_relative'] = 0.0
        # metrics['prec_val_relative_hits'] = 0
        # metrics['prec_val_relative_total'] = 0
        # metrics['prec_cont_relative'] = 0.0
        # metrics['prec_cont_relative_hits'] = 0
        # metrics['prec_cont_relative_total'] = 0
        
        # metrics['prec_val_relative_impr'] = 0.0
        # metrics['prec_cont_relative_impr'] = 0.0
        metrics['prec_val_rir_strict'] = 0.0
        metrics['prec_cont_rir_strict'] = 0.0
        
        metrics['impr_precise_val'] = 0.0
        metrics['impr_precise_cont'] = 0.0
        metrics['impr_any_val'] = 0.0
        metrics['impr_any_cont'] = 0.0

    return metrics

def load_results_with_baselines(base_dir="benchmarks/results-cached"):
    """Loads results, identifies 0-CFA baselines, and calculates metrics."""
    # 1. Load all files
    all_runs = []
    runs_by_bench = {}
    
    for root, _, files in os.walk(base_dir):
        for file in files:
            if file.endswith(".json"):
                try:
                    with open(os.path.join(root, file), 'r') as f:
                        data = json.load(f)
                        data['filePath'] = os.path.join(root, file)
                        # Ensure d/m are strings or consistent
                        all_runs.append(data)
                        
                        bench = data.get('benchmarkName')
                        if bench:
                            if bench not in runs_by_bench:
                                runs_by_bench[bench] = []
                            runs_by_bench[bench].append(data)
                except:
                    pass
    
    # 2. Process each benchmark
    processed_results = []
    
    for bench, runs in runs_by_bench.items():
        # Find baseline: kcfa d=0 m=0
        baseline = None
        for r in runs:
            if r.get('variant') == 'kcfa' and str(r.get('d')) == '0':
                baseline = r
                break
        
        # Fallback to dmcfar d=0 m=1 if kcfa missing
        if not baseline:
            for r in runs:
                 if r.get('variant') == 'dmcfar' and str(r.get('d')) == '0' and str(r.get('m')) == '1':
                     baseline = r
                     break
        
        # If no strict 0-CFA found, try to find "lowest" configuration?
        # Typically 0-CFA should exist if the suite was run.
        # If not, relative metrics will be 0.
        
        for r in runs:
            # Skip runs without metrics unless it's a timeout
            if not r.get('storeMetrics') and not r.get('isTimeout'):
                continue
                
            m = compute_metrics(r, baseline)
            processed_results.append(m)
            
    return processed_results

def geometric_sd(data):
    """Calculates geometric standard deviation."""
    clean = pd.to_numeric(data, errors='coerce').dropna()
    pos = clean[clean > 0]
    if pos.empty: return np.nan
    log_data = np.log(pos)
    return np.exp(np.std(log_data))

def get_complex_benchmarks(df, threshold=0.99):
    """Returns list of benchmark names where 0-CFA precision < threshold (Union of Cont and Val)."""
    cont = get_complex_cont_benchmarks(df, threshold)
    val = get_complex_val_benchmarks(df, threshold)
    return list(set(cont) | set(val))

def get_complex_cont_benchmarks(df, threshold=0.99):
    """Returns list of benchmarks where 0-CFA Continuation precision < threshold."""
    baseline = df[(df['variant'] == 'kcfa') & (df['d'] == 0) & (df['m'] == 0)]
    if baseline.empty: return df['benchmarkName'].unique()
    return baseline[baseline['AbsContPrecision'] < threshold]['benchmarkName'].unique()
def get_large_benchmarks(df, threshold=200):
    """Returns list of benchmarks where 0-CFA States > threshold."""
    baseline = df[(df['variant'] == 'kcfa') & (df['d'] == 0) & (df['m'] == 0)]
    if baseline.empty: return df['benchmarkName'].unique()
    return baseline[baseline['States'] > threshold]['benchmarkName'].unique()
def get_complex_val_benchmarks(df, threshold=0.99):
    """Returns list of benchmarks where 0-CFA Value (Struct) precision < threshold."""
    baseline = df[(df['variant'] == 'kcfa') & (df['d'] == 0) & (df['m'] == 0)]
    if baseline.empty: return df['benchmarkName'].unique()
    return baseline[baseline['AbsStructPrecision'] < threshold]['benchmarkName'].unique()

def prepare_tradeoff_data(results, config1, config2, metrics):
    """
    Prepares data for tradeoff analysis between two configurations.
    config1: dict {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'}
    config2: dict {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': '1,1-HMCFAR'}
    metrics: dict {'Precision': 'prec_struct', 'Cost': 'States'}
    """
    df = pd.DataFrame(results)
    
    # Filter for the two configs
    c1 = df[(df['variant'] == config1['variant']) & 
            (df['d'] == config1['d']) & 
            (df['m'] == config1['m'])].copy()
    c1['Configuration'] = config1['label']
    
    c2 = df[(df['variant'] == config2['variant']) & 
            (df['d'] == config2['d']) & 
            (df['m'] == config2['m'])].copy()
    c2['Configuration'] = config2['label']
    
    combined = pd.concat([c1, c2])
    
    # Pivot
    pivot_cols = ['benchmarkName', 'Configuration']
    value_cols = list(metrics.values()) + ['status'] # Add status
    
    # Pivot creates MultiIndex columns
    df_pivot = combined.pivot(index='benchmarkName', columns='Configuration', values=value_cols)
    
    # Flatten columns: State_1-kCFA, Precision_1-kCFA, etc.
    df_pivot.columns = [f"{col[0]}_{col[1]}" for col in df_pivot.columns]
    df_pivot = df_pivot.reset_index()
    
    # Map back to generic names for easier plotting
    rename_map = {}
    for metric_name, col_name in metrics.items():
        # Check if columns exist
        base_col = f"{col_name}_{config1['label']}"
        new_col = f"{col_name}_{config2['label']}"
        if base_col in df_pivot.columns:
             rename_map[base_col] = f"{metric_name}_Base"
        if new_col in df_pivot.columns:
             rename_map[new_col] = f"{metric_name}_New"
             
    # Map status
    if f"status_{config1['label']}" in df_pivot.columns:
        rename_map[f"status_{config1['label']}"] = "Status_Base"
    if f"status_{config2['label']}" in df_pivot.columns:
        rename_map[f"status_{config2['label']}"] = "Status_New"
    
    df_final = df_pivot.rename(columns=rename_map)
    # Do NOT dropna() here, let the plotter handle partials
    # df_final = df_final.dropna() 
    
    
    # Calculate Gain and Ratio
    # Note: Cost_New/Cost_Base depends on metric direction
    # But usually ratio of New/Base is standard.
    # Precision Gain = New - Base
    
    if 'Precision_New' in df_final.columns and 'Precision_Base' in df_final.columns:
        df_final['Prec_Gain'] = df_final['Precision_New'] - df_final['Precision_Base']
    
    if 'Cost_New' in df_final.columns and 'Cost_Base' in df_final.columns:
        c_new = df_final['Cost_New'].fillna(0.0).astype(float)
        c_base = df_final['Cost_Base'].fillna(0.0).astype(float)
        c_base[c_base == 0] = 1e-9
        df_final['Cost_Ratio'] = c_new / c_base
    
    return df_final

def get_tradeoff_color(prec_gain, cost_ratio):
    """
    Returns color based on Cost/Benefit analysis.
    Green: Win-Win (Better Prec & Lower Cost)
    Blue: Trade-off (Better Prec & Higher Cost)
    Red: Regression (Worse Prec)
    """
    if prec_gain < -0.005: # Worse Precision
        return 'red', 0.6
    elif prec_gain > 0.005: # Better Precision
        if cost_ratio < 1.0:
            return 'green', 0.6 # Win-Win
        else:
            return 'blue', 0.6 # Trade-off
    else:
        # Comparable precision
        if cost_ratio < 1.0:
            return 'gray', 0.4 # Efficiency Gain (same prec) - Keep gray to avoid confusion with Prec gain
        elif cost_ratio > 1.0:
            return 'gray', 0.4 # Efficiency Loss (not quite Regression)
        return 'gray', 0.3

def filter_common_benchmarks(df, config_list):
    """
    Keeps only benchmarks that appear in all specified configurations.
    config_list: list of dicts {'variant': 'kcfa', 'd': 0, 'm': 0}
    """
    common_bench = None
    
    for config in config_list:
        subset = df[
            (df['variant'] == config['variant']) & 
            (df['d'] == config['d']) & 
            (df['m'] == config['m'])
        ]
        benchs = set(subset['benchmarkName'].unique())
        
        if common_bench is None:
            common_bench = benchs
        else:
            common_bench = common_bench.intersection(benchs)
            
    print(f"Filtering: {len(common_bench)} benchmarks present in all {len(config_list)} configurations.")
    return df[df['benchmarkName'].isin(common_bench)]

def get_benchmark_category(bench_name):
    """
    Categorizes benchmark based on path/name.
    Categories:
    - Koka-Gen: 'koka-gen'
    - Rosetta: 'rosetta'
    - Handlers: 'handlers'
    - Suite: 'suite' (Micro-benchmarks)
    - Other: Fallback
    """
    if 'koka-gen' in bench_name:
        return 'Koka-Gen'
    elif 'rosetta' in bench_name or 'handlers' in bench_name:
        return 'Koka-Samples'
    elif 'suite' in bench_name:
        return 'Micro-Suite'
    else:
        return 'Other'


