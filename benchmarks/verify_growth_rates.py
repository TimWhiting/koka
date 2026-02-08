#!/usr/bin/env python3
"""
Verify growth rate claims with statistical rigor.
Computes R² values and tests goodness of fit for different models.
"""

import json
import os
import numpy as np
import pandas as pd
from scipy import stats

def r2_score(y_true, y_pred):
    """Compute R² score without sklearn."""
    ss_res = np.sum((y_true - y_pred) ** 2)
    ss_tot = np.sum((y_true - np.mean(y_true)) ** 2)
    return 1 - (ss_res / ss_tot)

def load_all_results(root_path="benchmarks/old-results"):
    """Load all benchmark results."""
    all_results = []
    for root, dirs, files in os.walk(root_path):
        for f_name in files:
            if f_name.endswith('.json'):
                rel_path = os.path.relpath(root, root_path)
                parts = rel_path.split(os.sep)
                if len(parts) >= 3:
                    variant = parts[0]
                    d = parts[1]
                    m = parts[2]
                    
                    file_path = os.path.join(root, f_name)
                    with open(file_path, 'r') as f:
                        try:
                            if os.path.getsize(file_path) == 0:
                                continue
                            data = json.load(f)
                            if isinstance(data, dict):
                                data.update({
                                    'variant': variant,
                                    'd': int(d),
                                    'm': int(m),
                                })
                                all_results.append(data)
                        except (json.JSONDecodeError, ValueError):
                            pass
    return all_results

def analyze_growth_rate(results, variant, d_val, m_val, min_size=350):
    """
    Analyze growth rate for a specific configuration.
    Tests multiple models and reports goodness of fit.
    """
    
    # Get program sizes from KCFA 0-0
    program_sizes = {}
    for r in results:
        if r['variant'] == 'kcfa' and r['d'] == 0 and r['m'] == 0:
            bench = r['benchmarkName']
            if '/suite/' in bench:  # Skip microbenchmarks
                continue
            if r.get('storeMetrics'):
                m = r['storeMetrics']
                total_states = m.get('numTotalFixInputStates', 0)
                store_addrs = m.get('numStoreAddresses', 0)
                configs_visited = total_states - store_addrs
                if configs_visited >= min_size:
                    program_sizes[bench] = configs_visited
    
    # Collect timing data for this configuration
    data_points = []
    for r in results:
        bench = r['benchmarkName']
        if bench not in program_sizes:
            continue
        
        # Match configuration (handle KCFA special case)
        if variant == 'kcfa':
            matches = r['variant'] == variant and r['d'] == 0 and r['m'] == m_val
        else:
            matches = r['variant'] == variant and r['d'] == d_val and r['m'] == m_val
        
        if matches and not r.get('isTimeout') and r.get('analysisTimes'):
            size = program_sizes[bench]
            time = np.mean(r['analysisTimes'])
            data_points.append({'size': size, 'time': time, 'benchmark': bench})
    
    if len(data_points) < 5:
        print(f"Insufficient data for {variant} d={d_val} m={m_val}: only {len(data_points)} points")
        return None
    
    df = pd.DataFrame(data_points).sort_values('size')
    X = df['size'].values
    Y = df['time'].values
    
    print(f"\n{'='*80}")
    print(f"Growth Rate Analysis: {variant.upper()} (d={d_val}, m={m_val})")
    print(f"{'='*80}")
    print(f"Data points: {len(X)}")
    print(f"Size range: {X.min():.0f} - {X.max():.0f} configurations")
    print(f"Time range: {Y.min():.4f}s - {Y.max():.4f}s")
    
    # Model 1: Linear (y = ax + b)
    slope_lin, intercept_lin, r_lin, p_lin, se_lin = stats.linregress(X, Y)
    Y_pred_lin = slope_lin * X + intercept_lin
    r2_lin = r2_score(Y, Y_pred_lin)
    
    # Model 2: Polynomial (y = ax^k) - fit in log-log space
    log_X = np.log10(X)
    log_Y = np.log10(Y)
    slope_poly, intercept_poly, r_poly, p_poly, se_poly = stats.linregress(log_X, log_Y)
    Y_pred_poly = 10 ** (intercept_poly + slope_poly * log_X)
    r2_poly = r2_score(Y, Y_pred_poly)
    
    # Model 3: Exponential (y = ae^(bx)) - fit in log-linear space
    slope_exp, intercept_exp, r_exp, p_exp, se_exp = stats.linregress(X, log_Y)
    Y_pred_exp = 10 ** (intercept_exp + slope_exp * X)
    r2_exp = r2_score(Y, Y_pred_exp)
    
    print(f"\nModel Fits:")
    print(f"{'Model':<20} {'Equation':<30} {'R²':<10} {'Interpretation'}")
    print(f"{'-'*80}")
    print(f"{'Linear':<20} {'y = ax + b':<30} {r2_lin:>8.4f}   {f'slope={slope_lin:.2e}'}")
    print(f"{'Polynomial (log-log)':<20} {f'y = ax^{slope_poly:.2f}':<30} {r2_poly:>8.4f}   {'exponent=' + f'{slope_poly:.2f}'}")
    print(f"{'Exponential (log-lin)':<20} {f'y = ae^(bx), b={slope_exp:.2e}':<30} {r2_exp:>8.4f}   {f'exp coef={slope_exp:.2e}'}")
    
    # Determine best fit
    models = [
        ('Linear', r2_lin),
        ('Polynomial', r2_poly),
        ('Exponential', r2_exp)
    ]
    best_model = max(models, key=lambda x: x[1])
    
    print(f"\nBest fit by R²: {best_model[0]} (R² = {best_model[1]:.4f})")
    
    # Test if models are significantly different
    residuals_poly = Y - Y_pred_poly
    residuals_exp = Y - Y_pred_exp
    
    # Compute mean squared errors
    mse_poly = np.mean(residuals_poly ** 2)
    mse_exp = np.mean(residuals_exp ** 2)
    
    print(f"\nMean Squared Error:")
    print(f"  Polynomial: {mse_poly:.6f}")
    print(f"  Exponential: {mse_exp:.6f}")
    print(f"  Ratio (Exp/Poly): {mse_exp/mse_poly:.2f}")
    
    if abs(r2_poly - r2_exp) < 0.05:
        print(f"\n⚠️  WARNING: R² values are very close ({abs(r2_poly - r2_exp):.4f} difference)")
        print(f"    The data may not be sufficient to distinguish between polynomial and exponential growth.")
    
    # Additional diagnostics
    print(f"\n{'='*80}")
    print("INTERPRETATION GUIDE:")
    print(f"{'='*80}")
    
    if r2_poly > 0.85:
        print(f"✓ Polynomial model fits well (R² = {r2_poly:.3f})")
        print(f"  Fitted exponent k = {slope_poly:.2f}")
        if slope_poly < 1.5:
            print(f"  → Suggests sub-quadratic growth (better than n²)")
        elif slope_poly < 2.5:
            print(f"  → Suggests approximately quadratic growth (≈n²)")
        else:
            print(f"  → Suggests super-quadratic growth (worse than n²)")
    else:
        print(f"⚠️  Polynomial model has modest fit (R² = {r2_poly:.3f})")
        print(f"   Data may not follow simple power law")
    
    if r2_exp > 0.85:
        print(f"\n✓ Exponential model fits well (R² = {r2_exp:.3f})")
        print(f"  Fitted coefficient b = {slope_exp:.2e}")
    else:
        print(f"\n⚠️  Exponential model has modest fit (R² = {r2_exp:.3f})")
    
    print(f"\n{'='*80}")
    
    return {
        'variant': variant,
        'd': d_val,
        'm': m_val,
        'n_points': len(X),
        'size_range': (X.min(), X.max()),
        'r2_linear': r2_lin,
        'r2_poly': r2_poly,
        'r2_exp': r2_exp,
        'poly_exponent': slope_poly,
        'exp_coefficient': slope_exp,
        'best_model': best_model[0]
    }

def main():
    print("Loading results...")
    results = load_all_results()
    print(f"Loaded {len(results)} results.")
    
    # Analyze key configurations
    configs = [
        ('dmcfar', 1, 1, "DMCFAR at (d=1, m=1) - Good precision-cost balance"),
        ('dmcfar', 2, 2, "DMCFAR at (d=2, m=2) - Highest sensitivity"),
        ('kcfa', 0, 1, "k-CFA with k=1"),
        ('kcfa', 0, 2, "k-CFA with k=2"),
    ]
    
    summary_results = []
    
    for variant, d_val, m_val, description in configs:
        print(f"\n\n{description}")
        result = analyze_growth_rate(results, variant, d_val, m_val, min_size=350)
        if result:
            summary_results.append(result)
    
    # Summary table
    print(f"\n\n{'='*80}")
    print("SUMMARY TABLE: Growth Rate Analysis")
    print(f"{'='*80}")
    print(f"{'Variant':<10} {'Config':<8} {'N':<5} {'Size Range':<20} {'R²(Poly)':<10} {'R²(Exp)':<10} {'Best Fit':<12} {'Poly Exp':<10}")
    print(f"{'-'*80}")
    
    for r in summary_results:
        config_str = f"({r['d']},{r['m']})" if r['variant'] != 'kcfa' else f"k={r['m']}"
        size_range_str = f"{r['size_range'][0]:.0f}-{r['size_range'][1]:.0f}"
        print(f"{r['variant']:<10} {config_str:<8} {r['n_points']:<5} {size_range_str:<20} "
              f"{r['r2_poly']:>8.4f}  {r['r2_exp']:>8.4f}  {r['best_model']:<12} {r['poly_exponent']:>8.2f}")
    
    print(f"{'='*80}")
    
    print(f"\n{'='*80}")
    print("RECOMMENDATIONS FOR PAPER")
    print(f"{'='*80}")
    print("""
1. If R² values are high (>0.85) and clearly different between polynomial/exponential:
   → You can say "fitted models show..." with the R² values

2. If R² values are modest (0.6-0.85):
   → Say "preliminary trends suggest..." and acknowledge limited data

3. If R² values are very close (<0.05 difference):
   → Say "data is insufficient to distinguish growth patterns" or rely on theory

4. If you have theoretical complexity bounds:
   → Lead with theory, say "empirical data is consistent with theoretical bounds"

5. Consider adding R² to your plot legends for transparency

Current framing suggestion based on above analysis:
- Report what you measured (times, sizes, precision)
- Show the fitted curves in plots
- Be careful about claiming "polynomial vs exponential" without theory
- Focus on "DMCFAR scales more favorably than k-CFA on available benchmarks"
    """)

if __name__ == '__main__':
    main()
