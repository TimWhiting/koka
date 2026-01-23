#!/usr/bin/env python3
"""
Analyze correlation between sensitivity parameters and actual precision/cost changes.
Shows how precision improves (or worsens) as D/M(K)/K increase.
"""

import os
import csv
import json
from pathlib import Path
from collections import defaultdict
from statistics import mean, stdev
from typing import Dict, List, Tuple

RESULTS_DIR = Path("benchmarks/results")
OUTPUT_DIR = Path("benchmarks/analysis/exports")

def load_all_results(benchmark: str, analysis: str) -> List[Dict]:
    """Load all CSV results for a benchmark/analysis combination."""
    # Search in benchmarks/results/*/*/suite/{benchmark}.csv
    all_results = []
    
    if not RESULTS_DIR.exists():
        return []

    # Recursively find all csv files with the benchmark name
    # We expect them to be in d/m/suite/benchmark.csv
    # But since 'benchmark' is just "basic", we search for "basic.csv"
    # and filter for those in "suite" folder if needed, or just generally.
    # The script hardcodes SUITE benchmarks.
    
    file_pattern = f"{benchmark}.csv"
    
    for csv_file in RESULTS_DIR.rglob(file_pattern):
        # We assume structure is valid.
        with open(csv_file, 'r') as f:
            reader = csv.DictReader(f)
            for row in reader:
                # Filter by analysis type (the 'Analysis' column)
                if row.get('Analysis') != analysis:
                    continue
                    
                try:
                    row['D'] = int(row['D']) if row['D'] else 0
                    row['M(K)'] = int(row['M(K)']) if row['M(K)'] else 0
                    row['K'] = int(row.get('K', 0)) if row.get('K') else 0
                    row['Precise'] = float(row['Precise'])
                    
                    # Compute average time if Time column is missing
                    if 'Time' in row and row['Time'] and row['Time'] != 'timeout':
                        row['Time'] = float(row['Time'])
                    else:
                        times = []
                        for t in ['Time1', 'Time2', 'Time3']:
                            if t in row and row[t] and row[t] != 'timeout':
                                times.append(float(row[t]))
                        row['Time'] = mean(times) if times else 0.0
                        
                    all_results.append(row)
                except (ValueError, TypeError):
                    continue
    
    return all_results

def analyze_parameter_sensitivity(results: List[Dict], param_name: str) -> Dict:
    """
    Analyze how precision and time change with a parameter.
    Returns per-example precision changes and cost multipliers.
    """
    # Group by example (File/Example)
    by_example = defaultdict(list)
    for r in results:
        by_example[r['File/Example']].append(r)
    
    # For each example, track how precision changes with parameter
    example_analyses = []
    
    for example, rows in by_example.items():
        # Sort by parameter
        if param_name == 'D':
            sorted_rows = sorted(rows, key=lambda r: r['D'])
            param_values = [r['D'] for r in sorted_rows]
        elif param_name == 'M(K)':
            sorted_rows = sorted(rows, key=lambda r: r['M(K)'])
            param_values = [r['M(K)'] for r in sorted_rows]
        else:  # K
            sorted_rows = sorted(rows, key=lambda r: r['K'])
            param_values = [r['K'] for r in sorted_rows]
        
        precisions = [float(r['Precise']) for r in sorted_rows]
        times = [float(r['Time']) for r in sorted_rows]
        
        # Analyze changes
        precision_improved = False
        precision_worsened = False
        precision_stable = True
        
        for i in range(1, len(precisions)):
            if precisions[i] > precisions[i-1]:
                precision_improved = True
                precision_stable = False
            elif precisions[i] < precisions[i-1]:
                precision_worsened = True
                precision_stable = False
        
        # Cost multiplier from min to max parameter
        if len(times) > 1 and times[0] > 0:
            cost_multiplier = times[-1] / times[0]
        else:
            cost_multiplier = 1.0
        
        # Final precision
        final_precision = precisions[-1]
        initial_precision = precisions[0]
        precision_change = final_precision - initial_precision
        
        example_analyses.append({
            'example': example,
            'param_values': param_values,
            'precisions': precisions,
            'times': times,
            'initial_precision': initial_precision,
            'final_precision': final_precision,
            'precision_change': precision_change,
            'precision_improved': precision_improved,
            'precision_worsened': precision_worsened,
            'precision_stable': precision_stable,
            'cost_multiplier': cost_multiplier,
            'initial_time': times[0],
            'final_time': times[-1]
        })
    
    return example_analyses

def generate_sensitivity_analysis():
    """Generate detailed sensitivity analysis for all benchmarks."""
    
    benchmarks = [
        "basic", "nondet", "nested", "multi-effect",
        "recursion", "state-handler", "complex-flow", "nested-nondet"
    ]
    analyses = ["dmcfa", "dmcfae", "kcfa"]
    
    output_file = OUTPUT_DIR / "parameter_sensitivity_analysis.txt"
    
    with open(output_file, 'w') as f:
        f.write("=" * 90 + "\n")
        f.write("PARAMETER SENSITIVITY ANALYSIS - PRECISION vs COST\n")
        f.write("=" * 90 + "\n\n")
        
        f.write("This analysis shows how individual examples' precision changes as context\n")
        f.write("sensitivity parameters (D, M(K), K) increase, and the associated cost.\n\n")
        
        for benchmark in benchmarks:
            f.write("\n" + "=" * 90 + "\n")
            f.write(f"BENCHMARK: {benchmark.upper()}\n")
            f.write("=" * 90 + "\n")
            
            for analysis in analyses:
                try:
                    results = load_all_results(benchmark, analysis)
                    if not results:
                        continue
                    
                    # Determine parameter to analyze
                    if analysis == "kcfa":
                        param_name = "K"
                    else:
                        param_name = "M(K)"  # Analyze M(K) as primary parameter
                    
                    f.write(f"\n{analysis.upper()} - {param_name} Parameter Sensitivity\n")
                    f.write("-" * 90 + "\n")
                    
                    analyses_result = analyze_parameter_sensitivity(results, param_name)
                    
                    if not analyses_result:
                        f.write("(No data)\n")
                        continue
                    
                    # Summary statistics
                    improved = sum(1 for a in analyses_result if a['precision_improved'])
                    worsened = sum(1 for a in analyses_result if a['precision_worsened'])
                    stable = sum(1 for a in analyses_result if a['precision_stable'])
                    
                    f.write(f"\nPrecision Changes ({len(analyses_result)} examples):\n")
                    f.write(f"  Improved: {improved} ({100*improved/len(analyses_result):.1f}%)\n")
                    f.write(f"  Worsened: {worsened} ({100*worsened/len(analyses_result):.1f}%)\n")
                    f.write(f"  Stable:   {stable} ({100*stable/len(analyses_result):.1f}%)\n")
                    
                    # Cost statistics
                    multipliers = [a['cost_multiplier'] for a in analyses_result]
                    f.write(f"\nCost Multiplier ({param_name} min to max):\n")
                    f.write(f"  Mean:     {mean(multipliers):.2f}x\n")
                    f.write(f"  Min:      {min(multipliers):.2f}x\n")
                    f.write(f"  Max:      {max(multipliers):.2f}x\n")
                    
                    # Examples with precision improvement
                    if improved > 0:
                        f.write(f"\nExamples with Precision Improvement:\n")
                        for a in sorted(analyses_result, 
                                      key=lambda x: x['precision_change'],
                                      reverse=True):
                            if a['precision_improved']:
                                f.write(f"  {a['example']:<50}")
                                f.write(f" {a['initial_precision']:.2f} → {a['final_precision']:.2f}")
                                f.write(f" (Δ+{a['precision_change']:.2f})")
                                f.write(f" [{a['cost_multiplier']:.2f}x cost]\n")
                    
                    # Examples with precision loss
                    if worsened > 0:
                        f.write(f"\nExamples with Precision Loss:\n")
                        for a in sorted(analyses_result,
                                      key=lambda x: x['precision_change']):
                            if a['precision_worsened']:
                                f.write(f"  {a['example']:<50}")
                                f.write(f" {a['initial_precision']:.2f} → {a['final_precision']:.2f}")
                                f.write(f" (Δ{a['precision_change']:.2f})")
                                f.write(f" [{a['cost_multiplier']:.2f}x cost]\n")
                    
                    # Examples with largest cost but no precision improvement
                    no_improvement = [a for a in analyses_result 
                                     if a['precision_stable'] and a['final_precision'] < 1.0]
                    if no_improvement:
                        f.write(f"\nHigh Cost, No Improvement (precision already limited):\n")
                        for a in sorted(no_improvement,
                                      key=lambda x: x['cost_multiplier'],
                                      reverse=True)[:3]:
                            f.write(f"  {a['example']:<50}")
                            f.write(f" precision={a['final_precision']:.2f}")
                            f.write(f" [{a['cost_multiplier']:.2f}x cost]\n")
                    
                except Exception as e:
                    f.write(f"Error analyzing {analysis}: {e}\n")
    
    print(f"✓ Parameter sensitivity analysis: {output_file}")
    return output_file

def generate_precision_cost_tradeoff():
    """Analyze precision vs cost trade-off patterns."""
    
    benchmarks = [
        "basic", "nondet", "nested", "multi-effect",
        "recursion", "state-handler", "complex-flow", "nested-nondet"
    ]
    analyses = ["dmcfa", "dmcfae", "kcfa"]
    
    output_file = OUTPUT_DIR / "precision_cost_tradeoff.txt"
    
    with open(output_file, 'w') as f:
        f.write("=" * 90 + "\n")
        f.write("PRECISION vs COST TRADE-OFF ANALYSIS\n")
        f.write("=" * 90 + "\n\n")
        
        f.write("Shows examples where increased context sensitivity achieves precision improvement\n")
        f.write("and those where it provides no benefit (precision-limited).\n\n")
        
        for benchmark in benchmarks:
            f.write("\n" + "=" * 90 + "\n")
            f.write(f"BENCHMARK: {benchmark.upper()}\n")
            f.write("=" * 90 + "\n")
            
            for analysis in analyses:
                try:
                    results = load_all_results(benchmark, analysis)
                    if not results:
                        continue
                    
                    param_name = "K" if analysis == "kcfa" else "M(K)"
                    
                    f.write(f"\n{analysis.upper()}\n")
                    f.write("-" * 90 + "\n")
                    
                    analyses_result = analyze_parameter_sensitivity(results, param_name)
                    
                    # Categorize examples
                    perfect = [a for a in analyses_result 
                              if a['final_precision'] == 1.0]
                    improvable = [a for a in analyses_result
                                 if a['precision_improved'] and a['final_precision'] < 1.0]
                    limited = [a for a in analyses_result
                              if a['precision_stable'] and a['final_precision'] < 1.0]
                    
                    f.write(f"\nPrecision Categories:\n")
                    f.write(f"  Perfect (100%):           {len(perfect):3} examples\n")
                    f.write(f"  Improvable (gains):       {len(improvable):3} examples\n")
                    f.write(f"  Limited (no gains):       {len(limited):3} examples\n")
                    
                    if improvable:
                        f.write(f"\nImprovable Examples (precision increases with sensitivity):\n")
                        for a in sorted(improvable,
                                      key=lambda x: x['precision_change'],
                                      reverse=True)[:5]:
                            f.write(f"  {a['example']:<45}")
                            f.write(f" {a['initial_precision']:.2f}→{a['final_precision']:.2f}")
                            f.write(f" [{a['cost_multiplier']:.2f}x]\n")
                    
                    if limited and len(limited) > 0:
                        # Find most expensive ones with no improvement
                        expensive_limited = sorted(limited,
                                                 key=lambda x: x['cost_multiplier'],
                                                 reverse=True)[:3]
                        f.write(f"\nPrecision-Limited Examples (high cost, no precision gain):\n")
                        for a in expensive_limited:
                            f.write(f"  {a['example']:<45}")
                            f.write(f" precision={a['final_precision']:.2f}")
                            f.write(f" [{a['cost_multiplier']:.2f}x cost]\n")
                
                except Exception as e:
                    f.write(f"Error: {e}\n")
    
    print(f"✓ Precision/cost tradeoff analysis: {output_file}")
    return output_file

def generate_parameter_effectiveness():
    """Analyze which parameter (D or M(K)) is most effective."""
    
    benchmarks = [
        "basic", "nondet", "nested", "multi-effect",
        "recursion", "state-handler", "complex-flow", "nested-nondet"
    ]
    
    output_file = OUTPUT_DIR / "parameter_effectiveness.txt"
    
    with open(output_file, 'w') as f:
        f.write("=" * 90 + "\n")
        f.write("PARAMETER EFFECTIVENESS - D vs M(K) Impact\n")
        f.write("=" * 90 + "\n\n")
        
        f.write("For DMCFA and DMCFAE, compares the impact of D (demand) vs M(K) (context).\n")
        f.write("Shows which parameter drives precision improvement.\n\n")
        
        for benchmark in benchmarks:
            try:
                results = load_all_results(benchmark, "dmcfa")
                if not results:
                    continue
                
                f.write("\n" + "-" * 90 + "\n")
                f.write(f"{benchmark.upper()}\n")
                f.write("-" * 90 + "\n")
                
                # Analyze D sensitivity
                d_analysis = analyze_parameter_sensitivity(results, "D")
                d_improved = sum(1 for a in d_analysis if a['precision_improved'])
                d_avg_cost = mean([a['cost_multiplier'] for a in d_analysis])
                
                # Analyze M(K) sensitivity
                mk_analysis = analyze_parameter_sensitivity(results, "M(K)")
                mk_improved = sum(1 for a in mk_analysis if a['precision_improved'])
                mk_avg_cost = mean([a['cost_multiplier'] for a in mk_analysis])
                
                f.write(f"\nD Parameter:\n")
                f.write(f"  Examples with precision improvement: {d_improved}/{len(d_analysis)}\n")
                f.write(f"  Average cost multiplier: {d_avg_cost:.2f}x\n")
                
                f.write(f"\nM(K) Parameter:\n")
                f.write(f"  Examples with precision improvement: {mk_improved}/{len(mk_analysis)}\n")
                f.write(f"  Average cost multiplier: {mk_avg_cost:.2f}x\n")
                
                # Comparison
                if d_improved == 0 and mk_improved == 0:
                    f.write(f"\n→ Neither parameter improves precision (precision-limited benchmark)\n")
                elif d_improved == 0:
                    f.write(f"\n→ M(K) is the only effective parameter for precision improvement\n")
                elif mk_improved == 0:
                    f.write(f"\n→ D is the only effective parameter for precision improvement\n")
                else:
                    if mk_improved > d_improved:
                        f.write(f"\n→ M(K) more effective ({mk_improved} vs {d_improved} examples)\n")
                    elif d_improved > mk_improved:
                        f.write(f"\n→ D more effective ({d_improved} vs {mk_improved} examples)\n")
                    else:
                        f.write(f"\n→ Both parameters equally effective\n")
                
            except Exception as e:
                f.write(f"Error: {e}\n")
    
    print(f"✓ Parameter effectiveness analysis: {output_file}")
    return output_file

if __name__ == "__main__":
    print("\nGenerating sensitivity analyses...\n")
    
    generate_sensitivity_analysis()
    generate_precision_cost_tradeoff()
    generate_parameter_effectiveness()
    
    print("\n✓ All sensitivity analyses generated to benchmarks/analysis/exports/")
