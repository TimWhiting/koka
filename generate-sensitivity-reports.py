#!/usr/bin/env python3
"""
Generate detailed metric comparison tables for sensitivity parameters.
Shows how NEval, NApply, and precision change with D and M(K).
"""

import json
from pathlib import Path
from typing import Dict, List
from collections import defaultdict

ANALYSIS_JSON = Path("benchmarks/analysis/suite-analysis.json")
EXPORT_DIR = Path("benchmarks/analysis/exports")

def load_suite_files_from_results() -> List[str]:
    """Load benchmark names by scanning the results directory structure."""
    benchmarks = set()
    RESULTS_BASE = Path("benchmarks/results")
    
    if not RESULTS_BASE.exists():
        return []
        
    for d_dir in RESULTS_BASE.iterdir():
        if not d_dir.is_dir(): continue
        for m_dir in d_dir.iterdir():
            if not m_dir.is_dir(): continue
            for csv_file in m_dir.rglob("*.csv"):
                rel_path = csv_file.relative_to(m_dir)
                benchmarks.add(str(rel_path.with_suffix('')))
                
    return sorted(list(benchmarks))

SUITE_FILES = load_suite_files_from_results()

def load_json_analysis() -> Dict:
    """Load the analysis JSON file."""
    if ANALYSIS_JSON.exists():
        with open(ANALYSIS_JSON, 'r') as f:
            return json.load(f)
    return {}

def generate_d_sensitivity_report():
    """Generate report on D sensitivity across benchmarks."""
    analysis = load_json_analysis()
    
    output_file = EXPORT_DIR / "d_sensitivity_report.txt"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_file, 'w') as f:
        f.write("=" * 100 + "\n")
        f.write("D (DEMAND LEVEL) SENSITIVITY ANALYSIS\n")
        f.write("=" * 100 + "\n\n")
        
        f.write("This report analyzes how varying D (demand-level sensitivity) affects:\n")
        f.write("- Execution time\n")
        f.write("- Number of evaluations (NEval)\n")
        f.write("- Number of applications (NApply)\n\n")
        
        for benchmark in SUITE_FILES:
            if benchmark not in analysis or 'dmcfa' not in analysis[benchmark]:
                continue
            
            dmcfa = analysis[benchmark]['dmcfa']
            
            f.write("\n" + "=" * 80 + "\n")
            f.write(f"{benchmark.upper()}\n")
            f.write("=" * 80 + "\n\n")
            
            d_trends = dmcfa.get('d_trends', {})
            if not d_trends:
                f.write("No D trend data available.\n")
                continue
            
            # Print header
            f.write(f"{'D':>5} {'Time(s)':>12} {'TimeChg%':>10} {'NEval':>10} {'NApply':>10}\n")
            f.write("-" * 60 + "\n")
            
            prev_time = None
            for d in sorted(d_trends.keys(), key=lambda x: int(x)):
                stats = d_trends[d]
                time_val = stats.get('mean', 0)
                
                time_str = f"{time_val:.4f}"
                
                if prev_time is not None and prev_time > 0:
                    time_change = ((time_val - prev_time) / prev_time) * 100
                    time_chg_str = f"{time_change:+.1f}%"
                else:
                    time_chg_str = "base"
                
                f.write(f"{d:>5} {time_str:>12} {time_chg_str:>10}\n")
                prev_time = time_val
            
            f.write("\n")
    
    print(f"D sensitivity report: {output_file}")

def generate_mk_sensitivity_report():
    """Generate report on M(K)/K sensitivity across benchmarks."""
    analysis = load_json_analysis()
    
    output_file = EXPORT_DIR / "mk_sensitivity_report.txt"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_file, 'w') as f:
        f.write("=" * 100 + "\n")
        f.write("M(K) / K (CONTEXT SENSITIVITY) ANALYSIS\n")
        f.write("=" * 100 + "\n\n")
        
        f.write("This report analyzes how varying M(K) / K affects:\n")
        f.write("- Execution time\n")
        f.write("- Time multiplier (relative to minimum)\n")
        f.write("- Analysis type comparison\n\n")
        
        for benchmark in SUITE_FILES:
            if benchmark not in analysis:
                continue
            
            f.write("\n" + "=" * 80 + "\n")
            f.write(f"{benchmark.upper()}\n")
            f.write("=" * 80 + "\n\n")
            
            # Compare DMCFA vs DMCFAE vs KCFA
            analyses_present = list(analysis[benchmark].keys())
            
            if 'dmcfa' in analyses_present:
                dmcfa = analysis[benchmark]['dmcfa']
                m_trends = dmcfa.get('m_trends', {})
                
                f.write("DMCFA M(K) Scaling:\n")
                f.write(f"{'M(K)':>5} {'Time(s)':>12} {'Multiplier':>12} {'Increase%':>10}\n")
                f.write("-" * 60 + "\n")
                
                times_list = [m_trends[str(m)].get('mean', 0) for m in sorted(m_trends.keys(), key=int)]
                min_time = min(times_list) if times_list else 1
                
                prev_time = None
                for m in sorted(m_trends.keys(), key=lambda x: int(x)):
                    stats = m_trends[m]
                    time_val = stats.get('mean', 0)
                    multiplier = time_val / min_time if min_time > 0 else 1
                    
                    if prev_time is not None and prev_time > 0:
                        increase = ((time_val - prev_time) / prev_time) * 100
                        increase_str = f"{increase:+.1f}%"
                    else:
                        increase_str = "base"
                    
                    f.write(f"{m:>5} {time_val:>12.4f} {multiplier:>12.2f}x {increase_str:>10}\n")
                    prev_time = time_val
                
                f.write("\n")
            
            if 'kcfa' in analyses_present:
                kcfa = analysis[benchmark]['kcfa']
                k_trends = kcfa.get('m_trends', {})  # KCFA uses m_trends for K values
                
                f.write("KCFA K Scaling:\n")
                f.write(f"{'K':>5} {'Time(s)':>12} {'Multiplier':>12} {'Increase%':>10}\n")
                f.write("-" * 60 + "\n")
                
                times_list = [k_trends[str(k)].get('mean', 0) for k in sorted(k_trends.keys(), key=int)]
                min_time = min(times_list) if times_list else 1
                
                prev_time = None
                for k in sorted(k_trends.keys(), key=lambda x: int(x)):
                    stats = k_trends[k]
                    time_val = stats.get('mean', 0)
                    multiplier = time_val / min_time if min_time > 0 else 1
                    
                    if prev_time is not None and prev_time > 0:
                        increase = ((time_val - prev_time) / prev_time) * 100
                        increase_str = f"{increase:+.1f}%"
                    else:
                        increase_str = "base"
                    
                    f.write(f"{k:>5} {time_val:>12.4f} {multiplier:>12.2f}x {increase_str:>10}\n")
                    prev_time = time_val
                
                f.write("\n")
    
    print(f"M(K)/K sensitivity report: {output_file}")

def generate_cost_summary_table():
    """Generate a summary table of sensitivity costs."""
    analysis = load_json_analysis()
    
    output_file = EXPORT_DIR / "sensitivity_cost_summary.txt"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_file, 'w') as f:
        f.write("=" * 120 + "\n")
        f.write("SENSITIVITY COST SUMMARY - D and M(K) Impact Comparison\n")
        f.write("=" * 120 + "\n\n")
        
        f.write("D IMPACT (Demand Level): Time multiplier from D=1 to D=4\n")
        f.write("-" * 120 + "\n")
        f.write(f"{'Benchmark':<20} {'D Min Time':>15} {'D Max Time':>15} {'D Multiplier':>15} {'D Impact':>15}\n")
        f.write("-" * 120 + "\n")
        
        for benchmark in SUITE_FILES:
            if benchmark not in analysis or 'dmcfa' not in analysis[benchmark]:
                f.write(f"{benchmark:<20} {'N/A':>15}\n")
                continue
            
            dmcfa = analysis[benchmark]['dmcfa']
            d_trends = dmcfa.get('d_trends', {})
            
            if not d_trends:
                f.write(f"{benchmark:<20} {'No data':>15}\n")
                continue
            
            times = [d_trends[str(d)].get('mean', 0) for d in sorted(d_trends.keys(), key=int)]
            min_time = min(times) if times else 0
            max_time = max(times) if times else 0
            multiplier = max_time / min_time if min_time > 0 else 1
            impact = "LOW" if multiplier < 1.2 else "MODERATE" if multiplier < 2 else "HIGH"
            
            f.write(f"{benchmark:<20} {min_time:>15.4f} {max_time:>15.4f} {multiplier:>15.2f}x {impact:>15}\n")
        
        f.write("\n")
        f.write("M(K) IMPACT (Context Sensitivity): Time multiplier from M(K)=1 to M(K)=6\n")
        f.write("-" * 120 + "\n")
        f.write(f"{'Benchmark':<20} {'M Min Time':>15} {'M Max Time':>15} {'M Multiplier':>15} {'M Impact':>15}\n")
        f.write("-" * 120 + "\n")
        
        for benchmark in SUITE_FILES:
            if benchmark not in analysis or 'dmcfa' not in analysis[benchmark]:
                f.write(f"{benchmark:<20} {'N/A':>15}\n")
                continue
            
            dmcfa = analysis[benchmark]['dmcfa']
            m_trends = dmcfa.get('m_trends', {})
            
            if not m_trends:
                f.write(f"{benchmark:<20} {'No data':>15}\n")
                continue
            
            times = [m_trends[str(m)].get('mean', 0) for m in sorted(m_trends.keys(), key=int)]
            min_time = min(times) if times else 0
            max_time = max(times) if times else 0
            multiplier = max_time / min_time if min_time > 0 else 1
            impact = "LOW" if multiplier < 1.5 else "MODERATE" if multiplier < 10 else "HIGH"
            
            f.write(f"{benchmark:<20} {min_time:>15.4f} {max_time:>15.4f} {multiplier:>15.2f}x {impact:>15}\n")
        
        f.write("\n")
        f.write("INTERPRETATION:\n")
        f.write("- LOW impact: < 1.2x multiplier for D, < 1.5x for M(K)\n")
        f.write("- MODERATE impact: 1.2-2x for D, 1.5-10x for M(K)\n")
        f.write("- HIGH impact: > 2x for D, > 10x for M(K)\n")
    
    print(f"Sensitivity cost summary: {output_file}")

def main():
    """Main entry point."""
    print("Generating sensitivity metric reports...\n")
    
    analysis = load_json_analysis()
    if not analysis:
        print("Error: Could not load analysis data")
        return
    
    generate_d_sensitivity_report()
    generate_mk_sensitivity_report()
    generate_cost_summary_table()
    
    print(f"\n✓ All reports saved to {EXPORT_DIR}")

if __name__ == "__main__":
    main()
