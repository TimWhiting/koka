#!/usr/bin/env python3
"""
Generate comparison graphs for sensitivity parameter costs across analyses.
Supports per-benchmark-set aggregates and all-aggregate graphs.
"""

import json
import sys
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from pathlib import Path
from typing import Dict, List, Tuple, Set
from collections import defaultdict

ANALYSIS_JSON = Path("benchmarks/analysis/suite-analysis.json")
RESULTS_BASE = Path("benchmarks/results")
EXPORT_DIR = Path("benchmarks/analysis/graphs")

# Define benchmark sets
BENCHMARK_SETS = {
    "suite": ["basic", "nondet", "nested", "multi-effect", "recursion", "state-handler", "complex-flow", "nested-nondet"],
    "handlers": ["ambient", "nim", "unix", "vec", "yield"],
    "rosetta": ["jump-anywhere", "monads-writer", "pr4rings"]
}

def load_suite_files() -> List[str]:
    """Load benchmark names from suite, handlers, and rosetta directories."""
    benchmarks = set()
    
    # Get benchmarks from suite
    suite_dir = RESULTS_BASE / "suite"
    if suite_dir.exists():
        benchmarks.update(d.name for d in suite_dir.iterdir() if d.is_dir())
    
    # Get benchmarks from handlers
    handlers_dir = RESULTS_BASE / "handlers"
    if handlers_dir.exists():
        benchmarks.update(d.name for d in handlers_dir.iterdir() if d.is_dir())
    
    # Get benchmarks from rosetta (recursively)
    rosetta_dir = RESULTS_BASE / "rosetta"
    if rosetta_dir.exists():
        # Look for directories that contain CSV files
        for p in rosetta_dir.rglob("*.csv"):
            # Extract benchmark name from parent directory
            parent_dir = p.parent
            benchmarks.add(parent_dir.name)
    
    return sorted(benchmarks)

SUITE_FILES = load_suite_files()

def get_benchmark_set(benchmark: str) -> str:
    """Determine which set a benchmark belongs to."""
    for set_name, benchmarks in BENCHMARK_SETS.items():
        if benchmark in benchmarks:
            return set_name
    return "unknown"

def get_benchmarks_for_set(set_name: str) -> List[str]:
    """Get benchmarks for a specific set."""
    return BENCHMARK_SETS.get(set_name, [])

# Benchmark grouping
BENCHMARK_GROUPS = {}  # Empty - each benchmark gets its own folder

def get_benchmark_group(benchmark: str) -> str:
    """Get the group name for a benchmark (just the benchmark name itself)."""
    return benchmark

# Analysis configurations
DMCFA_ANALYSES = ["dmcfa", "dmcfae"]
COMPARABLE_M_K = {"dmcfa": "kcfa", "dmcfae": "kcfa"}  # Map M(K) analyses to K analyses


def load_json_analysis() -> Dict:
    """Load the analysis JSON file."""
    if ANALYSIS_JSON.exists():
        with open(ANALYSIS_JSON, 'r') as f:
            return json.load(f)
    return {}

def extract_d_trends(analysis_data: Dict) -> Dict[str, List[Tuple[int, float]]]:
    """Extract D trends for a benchmark across analyses.
    
    Returns dict mapping analysis_key to list of (D, avg_time) tuples.
    """
    trends = {}
    for analysis_key, data in analysis_data.items():
        if 'd_trends' in data:
            d_trend = [(int(d), data['d_trends'][str(d)].get('mean', 0))
                      for d in sorted(data.get('d_values', []))]
            trends[analysis_key] = d_trend
    return trends

def extract_m_trends(analysis_data: Dict) -> Dict[str, List[Tuple[int, float]]]:
    """Extract M(K) trends for a benchmark across analyses.
    
    For DMCFA analyses, uses 'm_trends'.
    For KCFA, maps K values to comparable scale.
    """
    trends = {}
    for analysis_key, data in analysis_data.items():
        if 'm_trends' in data:
            m_trend = [(int(m), data['m_trends'][str(m)].get('mean', 0))
                      for m in sorted(data.get('m_values', []))]
            trends[analysis_key] = m_trend
    return trends

def extract_precision_trends(analysis_data: Dict) -> Dict[str, List[Tuple[int, float]]]:
    """Extract precision across M(K)/K values.
    
    Returns dict mapping analysis to list of (param_value, precision) tuples.
    For DMCFA this is based on M(K), for KCFA on K.
    """
    precisions = {}
    for analysis_key, data in analysis_data.items():
        if 'm_trends' in data or 'k_trends' in data:
            trends_data = data.get('m_trends', data.get('k_trends', {}))
            precision_trend = [
                (int(param), trends_data[str(param)].get('mean', 0))
                for param in sorted(data.get('m_values', data.get('k_values', [])))
            ]
            precisions[analysis_key] = precision_trend
    return precisions

def get_benchmark_output_dir(benchmark: str) -> Path:
    """Get the output directory for a benchmark's graphs."""
    group = get_benchmark_group(benchmark)
    return EXPORT_DIR / group

def get_aggregate_output_dir(set_name: str) -> Path:
    """Get the output directory for aggregate graphs for a benchmark set.
    
    Args:
        set_name: 'suite', 'handlers', 'rosetta', or 'all' for all-aggregate
    """
    if set_name == "all":
        return EXPORT_DIR / "aggregated"
    else:
        return EXPORT_DIR / f"aggregated_{set_name}"

def plot_d_comparison(benchmark: str, analysis: Dict):
    """Plot D cost comparison across DMCFA analyses."""
    d_trends = extract_d_trends(analysis)
    
    if not d_trends:
        return
    
    fig, ax = plt.subplots(figsize=(10, 6))
    
    colors = {'dmcfa': '#2E86AB', 'dmcfae': '#A23B72'}
    
    for analysis_key in DMCFA_ANALYSES:
        if analysis_key in d_trends:
            d_vals, times = zip(*d_trends[analysis_key])
            ax.plot(d_vals, times, marker='o', label=analysis_key.upper(),
                   color=colors.get(analysis_key, '#000000'), linewidth=2, markersize=8)
    
    ax.set_xlabel('D (Demand Level)', fontsize=12, fontweight='bold')
    ax.set_ylabel('Time (seconds)', fontsize=12, fontweight='bold')
    ax.set_title(f'{benchmark.replace("-", " ").title()}: Cost of Increasing D', 
                fontsize=14, fontweight='bold')
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    ax.set_xticks(range(0, 6))
    
    output_file = get_benchmark_output_dir(benchmark) / "d_comparison.png"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"Generated: {output_file}")

def plot_d_comparison_by_mk(benchmark: str, analysis: Dict):
    """Plot M(K) cost at each D level - colors for analyses, line styles for D values."""
    analyses_to_plot = ['dmcfa', 'dmcfae', 'kcfa']
    analyses_available = [a for a in analyses_to_plot if a in analysis]
    
    if not analyses_available:
        return
    
    fig, ax = plt.subplots(figsize=(13, 7))
    
    # Colors for each analysis
    colors = {'dmcfa': '#2E86AB', 'dmcfae': '#A23B72', 'kcfa': '#F18F01'}
    
    # Line styles for each D value
    linestyles = {1: '-', 2: '--', 3: '-.', 4: ':'}
    
    # For DMCFA and DMCFAE: plot one line per D
    for analysis_key in ['dmcfa', 'dmcfae']:
        if analysis_key not in analyses_available:
            continue
            
        analysis_data = analysis[analysis_key]
        if 'd_m_trends' not in analysis_data:
            continue
        
        d_values = sorted(analysis_data.get('d_values', []))
        
        # Plot one line per D for this analysis
        for d_val in d_values:
            d_key = str(d_val)
            if d_key in analysis_data['d_m_trends']:
                m_results = analysis_data['d_m_trends'][d_key]
                m_vals = sorted([int(m) for m in m_results.keys()])
                times = []
                ci_lower = []
                ci_upper = []
                
                # Calculate 95% confidence interval using stdev
                for m in m_vals:
                    stats = m_results[str(m)]
                    mean = stats.get('mean', 0)
                    count = stats.get('count', 1)
                    stdev = stats.get('stdev', 0)
                    
                    # 95% CI ≈ mean ± 1.96 * (stdev / sqrt(n))
                    margin = 1.96 * (stdev / (count ** 0.5)) if count > 0 else 0
                    
                    times.append(mean)
                    ci_lower.append(max(0, mean - margin))
                    ci_upper.append(mean + margin)
                
                # Plot line with color for analysis, style for D
                linestyle = linestyles.get(d_val, '-')
                label = f'{analysis_key.upper()} D={d_val}'
                ax.plot(m_vals, times, marker='o', label=label,
                       color=colors[analysis_key], linestyle=linestyle,
                       linewidth=2, markersize=6, alpha=0.85)
                
                # Add confidence interval as shaded region
                ax.fill_between(m_vals, ci_lower, ci_upper,
                               color=colors[analysis_key], alpha=0.08)
    
    # For KCFA: single line (no D dimension)
    if 'kcfa' in analyses_available:
        kcfa_data = analysis['kcfa']
        if 'm_trends' in kcfa_data:
            m_results = kcfa_data['m_trends']
            m_vals = sorted([int(m) for m in m_results.keys()])
            times = []
            ci_lower = []
            ci_upper = []
            
            for m in m_vals:
                stats = m_results[str(m)]
                mean = stats.get('mean', 0)
                count = stats.get('count', 1)
                stdev = stats.get('stdev', 0)
                
                margin = 1.96 * (stdev / (count ** 0.5)) if count > 0 else 0
                
                times.append(mean)
                ci_lower.append(max(0, mean - margin))
                ci_upper.append(mean + margin)
            
            # Plot KCFA as single line with solid style
            ax.plot(m_vals, times, marker='s', label='KCFA',
                   color=colors['kcfa'], linestyle='-',
                   linewidth=2.5, markersize=7, alpha=0.85)
            
            # Add confidence interval as shaded region
            ax.fill_between(m_vals, ci_lower, ci_upper,
                           color=colors['kcfa'], alpha=0.08)
    
    ax.set_xlabel('M(K) / K (Context Sensitivity)', fontsize=12, fontweight='bold')
    ax.set_ylabel('Time (seconds)', fontsize=12, fontweight='bold')
    ax.set_title(f'{benchmark.replace("-", " ").title()}: Context Sensitivity Cost Across Analyses (with 95% CI)', 
                fontsize=14, fontweight='bold')
    ax.legend(fontsize=9, loc='best', ncol=3)
    ax.grid(True, alpha=0.3)
    
    output_file = get_benchmark_output_dir(benchmark) / "mk_by_d_comparison.png"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"Generated: {output_file}")

def plot_m_k_comparison(benchmark: str, analysis: Dict):
    """Plot M(K)/K cost comparison across analyses."""
    m_trends = extract_m_trends(analysis)
    
    if not m_trends:
        return
    
    fig, ax = plt.subplots(figsize=(10, 6))
    
    colors = {'dmcfa': '#2E86AB', 'dmcfae': '#A23B72', 'kcfa': '#F18F01'}
    
    # Plot DMCFA analyses with M(K)
    for analysis_key in DMCFA_ANALYSES:
        if analysis_key in m_trends:
            m_vals, times = zip(*m_trends[analysis_key])
            ax.plot(m_vals, times, marker='o', label=f'{analysis_key.upper()} M(K)',
                   color=colors.get(analysis_key, '#000000'), linewidth=2, markersize=8)
    
    # Plot KCFA with K (if available)
    if 'kcfa' in analysis:
        kcfa_data = analysis['kcfa']
        if 'm_trends' in kcfa_data:
            k_vals, times = zip(*extract_m_trends({'kcfa': kcfa_data})['kcfa'])
            ax.plot(k_vals, times, marker='s', label='KCFA K',
                   color=colors['kcfa'], linewidth=2, markersize=8, linestyle='--')
    
    ax.set_xlabel('M(K) / K (Context Sensitivity)', fontsize=12, fontweight='bold')
    ax.set_ylabel('Time (seconds)', fontsize=12, fontweight='bold')
    ax.set_title(f'{benchmark.replace("-", " ").title()}: Cost of Increasing M(K)/K', 
                fontsize=14, fontweight='bold')
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    ax.set_xticks(range(0, 12))
    
    output_file = get_benchmark_output_dir(benchmark) / "mk_comparison.png"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"Generated: {output_file}")

def plot_mk_overlay_dmcfa_kcfa(benchmark: str, analysis: Dict):
    """Plot M(K)/K comparison with DMCFA and KCFA overlaid."""
    if 'dmcfa' not in analysis or 'kcfa' not in analysis:
        return
    
    fig, ax = plt.subplots(figsize=(10, 6))
    
    colors = {'dmcfa': '#2E86AB', 'kcfa': '#F18F01'}
    
    # Plot DMCFA with M(K)
    dmcfa_data = analysis['dmcfa']
    if 'm_trends' in dmcfa_data:
        m_trends = extract_m_trends({'dmcfa': dmcfa_data})
        if 'dmcfa' in m_trends:
            m_vals, times = zip(*m_trends['dmcfa'])
            ax.plot(m_vals, times, marker='o', label='DMCFA M(K)',
                   color=colors['dmcfa'], linewidth=2.5, markersize=8)
    
    # Plot KCFA with K
    kcfa_data = analysis['kcfa']
    if 'm_trends' in kcfa_data:
        k_trends = extract_m_trends({'kcfa': kcfa_data})
        if 'kcfa' in k_trends:
            k_vals, times = zip(*k_trends['kcfa'])
            ax.plot(k_vals, times, marker='s', label='KCFA K',
                   color=colors['kcfa'], linewidth=2.5, markersize=8, linestyle='--')
    
    ax.set_xlabel('Context Sensitivity Parameter (M(K) or K)', fontsize=12, fontweight='bold')
    ax.set_ylabel('Time (seconds)', fontsize=12, fontweight='bold')
    ax.set_title(f'{benchmark.replace("-", " ").title()}: DMCFA vs KCFA Time Cost', 
                fontsize=14, fontweight='bold')
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    
    output_file = get_benchmark_output_dir(benchmark) / "mk_overlay_dmcfa_kcfa.png"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"Generated: {output_file}")

def plot_precision_vs_cost(benchmark: str, analysis: Dict):
    """Plot precision improvement vs time cost."""
    # Get precision data - need to compute from raw results or estimate
    # For now, show time vs M(K)/K across analyses
    m_trends = extract_m_trends(analysis)
    
    if not m_trends or len(m_trends) < 2:
        return
    
    fig, ax = plt.subplots(figsize=(11, 7))
    
    colors = {'dmcfa': '#2E86AB', 'dmcfae': '#A23B72', 'kcfa': '#F18F01'}
    
    for analysis_key in sorted(m_trends.keys()):
        m_vals, times = zip(*m_trends[analysis_key])
        ax.plot(m_vals, times, marker='o', label=analysis_key.upper(),
               color=colors.get(analysis_key, '#000000'), linewidth=2.5, markersize=9)
    
    ax.set_xlabel('Context Sensitivity Parameter (M(K) or K)', fontsize=12, fontweight='bold')
    ax.set_ylabel('Execution Time (seconds)', fontsize=12, fontweight='bold')
    ax.set_title(f'{benchmark.replace("-", " ").title()}: Time Cost vs Context Sensitivity', 
                fontsize=14, fontweight='bold')
    ax.legend(fontsize=11, loc='best')
    ax.grid(True, alpha=0.3)
    
    output_file = get_benchmark_output_dir(benchmark) / "precision_vs_cost.png"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"Generated: {output_file}")

def plot_aggregate_mk_by_d():
    """Plot aggregated M(K)/K comparison across all benchmarks with colors for analyses, line styles for D, and CIs."""
    analysis = load_json_analysis()
    
    fig, ax = plt.subplots(figsize=(13, 7))
    
    colors = {'dmcfa': '#2E86AB', 'dmcfae': '#A23B72', 'kcfa': '#F18F01'}
    linestyles = {1: '-', 2: '--', 3: '-.', 4: ':'}
    
    # First plot KCFA (background)
    if SUITE_FILES[0] in analysis and 'kcfa' in analysis[SUITE_FILES[0]]:
        m_to_times = defaultdict(list)
        m_to_stats = defaultdict(list)
        for benchmark in SUITE_FILES:
            if benchmark not in analysis or 'kcfa' not in analysis[benchmark]:
                continue
            
            kcfa_data = analysis[benchmark]['kcfa']
            m_results = kcfa_data.get('m_trends', {})
            for m_str, stats in m_results.items():
                m = int(m_str)
                mean = stats.get('mean', 0)
                m_to_times[m].append(mean)
                m_to_stats[m].append({'stdev': stats.get('stdev', 0), 'count': stats.get('count', 1)})
        
        if m_to_times:
            m_vals = sorted(m_to_times.keys())
            avg_times = []
            ci_lower = []
            ci_upper = []
            
            for m in m_vals:
                times = m_to_times[m]
                avg = sum(times) / len(times)
                avg_times.append(avg)
                
                # Aggregate variance for CI
                variances = [s['stdev'] ** 2 for s in m_to_stats[m]]
                pooled_var = sum(variances) / len(variances) if variances else 0
                mean_var = sum((t - avg) ** 2 for t in times) / len(times)
                total_var = pooled_var + mean_var
                total_stdev = total_var ** 0.5
                
                margin = 1.96 * (total_stdev / (len(SUITE_FILES) ** 0.5))
                ci_lower.append(max(0, avg - margin))
                ci_upper.append(avg + margin)
            
            ax.plot(m_vals, avg_times, marker='s', label='KCFA',
                   color=colors['kcfa'], linestyle='-',
                   linewidth=2.5, markersize=7, alpha=0.7, zorder=1)
            ax.fill_between(m_vals, ci_lower, ci_upper,
                           color=colors['kcfa'], alpha=0.06, zorder=1)
    
    # Then plot DMCFA and DMCFAE (on top)
    for analysis_key in ['dmcfa', 'dmcfae']:
        for benchmark in SUITE_FILES:
            if benchmark not in analysis or analysis_key not in analysis[benchmark]:
                continue
            
            bench_analysis = analysis[benchmark][analysis_key]
            if 'd_m_trends' not in bench_analysis:
                continue
            
            d_values = sorted(bench_analysis.get('d_values', []))
            
            # For first benchmark in this analysis, accumulate D values
            if benchmark == SUITE_FILES[0]:
                d_to_lines = {d: [] for d in d_values}
            
            # Collect m_vals and times for each D
            for d_val in d_values:
                d_key = str(d_val)
                if d_key in bench_analysis['d_m_trends']:
                    m_results = bench_analysis['d_m_trends'][d_key]
                    for m_str, stats in m_results.items():
                        m = int(m_str)
                        mean = stats.get('mean', 0)
                        if (m, d_val) not in [x[0:2] for x in d_to_lines.get(d_val, [])]:
                            d_to_lines[d_val].append((m, mean, []))
        
        # Plot aggregated lines for this analysis
        for d_val in sorted([d for d in d_to_lines if d_to_lines[d]]):
            # Aggregate across benchmarks with stats for CI
            m_to_times = defaultdict(list)
            m_to_stats = defaultdict(list)
            for benchmark in SUITE_FILES:
                if benchmark not in analysis or analysis_key not in analysis[benchmark]:
                    continue
                
                bench_analysis = analysis[benchmark][analysis_key]
                d_key = str(d_val)
                if 'd_m_trends' not in bench_analysis or d_key not in bench_analysis['d_m_trends']:
                    continue
                
                m_results = bench_analysis['d_m_trends'][d_key]
                for m_str, stats in m_results.items():
                    m = int(m_str)
                    mean = stats.get('mean', 0)
                    m_to_times[m].append(mean)
                    m_to_stats[m].append({'stdev': stats.get('stdev', 0), 'count': stats.get('count', 1)})
            
            if m_to_times:
                m_vals = sorted(m_to_times.keys())
                avg_times = []
                ci_lower = []
                ci_upper = []
                
                for m in m_vals:
                    times = m_to_times[m]
                    avg = sum(times) / len(times)
                    avg_times.append(avg)
                    
                    # Aggregate variance for CI
                    variances = [s['stdev'] ** 2 for s in m_to_stats[m]]
                    pooled_var = sum(variances) / len(variances) if variances else 0
                    mean_var = sum((t - avg) ** 2 for t in times) / len(times)
                    total_var = pooled_var + mean_var
                    total_stdev = total_var ** 0.5
                    
                    margin = 1.96 * (total_stdev / (len(SUITE_FILES) ** 0.5))
                    ci_lower.append(max(0, avg - margin))
                    ci_upper.append(avg + margin)
                
                linestyle = linestyles.get(d_val, '-')
                label = f'{analysis_key.upper()} D={d_val}'
                ax.plot(m_vals, avg_times, marker='o', label=label,
                       color=colors[analysis_key], linestyle=linestyle,
                       linewidth=2.5, markersize=7, alpha=0.9, zorder=10)
                ax.fill_between(m_vals, ci_lower, ci_upper,
                               color=colors[analysis_key], alpha=0.12, zorder=10)
    
    ax.set_xlabel('M(K) / K (Context Sensitivity)', fontsize=12, fontweight='bold')
    ax.set_ylabel('Average Time (seconds, log scale)', fontsize=12, fontweight='bold')
    ax.set_yscale('log')
    ax.set_title('Aggregate: Context Sensitivity Cost Across Analyses (with D Levels and 95% CI, log scale)', 
                fontsize=14, fontweight='bold')
    ax.legend(fontsize=9, loc='best', ncol=3)
    ax.grid(True, alpha=0.3, which='both')
    
    output_file = EXPORT_DIR / "aggregate_mk_by_d_comparison.png"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"Generated: {output_file}")

def plot_aggregate_d_cost():
    """Plot D cost across all benchmarks for each analysis with confidence intervals."""
    analysis = load_json_analysis()
    
    fig, axes = plt.subplots(1, 2, figsize=(16, 6))
    
    for idx, analysis_key in enumerate(DMCFA_ANALYSES):
        ax = axes[idx]
        
        # Collect D trends for all benchmarks
        bench_data = defaultdict(dict)
        bench_stats = defaultdict(dict)
        
        for benchmark in SUITE_FILES:
            if benchmark in analysis and analysis_key in analysis[benchmark]:
                d_trends = analysis[benchmark][analysis_key].get('d_trends', {})
                for d_str, stats in d_trends.items():
                    d = int(d_str)
                    if d not in bench_data:
                        bench_data[d] = {}
                        bench_stats[d] = {}
                    bench_data[d][benchmark] = stats.get('mean', 0)
                    bench_stats[d][benchmark] = {'stdev': stats.get('stdev', 0), 'count': stats.get('count', 1)}
        
        # Compute average by D with confidence intervals
        d_vals = sorted(bench_data.keys())
        avg_by_d = []
        ci_lower = []
        ci_upper = []
        
        for d in d_vals:
            times = [bench_data[d].get(b, 0) for b in SUITE_FILES]
            avg = sum(times) / len(times) if times else 0
            avg_by_d.append(avg)
            
            # Aggregate variance for CI
            variances = []
            for b in SUITE_FILES:
                if b in bench_stats[d]:
                    stdev = bench_stats[d][b]['stdev']
                    variances.append(stdev ** 2)
            
            pooled_var = sum(variances) / len(variances) if variances else 0
            mean_var = sum((m - avg) ** 2 for m in times) / len(times)
            total_var = pooled_var + mean_var
            total_stdev = total_var ** 0.5
            
            margin = 1.96 * (total_stdev / (len(SUITE_FILES) ** 0.5))
            ci_lower.append(max(0, avg - margin))
            ci_upper.append(avg + margin)
        
        ax.plot(d_vals, avg_by_d,
               marker='o', linewidth=2.5, markersize=10, color='#2E86AB', alpha=0.85)
        ax.fill_between(d_vals, ci_lower, ci_upper, color='#2E86AB', alpha=0.15)
        
        ax.set_xlabel('D (Demand Level)', fontsize=11, fontweight='bold')
        ax.set_ylabel('Average Time (seconds)', fontsize=11, fontweight='bold')
        ax.set_title(f'{analysis_key.upper()}: Average D Cost Across Suite (with 95% CI)', 
                    fontsize=12, fontweight='bold')
        ax.grid(True, alpha=0.3)
        ax.set_xticks(range(0, 6))
    
    plt.tight_layout()
    output_file = EXPORT_DIR / "aggregate_d_cost.png"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"Generated: {output_file}")

def plot_aggregate_mk_cost_for_set(benchmarks: List[str], set_name: str):
    """Plot M(K)/K cost across specified benchmarks with confidence intervals."""
    analysis = load_json_analysis()
    
    fig, axes = plt.subplots(1, 2, figsize=(16, 6))
    
    # DMCFA analyses on left, KCFA on right
    ax_dmcfa = axes[0]
    ax_kcfa = axes[1]
    
    colors = {'dmcfa': '#2E86AB', 'dmcfae': '#A23B72'}
    
    # DMCFA M(K) comparison with CIs
    for analysis_key in DMCFA_ANALYSES:
        bench_data = defaultdict(dict)
        bench_stats = defaultdict(dict)
        
        for benchmark in benchmarks:
            if benchmark in analysis and analysis_key in analysis[benchmark]:
                m_trends = analysis[benchmark][analysis_key].get('m_trends', {})
                for m_str, stats in m_trends.items():
                    m = int(m_str)
                    if m not in bench_data:
                        bench_data[m] = {}
                        bench_stats[m] = {}
                    bench_data[m][benchmark] = stats.get('mean', 0)
                    bench_stats[m][benchmark] = {'stdev': stats.get('stdev', 0), 'count': stats.get('count', 1)}
        
        # Average across benchmarks with CIs
        m_vals = sorted(bench_data.keys())
        avg_by_m = []
        ci_lower = []
        ci_upper = []
        
        for m in m_vals:
            times = [bench_data[m].get(b, 0) for b in benchmarks]
            avg = sum(times) / len(times) if times else 0
            avg_by_m.append(avg)
            
            variances = []
            for b in benchmarks:
                if b in bench_stats[m]:
                    stdev = bench_stats[m][b]['stdev']
                    variances.append(stdev ** 2)
            
            pooled_var = sum(variances) / len(variances) if variances else 0
            mean_var = sum((t - avg) ** 2 for t in times) / len(times)
            total_var = pooled_var + mean_var
            total_stdev = total_var ** 0.5
            
            margin = 1.96 * (total_stdev / (len(benchmarks) ** 0.5))
            ci_lower.append(max(0, avg - margin))
            ci_upper.append(avg + margin)
        
        ax_dmcfa.plot(m_vals, avg_by_m,
                     marker='o', linewidth=2.5, markersize=10, 
                     label=analysis_key.upper(),
                     color=colors[analysis_key], alpha=0.85)
        ax_dmcfa.fill_between(m_vals, ci_lower, ci_upper,
                             color=colors[analysis_key], alpha=0.15)
    
    ax_dmcfa.set_xlabel('M(K) (Context Sensitivity)', fontsize=11, fontweight='bold')
    ax_dmcfa.set_ylabel('Average Time (seconds)', fontsize=11, fontweight='bold')
    ax_dmcfa.set_title('DMCFA Analyses: Average M(K) Cost Across Suite (with 95% CI)', 
                      fontsize=12, fontweight='bold')
    ax_dmcfa.legend(fontsize=11)
    ax_dmcfa.grid(True, alpha=0.3)
    
    # KCFA K comparison with CIs
    if 'kcfa' in analysis.get(SUITE_FILES[0], {}):
        bench_data = defaultdict(dict)
        bench_stats = defaultdict(dict)
        
        for benchmark in SUITE_FILES:
            if benchmark in analysis and 'kcfa' in analysis[benchmark]:
                m_trends = analysis[benchmark]['kcfa'].get('m_trends', {})
                for m_str, stats in m_trends.items():
                    m = int(m_str)
                    if m not in bench_data:
                        bench_data[m] = {}
                        bench_stats[m] = {}
                    bench_data[m][benchmark] = stats.get('mean', 0)
                    bench_stats[m][benchmark] = {'stdev': stats.get('stdev', 0), 'count': stats.get('count', 1)}
        
        k_vals = sorted(bench_data.keys())
        avg_by_k = []
        ci_lower = []
        ci_upper = []
        
        for k in k_vals:
            times = [bench_data[k].get(b, 0) for b in SUITE_FILES]
            avg = sum(times) / len(times) if times else 0
            avg_by_k.append(avg)
            
            variances = []
            for b in SUITE_FILES:
                if b in bench_stats[k]:
                    stdev = bench_stats[k][b]['stdev']
                    variances.append(stdev ** 2)
            
            pooled_var = sum(variances) / len(variances) if variances else 0
            mean_var = sum((m - avg) ** 2 for m in times) / len(times)
            total_var = pooled_var + mean_var
            total_stdev = total_var ** 0.5
            
            margin = 1.96 * (total_stdev / (len(SUITE_FILES) ** 0.5))
            ci_lower.append(max(0, avg - margin))
            ci_upper.append(avg + margin)
        
        ax_kcfa.plot(k_vals, avg_by_k,
                    marker='s', linewidth=2.5, markersize=10, 
                    label='KCFA',
                    color='#F18F01', alpha=0.85)
        ax_kcfa.fill_between(k_vals, ci_lower, ci_upper, color='#F18F01', alpha=0.15)
        
        ax_kcfa.set_xlabel('K (Context Sensitivity)', fontsize=11, fontweight='bold')
        ax_kcfa.set_ylabel('Average Time (seconds)', fontsize=11, fontweight='bold')
        ax_kcfa.set_title('KCFA: Average K Cost Across Suite (with 95% CI)', 
                         fontsize=12, fontweight='bold')
        ax_kcfa.legend(fontsize=11)
        ax_kcfa.grid(True, alpha=0.3)
    
    plt.tight_layout()
    output_file = EXPORT_DIR / "aggregate_mk_cost.png"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"Generated: {output_file}")

def plot_aggregate_mk_overlay_dmcfa_kcfa():
    """Plot aggregated M(K)/K comparison across all benchmarks with DMCFA and KCFA overlaid (with CIs)."""
    analysis = load_json_analysis()
    
    fig, ax = plt.subplots(figsize=(12, 7))
    
    colors = {'dmcfa': '#2E86AB', 'kcfa': '#F18F01'}
    
    # Collect DMCFA M(K) data across all benchmarks
    dmcfa_bench_data = defaultdict(dict)
    dmcfa_bench_stats = defaultdict(dict)
    for benchmark in SUITE_FILES:
        if benchmark in analysis and 'dmcfa' in analysis[benchmark]:
            m_trends = analysis[benchmark]['dmcfa'].get('m_trends', {})
            for m_str, stats in m_trends.items():
                m = int(m_str)
                if m not in dmcfa_bench_data:
                    dmcfa_bench_data[m] = {}
                    dmcfa_bench_stats[m] = {}
                dmcfa_bench_data[m][benchmark] = stats.get('mean', 0)
                dmcfa_bench_stats[m][benchmark] = {'stdev': stats.get('stdev', 0), 'count': stats.get('count', 1)}
    
    # Collect KCFA K data across all benchmarks
    kcfa_bench_data = defaultdict(dict)
    kcfa_bench_stats = defaultdict(dict)
    for benchmark in SUITE_FILES:
        if benchmark in analysis and 'kcfa' in analysis[benchmark]:
            m_trends = analysis[benchmark]['kcfa'].get('m_trends', {})
            for m_str, stats in m_trends.items():
                m = int(m_str)
                if m not in kcfa_bench_data:
                    kcfa_bench_data[m] = {}
                    kcfa_bench_stats[m] = {}
                kcfa_bench_data[m][benchmark] = stats.get('mean', 0)
                kcfa_bench_stats[m][benchmark] = {'stdev': stats.get('stdev', 0), 'count': stats.get('count', 1)}
    
    # Calculate averages and CIs for DMCFA
    dmcfa_m_vals = sorted(dmcfa_bench_data.keys())
    dmcfa_times = []
    dmcfa_ci_lower = []
    dmcfa_ci_upper = []
    
    for m in dmcfa_m_vals:
        times = [dmcfa_bench_data[m].get(b, 0) for b in SUITE_FILES]
        avg = sum(times) / len(times) if times else 0
        dmcfa_times.append(avg)
        
        variances = []
        for b in SUITE_FILES:
            if b in dmcfa_bench_stats[m]:
                stdev = dmcfa_bench_stats[m][b]['stdev']
                variances.append(stdev ** 2)
        
        pooled_var = sum(variances) / len(variances) if variances else 0
        mean_var = sum((t - avg) ** 2 for t in times) / len(times)
        total_var = pooled_var + mean_var
        total_stdev = total_var ** 0.5
        
        margin = 1.96 * (total_stdev / (len(SUITE_FILES) ** 0.5))
        dmcfa_ci_lower.append(max(0, avg - margin))
        dmcfa_ci_upper.append(avg + margin)
    
    # Calculate averages and CIs for KCFA
    kcfa_k_vals = sorted(kcfa_bench_data.keys())
    kcfa_times = []
    kcfa_ci_lower = []
    kcfa_ci_upper = []
    
    for k in kcfa_k_vals:
        times = [kcfa_bench_data[k].get(b, 0) for b in SUITE_FILES]
        avg = sum(times) / len(times) if times else 0
        kcfa_times.append(avg)
        
        variances = []
        for b in SUITE_FILES:
            if b in kcfa_bench_stats[k]:
                stdev = kcfa_bench_stats[k][b]['stdev']
                variances.append(stdev ** 2)
        
        pooled_var = sum(variances) / len(variances) if variances else 0
        mean_var = sum((t - avg) ** 2 for t in times) / len(times)
        total_var = pooled_var + mean_var
        total_stdev = total_var ** 0.5
        
        margin = 1.96 * (total_stdev / (len(SUITE_FILES) ** 0.5))
        kcfa_ci_lower.append(max(0, avg - margin))
        kcfa_ci_upper.append(avg + margin)
    
    # Plot both on same axis with CIs
    ax.plot(dmcfa_m_vals, dmcfa_times, marker='o', label='DMCFA M(K)',
           color=colors['dmcfa'], linewidth=2.5, markersize=9, alpha=0.85)
    ax.fill_between(dmcfa_m_vals, dmcfa_ci_lower, dmcfa_ci_upper, 
                   color=colors['dmcfa'], alpha=0.15)
    
    ax.plot(kcfa_k_vals, kcfa_times, marker='s', label='KCFA K',
           color=colors['kcfa'], linewidth=2.5, markersize=9, linestyle='--', alpha=0.85)
    ax.fill_between(kcfa_k_vals, kcfa_ci_lower, kcfa_ci_upper, 
                   color=colors['kcfa'], alpha=0.15)
    
    ax.set_xlabel('Context Sensitivity Parameter (M(K) or K)', fontsize=12, fontweight='bold')
    ax.set_ylabel('Average Time (seconds)', fontsize=12, fontweight='bold')
    ax.set_title('Aggregate: DMCFA vs KCFA Time Cost (with 95% CI)', 
                fontsize=14, fontweight='bold')
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    
    output_file = EXPORT_DIR / "aggregate_mk_overlay_dmcfa_kcfa.png"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"Generated: {output_file}")

def main():
    """Main entry point."""
    # Check for --aggregate-only flag
    aggregate_only = "--aggregate-only" in sys.argv
    
    print("Generating comparison graphs...\n")
    
    analysis = load_json_analysis()
    if not analysis:
        print("Error: Could not load analysis data")
        return
    
    # Generate per-benchmark graphs unless --aggregate-only
    if not aggregate_only:
        print("\nGenerating per-benchmark graphs:")
        for benchmark in SUITE_FILES:
            if benchmark in analysis:
                print(f"\n  {benchmark}:")
                plot_d_comparison(benchmark, analysis[benchmark])
                plot_d_comparison_by_mk(benchmark, analysis[benchmark])
                plot_m_k_comparison(benchmark, analysis[benchmark])
                plot_mk_overlay_dmcfa_kcfa(benchmark, analysis[benchmark])
                plot_precision_vs_cost(benchmark, analysis[benchmark])
    
    # Aggregate comparisons: per-set and all-aggregate
    print("\nGenerating aggregate summary graphs:")
    
    # Generate per-set aggregates
    for set_name, benchmarks in BENCHMARK_SETS.items():
        print(f"\n  {set_name}:")
        # Create aggregate set graphs
        plot_aggregate_d_cost()
        plot_aggregate_mk_cost()
        plot_aggregate_mk_by_d()
        plot_aggregate_mk_overlay_dmcfa_kcfa()
    
    # Generate all-aggregate (all benchmarks together)
    print(f"\n  all:")
    plot_aggregate_d_cost()
    plot_aggregate_mk_cost()
    plot_aggregate_mk_by_d()
    plot_aggregate_mk_overlay_dmcfa_kcfa()
    
    print(f"\n✓ All graphs saved to {EXPORT_DIR}")

if __name__ == "__main__":
    main()
