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

D_COLORS = {
    '0': '#1f77b4',
    '1': '#ff7f0e',
    '2': '#2ca02c', 
    '3': '#d62728',
    '20': '#9467bd',
    '100': '#8c564b'
}

# Define benchmark sets
BENCHMARK_SETS = {
    "suite": ["basic", "nondet", "nested", "multi-effect", "recursion", "state-handler", "complex-flow", "nested-nondet"],
    "handlers": ["ambient", "nim", "unix", "vec", "yield"],
    "rosetta": ["jump-anywhere", "monads-writer", "pr4rings"]
}

def load_suite_files() -> List[str]:
    """Load benchmark names from all result files."""
    benchmarks = set()
    
    if not RESULTS_BASE.exists():
        return []
        
    # Walk through the results directory to find all benchmarks
    # We look for any d/m directory to find the structure
    for d_dir in RESULTS_BASE.iterdir():
        if not d_dir.is_dir() or not d_dir.name.isdigit(): continue
        
        for m_dir in d_dir.iterdir():
            if not m_dir.is_dir() or not m_dir.name.isdigit(): continue
            
            # Found a valid d/m root. Scan for all CSVs under here.
            for csv_file in m_dir.rglob("*.csv"):
                # Path relative to m_dir is the benchmark key (e.g. suite/basic.csv -> suite/basic)
                rel_path = csv_file.relative_to(m_dir)
                benchmarks.add(str(rel_path.with_suffix('')))
                
    return sorted(list(benchmarks))

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
            d_trend = []
            for d in sorted(data.get('d_values', [])):
                stats = data['d_trends'][str(d)]
                # Support both flat and nested (new) structures
                avg_time = stats.get('time', stats).get('mean', 0)
                d_trend.append((int(d), avg_time))
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
            m_trend = []
            for m in sorted(data.get('m_values', [])):
                stats = data['m_trends'][str(m)]
                avg_time = stats.get('time', stats).get('mean', 0)
                m_trend.append((int(m), avg_time))
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
            precision_trend = []
            for param in sorted(data.get('m_values', data.get('k_values', []))):
                stats = trends_data[str(param)]
                avg_prec = stats.get('precision', stats).get('mean', 0)
                precision_trend.append((int(param), avg_prec))
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
        if analysis_key in d_trends and d_trends[analysis_key]:
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
        if analysis_key in m_trends and m_trends[analysis_key]:
            m_vals, times = zip(*m_trends[analysis_key])
            ax.plot(m_vals, times, marker='o', label=f'{analysis_key.upper()} M(K)',
                   color=colors.get(analysis_key, '#000000'), linewidth=2, markersize=8)
    
    # Plot KCFA with K (if available)
    if 'kcfa' in analysis:
        kcfa_data = analysis['kcfa']
        if 'm_trends' in kcfa_data:
            k_trends = extract_m_trends({'kcfa': kcfa_data})['kcfa']
            if k_trends:
                k_vals, times = zip(*k_trends)
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
        if 'dmcfa' in m_trends and m_trends['dmcfa']:
            m_vals, times = zip(*m_trends['dmcfa'])
            ax.plot(m_vals, times, marker='o', label='DMCFA M(K)',
                   color=colors['dmcfa'], linewidth=2.5, markersize=8)
    
    # Plot KCFA with K
    kcfa_data = analysis['kcfa']
    if 'm_trends' in kcfa_data:
        k_trends = extract_m_trends({'kcfa': kcfa_data})
        if 'kcfa' in k_trends and k_trends['kcfa']:
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
        if m_trends[analysis_key]:
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

def setup_broken_xaxis(fig, ax1, ax2):
    """Setup style for broken x-axis between two subplots."""
    ax1.spines['right'].set_visible(False)
    ax2.spines['left'].set_visible(False)
    
    # Don't put ticks on the broken side
    ax1.yaxis.tick_left()
    ax1.tick_params(labelright=False)
    ax2.yaxis.tick_right()
    ax2.tick_params(labelright=False) # Or True if specific
    ax2.set_yticks([]) # Hide Y ticks on second plot if sharing Y fully
    
    # Diagonal lines
    d = .015  # proportion of vertical to horizontal extent of the slanted line
    kwargs = dict(transform=ax1.transAxes, color='k', clip_on=False)
    ax1.plot((1 - d, 1 + d), (-d, +d), **kwargs)
    ax1.plot((1 - d, 1 + d), (1 - d, 1 + d), **kwargs)

    kwargs.update(transform=ax2.transAxes)  # switch to the bottom axes
    ax2.plot((-d, +d), (1 - d, 1 + d), **kwargs)
    ax2.plot((-d, +d), (-d, +d), **kwargs)

def plot_aggregate_mk_by_d():
    """Plot aggregated M(K)/K comparison across all benchmarks with colors for analyses, line styles for D, and CIs."""
    analysis = load_json_analysis()
    
    # Gather data first to determine range
    kcfa_data_points = {} # m -> (mean, ci_lower, ci_upper)
    dmcfa_lines = defaultdict(list) # d -> list of (m, mean)
    all_m = set()

    # Data Collection: KCFA
    if SUITE_FILES[0] in analysis:
        m_to_times = defaultdict(list)
        m_to_stats = defaultdict(list)
        for benchmark in SUITE_FILES:
            if benchmark not in analysis or 'kcfa' not in analysis[benchmark]:
                continue
            kcfa_res = analysis[benchmark]['kcfa'].get('m_trends', {})
            for m_str, stats in kcfa_res.items():
                m = int(m_str)
                m_to_times[m].append(stats.get('mean', 0))
                m_to_stats[m].append({'stdev': stats.get('stdev', 0), 'count': stats.get('count', 1)})
        
        for m in sorted(m_to_times.keys()):
            times = m_to_times[m]
            avg = sum(times) / len(times)
            
            variances = [s['stdev'] ** 2 for s in m_to_stats[m]]
            pooled_var = sum(variances) / len(variances) if variances else 0
            mean_var = sum((t - avg) ** 2 for t in times) / len(times)
            total_stdev = (pooled_var + mean_var) ** 0.5
            margin = 1.96 * (total_stdev / (len(SUITE_FILES) ** 0.5))
            
            kcfa_data_points[m] = (avg, max(0, avg - margin), avg + margin)
            all_m.add(m)

    # Data Collection: DMCFA
    d_to_lines = defaultdict(list)
    for analysis_key in ['dmcfa', 'dmcfae']:
        for benchmark in SUITE_FILES:
            if benchmark not in analysis or analysis_key not in analysis[benchmark]: continue
            bench_analysis = analysis[benchmark][analysis_key]
            
            d_values = sorted(bench_analysis.get('d_values', []))
            for d_val in d_values:
                d_key = str(d_val)
                if 'd_m_trends' in bench_analysis and d_key in bench_analysis['d_m_trends']:
                    m_results = bench_analysis['d_m_trends'][d_key]
                    for m_str, stats in m_results.items():
                        m = int(m_str)
                        d_to_lines[d_val].append((m, stats.get('mean', 0)))
                        all_m.add(m)

    # Consolidate DMCFA lines
    final_dmcfa_lines = {}
    for d_val, points in d_to_lines.items():
        if not points: continue
        m_map = defaultdict(list)
        for m, t in points: m_map[m].append(t)
        
        line_data = [] # (m, avg)
        for m in sorted(m_map.keys()):
            line_data.append((m, sum(m_map[m])/len(m_map[m])))
        final_dmcfa_lines[d_val] = line_data

    # Setup Plot
    has_large = any(m > 10 for m in all_m)
    if has_large:
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 7), sharey=True, 
                                      gridspec_kw={'width_ratios': [3, 1], 'wspace': 0.05})
        setup_broken_xaxis(fig, ax1, ax2)
        axes = [ax1, ax2]
        ax1.set_xlim(-0.5, 5.5) # Main part
        # Outlier part - assume > 10
        outliers = [m for m in all_m if m > 10]
        if outliers:
            ax2.set_xlim(min(outliers)-2, max(outliers)+2)
    else:
        fig, ax = plt.subplots(figsize=(13, 7))
        axes = [ax]
    
    # Plotting Function
    for ax in axes:
        # Plot KCFA
        if kcfa_data_points:
            m_vals = sorted(kcfa_data_points.keys())
            avgs = [kcfa_data_points[m][0] for m in m_vals]
            lowers = [kcfa_data_points[m][1] for m in m_vals]
            uppers = [kcfa_data_points[m][2] for m in m_vals]
            
            ax.plot(m_vals, avgs, marker='s', label='KCFA', color=colors['kcfa'], 
                   linestyle='-', linewidth=2.5, markersize=7, alpha=0.7, zorder=1)
            ax.fill_between(m_vals, lowers, avgers=uppers, color=colors['kcfa'], alpha=0.06, zorder=1) # Note: argument name fix needed 

        # Plot DMCFA/E
        for d_val in sorted(final_dmcfa_lines.keys()):
            line = final_dmcfa_lines[d_val]
            ms, ts = zip(*line)
            ax.plot(ms, ts, 'o-', label=f"D={d_val}", 
                   color=D_COLORS.get(str(d_val), 'gray'), linewidth=2)

    # Fix labels etc
    target_ax = axes[0]
    target_ax.set_yscale('log')
    # If broken, ax2 also needs log scale (shared Y handles it? Yes)
    
    target_ax.set_ylabel('Average Time (seconds, log scale)', fontsize=12, fontweight='bold')
    if len(axes) > 1:
        fig.text(0.5, 0.04, 'M(K) / K (Context Sensitivity)', ha='center', fontsize=12, fontweight='bold')
    else:
        target_ax.set_xlabel('M(K) / K (Context Sensitivity)', fontsize=12, fontweight='bold')

    plt.suptitle('Aggregate: Context Sensitivity Cost (with D Levels)', fontsize=14, fontweight='bold', y=0.95)
    
    # Legend - gather handles from first axis
    h, l = axes[0].get_legend_handles_labels()
    # De-duplicate legacy if needed, but dict keys are unique here usually?
    # Actually we plot multiple times (once per axis). Just take one set.
    by_label = dict(zip(l, h))
    if by_label:
        axes[0].legend(by_label.values(), by_label.keys(), fontsize=9, loc='best', ncol=3)
    
    output_file = EXPORT_DIR / "aggregate_mk_by_d_comparison.png"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"Generated: {output_file}")

def plot_aggregate_d_cost():
    """Plot D cost across all benchmarks for each analysis with confidence intervals."""
    analysis = load_json_analysis()
    
    # Pre-scan data to check for outliers
    all_d = set()
    for analysis_key in DMCFA_ANALYSES:
        for benchmark in SUITE_FILES:
            if benchmark in analysis and analysis_key in analysis[benchmark]:
                d_trends = analysis[benchmark][analysis_key].get('d_trends', {})
                for d_str in d_trends: all_d.add(int(d_str))
    
    has_large = any(d > 10 for d in all_d)
    
    if has_large:
        fig, axes_flat = plt.subplots(1, 4, figsize=(16, 6), 
                                     gridspec_kw={'width_ratios': [3, 1, 3, 1]})
        # Group 0,1 -> Analysis 1. Group 2,3 -> Analysis 2
        ax_groups = [(axes_flat[0], axes_flat[1]), (axes_flat[2], axes_flat[3])]
    else:
        fig, axes = plt.subplots(1, 2, figsize=(16, 6))
        ax_groups = [(axes[0],), (axes[1],)]

    for idx, analysis_key in enumerate(DMCFA_ANALYSES):
        current_axes = ax_groups[idx]
        is_broken = len(current_axes) > 1
        
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
        
        # Plot on all axes in group
        for ax in current_axes:
            ax.plot(d_vals, avg_by_d,
                   marker='o', linewidth=2.5, markersize=10, color='#2E86AB', alpha=0.85)
            ax.fill_between(d_vals, ci_lower, ci_upper, color='#2E86AB', alpha=0.15)
        
        target_ax = current_axes[0]
        
        if is_broken:
            ax1, ax2 = current_axes
            setup_broken_xaxis(fig, ax1, ax2)
            ax1.set_xlim(-0.5, 5.5)
            outliers = [d for d in d_vals if d > 10]
            if outliers:
                ax2.set_xlim(min(outliers)-2, max(outliers)+2)
                # ax2 seems to share Y? NOT AUTOMATICALLY with subplots(1,4).
                # Need to share Y manually or plotting limits manually.
                # Let's share Y
                ax2.sharey(ax1)
                ax2.tick_params(labelleft=False)

        target_ax.set_ylabel('Average Time (seconds)', fontsize=11, fontweight='bold')
        
        # Title mostly centered
        if is_broken:
             # Hacky title placement
             target_ax.set_title(f'{analysis_key.upper()}: Average D Cost', 
                    fontsize=12, fontweight='bold', loc='left')
        else:
             target_ax.set_title(f'{analysis_key.upper()}: Average D Cost Across Suite (with 95% CI)', 
                    fontsize=12, fontweight='bold')
             target_ax.set_xticks(range(0, max(d_vals)+1)) # Better than fixed 6

        target_ax.grid(True, alpha=0.3)
        if len(current_axes) > 1: current_axes[1].grid(True, alpha=0.3)
        
        # Common X label
        if is_broken:
             # x label on ax1 is misleading if it covers whole thing
             # put text centered below
             pass 
        else:
             target_ax.set_xlabel('D (Demand Level)', fontsize=11, fontweight='bold')

    plt.tight_layout()
    output_file = EXPORT_DIR / "aggregate_d_cost.png"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"Generated: {output_file}")

def plot_aggregate_mk_cost_for_set(benchmarks: List[str], set_name: str):
    """Plot M(K)/K cost across specified benchmarks with confidence intervals."""
    analysis = load_json_analysis()
    
    # Pre-scan for M(K) range
    all_m = set()
    for analysis_key in DMCFA_ANALYSES:
        for benchmark in benchmarks:
            if benchmark in analysis and analysis_key in analysis[benchmark]:
                m_trends = analysis[benchmark][analysis_key].get('m_trends', {})
                for m_str in m_trends: all_m.add(int(m_str))
    
    has_large_m = any(m > 10 for m in all_m)
    
    if has_large_m:
        fig = plt.figure(figsize=(16, 6))
        gs = fig.add_gridspec(1, 3, width_ratios=[3, 1, 3], wspace=0.1)
        ax_dmcfa_1 = fig.add_subplot(gs[0])
        ax_dmcfa_2 = fig.add_subplot(gs[1])
        ax_kcfa = fig.add_subplot(gs[2])
        
        setup_broken_xaxis(fig, ax_dmcfa_1, ax_dmcfa_2)
        ax_dmcfa_1.set_xlim(-0.5, 5.5)
        outliers = [m for m in all_m if m > 10]
        if outliers:
            ax_dmcfa_2.set_xlim(min(outliers)-2, max(outliers)+2)
        
        dmcfa_axes = [ax_dmcfa_1, ax_dmcfa_2]
        
        # Adjust spacing between DMCFA group and KCFA
        # gridspec wspace handles between 1 and 2 roughly
        # but 1 and 2 are close (broken), 2 and 3 should be far?
        # wspace applies to all. Maybe use nested gridspec?
        # Simpler: 4 cols. [3, 1, 0.5 (spacer), 4]
        # Or just accept default.
        # Let's check spacing manually by adjusting wspace for broken
        # But setup_broken_xaxis expects them to be close?
        # It relies on visual line.
        
        # Simpler manual approach with 1 row, 3 cols, sharey=False (between dmcfa and kcfa?)
        # DMCFA pair shares Y.
        ax_dmcfa_2.sharey(ax_dmcfa_1)
        ax_dmcfa_2.tick_params(labelleft=False)
        
    else:
        fig, axes = plt.subplots(1, 2, figsize=(16, 6))
        ax_dmcfa = axes[0]
        ax_kcfa = axes[1]
        dmcfa_axes = [ax_dmcfa]

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
        
        # Plot on all DMCFA axes
        for ax in dmcfa_axes:
            ax.plot(m_vals, avg_by_m,
                     marker='o', linewidth=2.5, markersize=10, 
                     label=analysis_key.upper(),
                     color=colors[analysis_key], alpha=0.85)
            ax.fill_between(m_vals, ci_lower, ci_upper,
                             color=colors[analysis_key], alpha=0.15)
    
    target_ax = dmcfa_axes[0]
    target_ax.set_ylabel('Average Time (seconds)', fontsize=11, fontweight='bold')
    
    # Title
    if len(dmcfa_axes) > 1:
        target_ax.set_title('DMCFA Analyses: Average M(K) Cost', fontsize=12, fontweight='bold', loc='left')
    else:
        target_ax.set_title('DMCFA Analyses: Average M(K) Cost Across Suite (with 95% CI)', 
                      fontsize=12, fontweight='bold')
        
    target_ax.grid(True, alpha=0.3)
    if len(dmcfa_axes) > 1: dmcfa_axes[1].grid(True, alpha=0.3)
    target_ax.legend(fontsize=11)
    
    # Common X label for DMCFA
    target_ax.set_xlabel('M(K) (Context Sensitivity)', fontsize=11, fontweight='bold')
    
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
        plot_aggregate_mk_cost_for_set(benchmarks, set_name)
        plot_aggregate_mk_by_d()
        plot_aggregate_mk_overlay_dmcfa_kcfa()
    
    # Generate all-aggregate (all benchmarks together)
    print(f"\n  all:")
    plot_aggregate_d_cost()
    plot_aggregate_mk_cost_for_set(SUITE_FILES, "all")
    plot_aggregate_mk_by_d()
    plot_aggregate_mk_overlay_dmcfa_kcfa()
    
    print(f"\n✓ All graphs saved to {EXPORT_DIR}")

if __name__ == "__main__":
    main()
