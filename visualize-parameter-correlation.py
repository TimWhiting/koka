#!/usr/bin/env python3
"""
Correlation visualization: parameter value vs precision/proxies.
Supports multiple metrics: 'precision' (actual precision), 'proxy' (1/AvgS/AvgMK/AvgK)
Shows clear scatter plots with separate D value lines.

Parameters:
  metric: 'precision' or 'proxy' (default: both)
  omit_d0: include 'omit-d0' to exclude D=0 for better readability
  overlay: include 'overlay' to show KCFA and DMCFA overlaid (omitting DMCFAE)
"""

import os
import csv
import json
import sys
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Literal
import random

try:
    import matplotlib.pyplot as plt
    import numpy as np
    from matplotlib.scale import ScaleBase
    from matplotlib.ticker import NullFormatter
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False
    print("matplotlib not available")
    exit(1)

# Custom power scale class
class PowerScale(ScaleBase):
    """Custom power scale: y' = y^(1/power) to spread upper values"""
    name = 'power'
    
    def __init__(self, axis, *, power=2.0, **kwargs):
        super().__init__(axis, **kwargs)
        self.power = power
    
    def get_transform(self):
        return PowerTransform(self.power)
    
    def set_default_locators_and_formatters(self, axis):
        from matplotlib.ticker import AutoLocator, ScalarFormatter
        axis.set_major_locator(AutoLocator())
        axis.set_major_formatter(ScalarFormatter())

from matplotlib.transforms import Transform

class PowerTransform(Transform):
    input_dims = 1
    output_dims = 1
    is_separable = True
    
    def __init__(self, power):
        super().__init__()
        self.power = power
    
    def transform_non_affine(self, a):
        return np.sign(a) * np.abs(a) ** (1.0 / self.power)
    
    def inverted(self):
        return PowerTransform(-self.power)

# Register the custom scale
import matplotlib.scale as mscale
mscale.register_scale(PowerScale)

RESULTS_BASE = Path("benchmarks/results")
RESULTS_DIRS = [RESULTS_BASE / "suite", RESULTS_BASE / "handlers", RESULTS_BASE / "rosetta"]
GRAPHS_DIR = Path("benchmarks/analysis/graphs")

def get_benchmark_output_dir(benchmark: str) -> Path:
    """Get the output directory for a benchmark's graphs."""
    return GRAPHS_DIR / benchmark

def find_benchmark_dir(benchmark: str) -> Path:
    """Find the directory containing results for a benchmark.
    Searches recursively in suite, handlers, and rosetta directories.
    """
    # First try suite (most common)
    suite_dir = RESULTS_BASE / "suite" / benchmark
    if suite_dir.exists():
        return suite_dir
    
    # Then try handlers subdirectories
    handlers_dir = RESULTS_BASE / "handlers" / benchmark
    if handlers_dir.exists():
        return handlers_dir
    
    # Then search recursively in rosetta
    rosetta_base = RESULTS_BASE / "rosetta"
    if rosetta_base.exists():
        for p in rosetta_base.rglob(benchmark):
            if p.is_dir():
                return p
    
    # Fallback: return the suite location (will be empty)
    return suite_dir

def load_results(benchmark: str, analysis: str, metric: Literal['precision', 'proxy'] = 'precision') -> List[Dict]:
    """Load all results for a benchmark/analysis.
    
    Args:
        benchmark: Benchmark name
        analysis: Analysis type (dmcfa, dmcfae, kcfa)
        metric: 'precision' for actual precision, 'proxy' for 1/AvgS/AvgMK/AvgK
    """
    benchmark_dir = find_benchmark_dir(benchmark)
    all_results = []
    
    for csv_file in benchmark_dir.glob(f"{analysis}-*-*.csv"):
        with open(csv_file, 'r') as f:
            reader = csv.DictReader(f)
            for row in reader:
                try:
                    row['D'] = int(row['D']) if row['D'] else 0
                    row['M(K)'] = int(row['M(K)']) if row['M(K)'] else 0
                    row['K'] = int(row.get('K', 0)) if row.get('K') else 0
                    
                    if metric == 'proxy':
                        # Parse proxy metrics and invert them (1/proxy)
                        avg_s = float(row['AvgS']) if row.get('AvgS') else None
                        avg_mk = float(row['AvgMK']) if row.get('AvgMK') else None
                        avg_k = float(row['AvgK']) if row.get('AvgK') else None
                        
                        # Use average of inverted proxies (1/proxy)
                        proxies = [1.0/v if v > 0 else 1.0 for v in [avg_s, avg_mk, avg_k] if v is not None]
                        if proxies:
                            row['Precise'] = sum(proxies) / len(proxies)
                        else:
                            row['Precise'] = 1.0
                    else:
                        # Use actual precision
                        row['Precise'] = float(row['Precise'])
                    
                    # Try to parse Time; if it fails (timeout), skip for proxy, mark for precision
                    try:
                        row['Time'] = float(row['Time'])
                    except ValueError:
                        if metric == 'proxy':
                            continue  # Skip timeout datapoints for proxy metrics
                        else:
                            row['Time'] = 999.0  # Large timeout value
                            row['Precise'] = 0.0  # Bad score for timeout
                    
                    all_results.append(row)
                except (ValueError, TypeError):
                    continue
    
    return all_results

def plot_analysis_on_axis(ax, analysis: str, results: List[Dict], metric: Literal['precision', 'proxy'],
                         colors_map: Dict, ylabel: str, ylim: tuple, ref_label: str, overlay: bool = False,
                         lines_only: bool = False):
    """Plot a single analysis on a given axis.
    
    Args:
        ax: matplotlib axis to plot on
        analysis: 'dmcfa', 'dmcfae', or 'kcfa'
        results: list of result rows
        metric: 'precision' or 'proxy'
        colors_map: dict mapping analysis names to colors
        ylabel: y-axis label
        ylim: y-axis limits
        ref_label: reference line label
        overlay: if True, don't set xlim/title (they're shared with other analyses)
        lines_only: if True, don't plot scatter points (only trend lines)
    """
    if not results:
        if not overlay:
            ax.text(0.5, 0.5, f'No data for {analysis}', 
                   ha='center', va='center', transform=ax.transAxes)
            ax.set_visible(False)
        return None
    
    # For KCFA, we don't separate by D (it's always 0)
    if analysis == 'kcfa':
        param_name = 'K'
        param_values = sorted(set(int(float(r['M(K)'])) for r in results if r['M(K)']))
        
        # Collect data by parameter value
        param_data = defaultdict(lambda: {'precisions': [], 'times': [], 'examples': []})
        
        for r in results:
            param = int(float(r['M(K)'])) if r['M(K)'] else 0
            param_data[param]['precisions'].append(r['Precise'])
            param_data[param]['times'].append(r['Time'])
        
        # Plot individual points with jitter (unless lines_only is True)
        if not lines_only:
            for param in param_values:
                precisions = param_data[param]['precisions']
                xs = [param + random.uniform(-0.15, 0.15) for _ in precisions]
                
                for x, prec in zip(xs, precisions):
                    ax.scatter(x, prec, s=80, alpha=0.6, 
                              color=colors_map[analysis], edgecolors='black', linewidth=0.5)
        
        # Add trend line
        averages = [sum(param_data[p]['precisions']) / len(param_data[p]['precisions']) 
                   for p in param_values]
        ax.plot(param_values, averages, '-', linewidth=2.5, 
               color=colors_map[analysis], alpha=0.7, label=f'{analysis.upper()} Trend')
        
        title_suffix = f'({len(results)} examples'
    else:
        # For DMCFA/DMCFAE, separate by D values
        param_name = 'M(K)'
        param_values = sorted(set(int(float(r['M(K)'])) for r in results if r['M(K)']))
        d_values = sorted(set(r['D'] for r in results))
        
        # Use vibrant colors that are distinct from the analysis color
        d_colors_list = ['#E63946', '#F77F00', '#06A77D', '#5A189A', '#0096C7']  # Red, Orange, Green, Purple, Blue
        d_colors = {d: d_colors_list[i % len(d_colors_list)] for i, d in enumerate(d_values)}
        
        # Line styles to further differentiate
        d_styles = {d: ['-', '--', '-.', ':'][i % 4] for i, d in enumerate(d_values)}
        
        # Collect data by D and parameter
        d_data = defaultdict(lambda: defaultdict(lambda: {'precisions': [], 'times': []}))
        
        for r in results:
            d = r['D']
            param = int(float(r['M(K)'])) if r['M(K)'] else 0
            d_data[d][param]['precisions'].append(r['Precise'])
            d_data[d][param]['times'].append(r['Time'])
        
        # Plot for each D value (reverse order so lower D values are on top)
        for d_idx, d in enumerate(reversed(d_values)):
            params_for_d = sorted(set(int(float(r['M(K)'])) for r in results if r['D'] == d and r['M(K)']))
            
            # Plot individual points (unless lines_only is True)
            if not lines_only:
                for param in params_for_d:
                    precisions = d_data[d][param]['precisions']
                    xs = [param + random.uniform(-0.08, 0.08) for _ in precisions]
                    
                    for x, prec in zip(xs, precisions):
                        ax.scatter(x, prec, s=60, alpha=0.5, 
                                  color=d_colors[d], edgecolors='black', linewidth=0.3)
            
            # Add trend line for this D with distinct styling
            averages = [sum(d_data[d][p]['precisions']) / len(d_data[d][p]['precisions']) 
                       for p in params_for_d]
            ax.plot(params_for_d, averages, linestyle=d_styles[d], linewidth=2.5, 
                   color=d_colors[d], alpha=0.85, label=f'D={d}', marker='o', markersize=6)
        
        # Second pass: add ordering markers at points where precision reaches milestones
        if metric == 'precision':
            milestone_precision = [0.5, 0.75, 1.0]
        else:
            milestone_precision = [0.5, 0.75, 1.0]
        
        for milestone in milestone_precision:
            first_d_to_reach = None
            min_param_to_reach = float('inf')
            
            for d in d_values:
                params_for_d = sorted(set(int(float(r['M(K)'])) for r in results if r['D'] == d and r['M(K)']))
                for param in params_for_d:
                    avg_prec = sum(d_data[d][param]['precisions']) / len(d_data[d][param]['precisions'])
                    if avg_prec >= milestone:
                        if param < min_param_to_reach:
                            min_param_to_reach = param
                            first_d_to_reach = d
                        break
            
            # Mark the point where the first D reaches this milestone with large star in matching color
            if first_d_to_reach is not None and min_param_to_reach != float('inf'):
                avg_prec = sum(d_data[first_d_to_reach][min_param_to_reach]['precisions']) / len(d_data[first_d_to_reach][min_param_to_reach]['precisions'])
                ax.scatter(min_param_to_reach, avg_prec, s=400, alpha=0.9, 
                          color=d_colors[first_d_to_reach], marker='*', edgecolors='black', linewidth=2.0, zorder=10)
        
        title_suffix = f'({len(results)} examples'
    
    if not overlay:
        title_suffix += ')'
        
        # Formatting (only when not in overlay mode)
        ax.set_xlabel(f'{param_name} Parameter Value', fontsize=11, fontweight='bold')
        ax.set_ylabel(ylabel, fontsize=11, fontweight='bold')
        ax.set_title(f'{analysis.upper()}\n{title_suffix}', 
                    fontsize=12, fontweight='bold')
        ax.set_ylim(ylim)
        ax.set_xlim(min(param_values) - 0.5, max(param_values) + 0.5)
        # Only use power scale for proxy metrics (not precision)
        if metric == 'proxy':
            ax.set_yscale('power', power=0.5)  # y' = y^2, spreads upper values
        ax.grid(True, alpha=0.3, linestyle='--')
        
        # Add horizontal reference lines
        ax.axhline(y=1.0, color='green', linestyle=':', alpha=0.3, linewidth=1, label=ref_label)
        if metric == 'precision':
            ax.axhline(y=0.0, color='red', linestyle=':', alpha=0.3, linewidth=1, label='Failed (0%)')
        
        ax.legend(loc='lower left', fontsize=8)
    
    return param_values

def create_improved_correlation_plot(benchmark: str, metric: Literal['precision', 'proxy'] = 'precision', 
                                     omit_d0: bool = False, overlay: bool = False, lines_only: bool = False):
    """Create improved scatter plot of parameter vs precision/proxy, with separate lines per D.
    
    Args:
        benchmark: Benchmark name
        metric: 'precision' or 'proxy'
        omit_d0: If True, exclude D=0 data for better readability
        overlay: If True, overlay KCFA and DMCFA only (omitting DMCFAE) on same axis
        lines_only: If True, don't plot scatter points (only trend lines)
    """
    
    if overlay:
        analyses = ['dmcfa', 'kcfa']
        num_cols = 1
    else:
        analyses = ['dmcfa', 'dmcfae', 'kcfa']
        num_cols = 3
    
    fig, axes = plt.subplots(1, num_cols, figsize=(6*num_cols, 5))
    if num_cols == 1:
        axes = [axes]
    
    d0_suffix = ' (D>0)' if omit_d0 else ''
    overlay_suffix = ' - KCFA/DMCFA Overlay' if overlay else ' (Separate D Values)' if not overlay else ''
    
    if metric == 'proxy':
        fig.suptitle(f'{benchmark.upper()} - 1/Proxy Metrics by Parameter (Higher=Better){overlay_suffix}{d0_suffix}', 
                     fontsize=14, fontweight='bold')
        ylabel = '1/Proxy Metric (higher=more precise)'
        ylim = (0.0, 1.02)  # 0 at bottom, 1.02 at top (wiggle room for dots at 1.0)
        ref_label = 'Baseline (1.0)'
    else:
        fig.suptitle(f'{benchmark.upper()} - Precision by Parameter{overlay_suffix}{d0_suffix}', 
                     fontsize=14, fontweight='bold')
        ylabel = 'Precision (0.0 = fail, 1.0 = perfect)'
        ylim = (-0.08, 1.08)
        ref_label = 'Perfect (100%)'
    
    colors_map = {'dmcfa': '#2E86AB', 'dmcfae': '#A23B72', 'kcfa': '#F18F01'}
    
    if overlay:
        ax = axes[0]
        all_param_values = []
        for analysis in analyses:
            results = load_results(benchmark, analysis, metric)
            # Filter out D=0 if requested (but not for KCFA, since it doesn't use D meaningfully)
            if omit_d0 and analysis != 'kcfa':
                results = [r for r in results if r['D'] > 0]
            
            if not results:
                continue
            param_values = plot_analysis_on_axis(ax, analysis, results, metric, colors_map, ylabel, ylim, ref_label, 
                                               overlay=True, lines_only=lines_only)
            if param_values:
                all_param_values.extend(param_values)
        
        # Format the shared axis
        if all_param_values:
            ax.set_xlabel('M/K Parameter Value', fontsize=11, fontweight='bold')
            ax.set_ylabel(ylabel, fontsize=11, fontweight='bold')
            ax.set_title(f'DMCFA & KCFA Overlay', fontsize=12, fontweight='bold')
            ax.set_ylim(ylim)
            ax.set_xlim(min(all_param_values) - 0.5, max(all_param_values) + 0.5)
            if metric == 'proxy':
                ax.set_yscale('power', power=0.5)  # y' = y^2, spreads upper values
            ax.grid(True, alpha=0.3, linestyle='--')
            
            # Add horizontal reference lines
            ax.axhline(y=1.0, color='green', linestyle=':', alpha=0.3, linewidth=1, label=ref_label)
            if metric == 'precision':
                ax.axhline(y=0.0, color='red', linestyle=':', alpha=0.3, linewidth=1, label='Failed (0%)')
            
            ax.legend(loc='lower left', fontsize=8)
    else:
        for ax_idx, analysis in enumerate(analyses):
            ax = axes[ax_idx]
            results = load_results(benchmark, analysis, metric)
            
            # Filter out D=0 if requested (but not for KCFA, since it doesn't use D meaningfully)
            if omit_d0 and analysis != 'kcfa':
                results = [r for r in results if r['D'] > 0]
            
            plot_analysis_on_axis(ax, analysis, results, metric, colors_map, ylabel, ylim, ref_label)
    
    plt.tight_layout()
    
    # Build filename suffix
    suffix_parts = []
    if metric == 'proxy':
        suffix_parts.append('proxies')
    else:
        suffix_parts.append('correlation')
    if omit_d0:
        suffix_parts.append('no-d0')
    if overlay:
        suffix_parts.append('overlay')
    if lines_only:
        suffix_parts.append('lines-only')
    
    suffix = '_'.join(suffix_parts)
    output_file = get_benchmark_output_dir(benchmark) / f"parameter_precision_{suffix}.png"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    return output_file

def create_aggregated_correlation_plot(metric: Literal['precision', 'proxy'] = 'precision',
                                      omit_d0: bool = False, overlay: bool = False, lines_only: bool = False):
    """Create aggregated scatter plot of parameter vs precision/proxy across all benchmarks.
    
    Args:
        metric: 'precision' or 'proxy'
        omit_d0: If True, exclude D=0 data for better readability
        overlay: If True, overlay KCFA and DMCFA only (omitting DMCFAE)
        lines_only: If True, don't plot scatter points (only trend lines)
    """
    
    if overlay:
        analyses = ['dmcfa', 'kcfa']
        num_cols = 1
    else:
        analyses = ['dmcfa', 'dmcfae', 'kcfa']
        num_cols = 3
    
    fig, axes = plt.subplots(1, num_cols, figsize=(6*num_cols, 5))
    if num_cols == 1:
        axes = [axes]
    
    d0_suffix = ' (D>0)' if omit_d0 else ''
    overlay_suffix = ' - KCFA/DMCFA Overlay' if overlay else ''
    
    if metric == 'proxy':
        fig.suptitle(f'ALL BENCHMARKS - Aggregated 1/Proxy Metrics by Parameter (Higher=Better){overlay_suffix}{d0_suffix}', 
                     fontsize=14, fontweight='bold')
        ylabel = '1/Proxy Metric (higher=more precise)'
        ylim = (0.0, 1.02)  # 0 at bottom, 1.02 at top (wiggle room for dots at 1.0)
        ref_label = 'Baseline (1.0)'
    else:
        fig.suptitle(f'ALL BENCHMARKS - Aggregated Precision by Parameter{overlay_suffix}{d0_suffix}', 
                     fontsize=14, fontweight='bold')
        ylabel = 'Precision (0.0 = fail, 1.0 = perfect)'
        ylim = (-0.08, 1.08)
        ref_label = 'Perfect (100%)'
    
    colors_map = {'dmcfa': '#2E86AB', 'dmcfae': '#A23B72', 'kcfa': '#F18F01'}
    benchmarks = ["basic", "nondet", "nested", "multi-effect", "recursion", "state-handler", "complex-flow", "nested-nondet"]
    
    # Load all results across all benchmarks
    all_results_by_analysis = {analysis: [] for analysis in analyses}
    
    for benchmark in benchmarks:
        for analysis in analyses:
            results = load_results(benchmark, analysis, metric)
            # Filter out D=0 if requested (but not for KCFA, since it doesn't use D meaningfully)
            if omit_d0 and analysis != 'kcfa':
                results = [r for r in results if r['D'] > 0]
            all_results_by_analysis[analysis].extend(results)
    
    if overlay:
        ax = axes[0]
        all_param_values = []
        for analysis in analyses:
            results = all_results_by_analysis[analysis]
            if not results:
                continue
            param_values = plot_analysis_on_axis(ax, analysis, results, metric, colors_map, ylabel, ylim, ref_label, 
                                               overlay=True, lines_only=lines_only)
            if param_values:
                all_param_values.extend(param_values)
        
        # Format the shared axis
        if all_param_values:
            ax.set_xlabel('M/K Parameter Value', fontsize=11, fontweight='bold')
            ax.set_ylabel(ylabel, fontsize=11, fontweight='bold')
            ax.set_title(f'DMCFA & KCFA Overlay (All Benchmarks)', fontsize=12, fontweight='bold')
            ax.set_ylim(ylim)
            ax.set_xlim(min(all_param_values) - 0.5, max(all_param_values) + 0.5)
            if metric == 'proxy':
                ax.set_yscale('power', power=0.5)  # y' = y^2, spreads upper values
            ax.grid(True, alpha=0.3, linestyle='--')
            
            # Add horizontal reference lines
            ax.axhline(y=1.0, color='green', linestyle=':', alpha=0.3, linewidth=1, label=ref_label)
            if metric == 'precision':
                ax.axhline(y=0.0, color='red', linestyle=':', alpha=0.3, linewidth=1, label='Failed (0%)')
            
            ax.legend(loc='lower left', fontsize=8)
    else:
        for ax_idx, analysis in enumerate(analyses):
            ax = axes[ax_idx]
            results = all_results_by_analysis[analysis]
            plot_analysis_on_axis(ax, analysis, results, metric, colors_map, ylabel, ylim, ref_label)
    
    plt.tight_layout()
    
    # Build filename suffix
    suffix_parts = []
    if metric == 'proxy':
        suffix_parts.append('proxies')
    else:
        suffix_parts.append('correlation')
    if omit_d0:
        suffix_parts.append('no-d0')
    if overlay:
        suffix_parts.append('overlay')
    if lines_only:
        suffix_parts.append('lines-only')
    
    suffix = '_'.join(suffix_parts)
    output_file = GRAPHS_DIR / f"aggregated_parameter_precision_{suffix}.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    return output_file

def main():
    """Generate correlation plots for all benchmarks and aggregated.
    
    Usage:
      python3 visualize-parameter-correlation.py [metric] [omit-d0] [overlay]
    
    Arguments:
    metric: 'precision' or 'proxy' (default: both)
    omit-d0: exclude D=0 data (PROXY ONLY - ignored for precision)
    overlay: show KCFA and DMCFA overlaid; automatically enables lines-only
    lines-only: show only trend lines without scatter points (PROXY ONLY)
    
    Constraints:
      - omit-d0 and lines-only only apply to proxy metric
      - overlay automatically enables lines-only (lines-only is implicit)
    
    Examples:
      python3 visualize-parameter-correlation.py           # Both metrics, all variants
      python3 visualize-parameter-correlation.py proxy     # Proxy only
      python3 visualize-parameter-correlation.py proxy omit-d0  # Proxy with D>0 only
      python3 visualize-parameter-correlation.py proxy overlay  # Proxy overlay (lines-only auto-enabled)
    """
    
    if not HAS_MATPLOTLIB:
        print("matplotlib required")
        return
    
    GRAPHS_DIR.mkdir(parents=True, exist_ok=True)
    
    # Parse arguments
    metrics = ['precision', 'proxy']
    omit_d0 = False
    overlay = False
    lines_only = False
    
    for arg in sys.argv[1:]:
        if arg in ['precision', 'proxy']:
            metrics = [arg]
        elif arg == 'omit-d0':
            omit_d0 = True
        elif arg == 'overlay':
            overlay = True
        elif arg == 'lines-only':
            lines_only = True
        else:
            print(f"Unknown argument: {arg}")
            print("Usage: python3 visualize-parameter-correlation.py [metric] [omit-d0] [overlay] [lines-only]")
            print("  metric: 'precision' or 'proxy' (default: both)")
            print("  omit-d0: exclude D=0 (PROXY ONLY)")
            print("  overlay: KCFA/DMCFA overlay (auto-enables lines-only)")
            print("  lines-only: show only trend lines (PROXY ONLY)")
            sys.exit(1)
    
    # Validate constraints
    if omit_d0 and 'precision' in metrics and len(metrics) == 1:
        print("Error: omit-d0 is only valid for proxy metric")
        sys.exit(1)
    
    if lines_only and 'precision' in metrics and len(metrics) == 1:
        print("Error: lines-only is only valid for proxy metric")
        sys.exit(1)
    
    # Overlay automatically enables lines-only
    if overlay:
        lines_only = True
    
    # Load all available benchmarks from suite, handlers, and rosetta
    def load_all_benchmarks() -> List[str]:
        """Get list of all available benchmarks from suite, handlers, and rosetta directories."""
        benchmarks_set = set()
        
        # Get benchmarks from suite
        suite_dir = RESULTS_BASE / "suite"
        if suite_dir.exists():
            benchmarks_set.update(d.name for d in suite_dir.iterdir() if d.is_dir())
        
        # Get benchmarks from handlers
        handlers_dir = RESULTS_BASE / "handlers"
        if handlers_dir.exists():
            benchmarks_set.update(d.name for d in handlers_dir.iterdir() if d.is_dir())
        
        # Get benchmarks from rosetta (recursively)
        rosetta_dir = RESULTS_BASE / "rosetta"
        if rosetta_dir.exists():
            # Look for directories that contain CSV files
            for p in rosetta_dir.rglob("*.csv"):
                # Extract benchmark name from parent directory
                parent_dir = p.parent
                benchmarks_set.add(parent_dir.name)
        
        return sorted(benchmarks_set)
    
    benchmarks = load_all_benchmarks()
    
    # Generate graphs based on metric(s) specified
    # If both metrics specified, generate all combinations
    # If single metric specified, apply constraints for that metric
    
    if len(metrics) == 2:  # Both metrics
        # Generate base variants (no special options)
        for metric in metrics:
            metric_name = 'Precision' if metric == 'precision' else 'Proxy (1/AvgS/AvgMK/AvgK)'
            print(f"Generating {metric_name} correlation plots...\n")
            
            for benchmark in benchmarks:
                print(f"  {benchmark}...", end='', flush=True)
                try:
                    output = create_improved_correlation_plot(benchmark, metric, False, False, False)
                    print(f" ✓ {output.name}")
                except Exception as e:
                    print(f" ✗ Error: {e}")
            
            print(f"  aggregated...", end='', flush=True)
            try:
                output = create_aggregated_correlation_plot(metric, False, False, False)
                print(f" ✓ {output.name}")
            except Exception as e:
                print(f" ✗ Error: {e}")
            print()
        
        # Generate proxy-only variants (omit-d0, overlay)
        metric = 'proxy'
        metric_name = 'Proxy (1/AvgS/AvgMK/AvgK)'
        
        # omit-d0 variant
        print(f"Generating {metric_name} correlation plots (D>0 only)...\n")
        for benchmark in benchmarks:
            print(f"  {benchmark}...", end='', flush=True)
            try:
                output = create_improved_correlation_plot(benchmark, metric, True, False, False)
                print(f" ✓ {output.name}")
            except Exception as e:
                print(f" ✗ Error: {e}")
        
        print(f"  aggregated...", end='', flush=True)
        try:
            output = create_aggregated_correlation_plot(metric, True, False, False)
            print(f" ✓ {output.name}")
        except Exception as e:
            print(f" ✗ Error: {e}")
        print()
        
        # overlay variant (automatically lines-only)
        print(f"Generating {metric_name} correlation plots (KCFA/DMCFA overlay)...\n")
        for benchmark in benchmarks:
            print(f"  {benchmark}...", end='', flush=True)
            try:
                output = create_improved_correlation_plot(benchmark, metric, False, True, True)
                print(f" ✓ {output.name}")
            except Exception as e:
                print(f" ✗ Error: {e}")
        
        print(f"  aggregated...", end='', flush=True)
        try:
            output = create_aggregated_correlation_plot(metric, False, True, True)
            print(f" ✓ {output.name}")
        except Exception as e:
            print(f" ✗ Error: {e}")
        print()
        
        # precision overlay variant (lines-only, no dots)
        metric = 'precision'
        metric_name = 'Precision'
        print(f"Generating {metric_name} correlation plots (KCFA/DMCFA overlay, lines-only)...\n")
        for benchmark in benchmarks:
            print(f"  {benchmark}...", end='', flush=True)
            try:
                output = create_improved_correlation_plot(benchmark, metric, False, True, True)
                print(f" ✓ {output.name}")
            except Exception as e:
                print(f" ✗ Error: {e}")
        
        print(f"  aggregated...", end='', flush=True)
        try:
            output = create_aggregated_correlation_plot(metric, False, True, True)
            print(f" ✓ {output.name}")
        except Exception as e:
            print(f" ✗ Error: {e}")
        print()
    
    else:  # Single metric specified
        metric = metrics[0]
        metric_name = 'Precision' if metric == 'precision' else 'Proxy (1/AvgS/AvgMK/AvgK)'
        options_str = []
        if omit_d0:
            options_str.append('D>0 only')
        if overlay:
            options_str.append('KCFA/DMCFA overlay')
        options_text = f" ({', '.join(options_str)})" if options_str else ""
        
        print(f"Generating {metric_name} correlation plots{options_text}...\n")
        
        for benchmark in benchmarks:
            print(f"  {benchmark}...", end='', flush=True)
            try:
                output = create_improved_correlation_plot(benchmark, metric, omit_d0, overlay, lines_only)
                print(f" ✓ {output.name}")
            except Exception as e:
                print(f" ✗ Error: {e}")
        
        print(f"  aggregated...", end='', flush=True)
        try:
            output = create_aggregated_correlation_plot(metric, omit_d0, overlay, lines_only)
            print(f" ✓ {output.name}")
        except Exception as e:
            print(f" ✗ Error: {e}")
        print()
    
    print("✓ All graphs saved to benchmarks/analysis/graphs")

if __name__ == '__main__':
    main()
