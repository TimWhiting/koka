#!/usr/bin/env python3
"""
Generate visualizations for benchmark analysis focusing on precision, cost, and proxy metrics.
Includes LOC correlation as additional dimension.
"""

import json
import sys
from pathlib import Path
from collections import defaultdict
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np

ANALYSIS_FILE = Path("benchmarks/analysis/benchmark-summary.json")
GRAPHS_DIR = Path("benchmarks/analysis/graphs")

# Color schemes
CATEGORY_COLORS = {
    'suite': '#1f77b4',
    'handlers': '#ff7f0e',
    'koka-gen': '#2ca02c',
    'rosetta': '#d62728'
}

D_COLORS = {
    0: '#1f77b4',
    1: '#ff7f0e',
    2: '#2ca02c',
    3: '#d62728',
    20: '#9467bd',
    100: '#8c564b'
}

METRIC_CONFIG = {
    'precision': {
        'label': 'Precision',
        'filename_suffix': '',
        'json_key': 'precision',
        'trend_key': 'precision_mean'
    },
    'proxy': {
        'label': 'Proxy Precision (1/AvgS)',
        'filename_suffix': '_proxy',
        'json_key': 'proxy_precision',
        'trend_key': 'proxy_precision_mean'
    }
}

def load_analysis() -> dict:
    """Load the analysis JSON file."""
    if not ANALYSIS_FILE.exists():
        print(f"Error: {ANALYSIS_FILE} not found. Run analyze-benchmarks.py first.")
        sys.exit(1)
    
    with open(ANALYSIS_FILE, 'r') as f:
        return json.load(f)

def plot_metric_vs_cost(analysis: dict, metric_type: str = 'precision'):
    """Plot metric vs execution time for all benchmarks."""
    config = METRIC_CONFIG[metric_type]
    label = config['label']
    json_key = config['json_key']
    
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    
    for analysis_type, ax, title in [('dmcfa', ax1, 'DMCFA'), ('dmcfae', ax2, 'DMCFA-Exp')]:
        by_category = defaultdict(lambda: {'metric': [], 'time': [], 'names': []})
        
        for benchmark, stats in analysis.items():
            if analysis_type not in stats:
                continue
            
            s = stats[analysis_type]
            category = s.get('category', 'unknown')
            
            if json_key in s:
                by_category[category]['metric'].append(s[json_key]['mean'])
                by_category[category]['time'].append(s['time']['mean'])
                by_category[category]['names'].append(benchmark)
        
        # Plot each category
        for category, data in by_category.items():
            ax.scatter(data['time'], data['metric'], 
                      label=category, alpha=0.6, s=50,
                      color=CATEGORY_COLORS.get(category, '#888888'))
        
        ax.set_xlabel('Execution Time (seconds)')
        ax.set_ylabel(label)
        ax.set_title(f'{title}: {label} vs Cost')
        ax.legend()
        ax.grid(True, alpha=0.3)
        ax.set_ylim([0, 1.05])
    
    plt.tight_layout()
    output_path = GRAPHS_DIR / f'{metric_type}_vs_cost.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"Saved: {output_path}")
    plt.close()

def plot_parameter_sensitivity(analysis: dict, metric_type: str = 'precision'):
    """Plot how metric/cost change with D parameter, with axis break for D=20,100."""
    config = METRIC_CONFIG[metric_type]
    label = config['label']
    trend_key = config['trend_key']
    
    # Select a few representative benchmarks
    benchmarks_to_plot = []
    for benchmark, stats in analysis.items():
        if 'dmcfa' in stats and 'd_trends' in stats['dmcfa']:
            # Pick benchmarks with varying D values
            if len(stats['dmcfa']['d_trends']) > 2:
                benchmarks_to_plot.append(benchmark)
    
    # Limit to top 6 most interesting
    benchmarks_to_plot = sorted(benchmarks_to_plot)[:6]
    
    if not benchmarks_to_plot:
        print(f"No benchmarks with D parameter variation found for {metric_type}")
        return
    
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()
    
    for idx, benchmark in enumerate(benchmarks_to_plot):
        if idx >= len(axes):
            break
        
        ax = axes[idx]
        stats = analysis[benchmark]['dmcfa']
        d_trends = stats['d_trends']
        
        # Extract data and separate low D (0-3) from high D (20, 100)
        all_d_values = sorted([int(d) for d in d_trends.keys()])
        high_d = [d for d in all_d_values if d >= 20]
        
        times = [d_trends[str(d)]['time_mean'] for d in all_d_values]
        metric_values = [d_trends[str(d)].get(trend_key, 0) for d in all_d_values]
        
        # Plot with x-axis positions that create visual break
        x_positions = []
        x_labels = []
        for d in all_d_values:
            if d <= 3:
                x_positions.append(float(d))
            elif d == 20:
                x_positions.append(4.5)
            elif d == 100:
                x_positions.append(5.5)
            x_labels.append(str(d))
        
        # Plot on dual axes
        ax2 = ax.twinx()
        
        line1 = ax.plot(x_positions, times, 'b-o', label='Time', linewidth=2)
        line2 = ax2.plot(x_positions, metric_values, 'r-s', label=label, linewidth=2)
        
        # Add visual break indicator
        if len(high_d) > 0:
            ax.axvline(x=3.75, color='gray', linestyle=':', alpha=0.5, linewidth=1)
        
        ax.set_xlabel('D Parameter')
        ax.set_ylabel('Time (s)', color='b')
        ax2.set_ylabel(label, color='r')
        ax.set_title(benchmark)
        ax.set_xticks(x_positions)
        ax.set_xticklabels(x_labels)
        ax.grid(True, alpha=0.3)
        ax.tick_params(axis='y', labelcolor='b')
        ax2.tick_params(axis='y', labelcolor='r')
        ax2.set_ylim([0, 1.05])
        
        # Combined legend
        lines = line1 + line2
        labels = [l.get_label() for l in lines]
        ax.legend(lines, labels, loc='upper left')
    
    # Hide unused subplots
    for idx in range(len(benchmarks_to_plot), len(axes)):
        axes[idx].set_visible(False)
    
    plt.suptitle(f'Parameter Sensitivity: D vs Time & {label} (axis break at D>3)', fontsize=14, y=1.02)
    plt.tight_layout()
    output_path = GRAPHS_DIR / f'{metric_type}_parameter_sensitivity.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"Saved: {output_path}")
    plt.close()

def plot_cost_distribution(analysis: dict):
    """Plot distribution of execution times by category."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    
    for analysis_type, ax, title in [('dmcfa', ax1, 'DMCFA'), ('dmcfae', ax2, 'DMCFA-Exp')]:
        by_category = defaultdict(list)
        
        for benchmark, stats in analysis.items():
            if analysis_type not in stats:
                continue
            
            s = stats[analysis_type]
            category = s.get('category', 'unknown')
            by_category[category].append(s['time']['mean'])
        
        # Create box plot
        categories = sorted(by_category.keys())
        data = [by_category[cat] for cat in categories]
        
        bp = ax.boxplot(data, labels=categories, patch_artist=True)
        
        # Color boxes
        for patch, category in zip(bp['boxes'], categories):
            patch.set_facecolor(CATEGORY_COLORS.get(category, '#888888'))
            patch.set_alpha(0.6)
        
        ax.set_ylabel('Execution Time (seconds)')
        ax.set_title(f'{title}: Cost Distribution by Category')
        ax.grid(True, alpha=0.3, axis='y')
    
    plt.tight_layout()
    output_path = GRAPHS_DIR / 'cost_distribution.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"Saved: {output_path}")
    plt.close()

def plot_m_across_d_lines(analysis: dict, metric_type: str = 'precision'):
    """Plot line graphs showing different M values across D parameters."""
    config = METRIC_CONFIG[metric_type]
    label = config['label']
    trend_key = config['trend_key']
    
    # Line styles for different M values
    M_STYLES = {0: '-', 1: '--', 2: '-.', 3: ':', 20: (0, (3, 1, 1, 1))}
    
    # Select representative benchmarks with good M/D coverage
    benchmarks_to_plot = []
    for benchmark, stats in analysis.items():
        if 'dmcfa' in stats and 'm_trends' in stats['dmcfa']:
            # Count how many D/M combinations exist
            total_points = sum(len(m_dict) for m_dict in stats['dmcfa']['m_trends'].values())
            if total_points >= 6:  # At least 6 data points
                benchmarks_to_plot.append((benchmark, total_points))
    
    # Sort by coverage and take top 6
    benchmarks_to_plot.sort(key=lambda x: x[1], reverse=True)
    benchmarks_to_plot = [b[0] for b in benchmarks_to_plot[:6]]
    
    if not benchmarks_to_plot:
        print(f"No benchmarks with sufficient M/D coverage for {metric_type}")
        return
    
    fig, axes = plt.subplots(2, 3, figsize=(18, 10))
    axes = axes.flatten()
    
    for idx, benchmark in enumerate(benchmarks_to_plot):
        if idx >= len(axes):
            break
        
        ax = axes[idx]
        
        # Plot both DMCFA and DMCFAE
        for analysis_type, color, label_prefix in [('dmcfa', '#1f77b4', 'DMCFA'), 
                                                     ('dmcfae', '#ff7f0e', 'DMCFAE')]:
            if analysis_type not in analysis[benchmark] or 'm_trends' not in analysis[benchmark][analysis_type]:
                continue
            
            m_trends = analysis[benchmark][analysis_type]['m_trends']
            
            # Get all M values that appear
            all_m_values = set()
            for d_dict in m_trends.values():
                all_m_values.update(int(m) for m in d_dict.keys())
            
            # Plot line for each M value
            for m_val in sorted(all_m_values):
                d_values = []
                metric_values = []
                
                for d_val in sorted([int(d) for d in m_trends.keys()]):
                    if str(m_val) in m_trends[str(d_val)]:
                        d_values.append(d_val)
                        metric_values.append(m_trends[str(d_val)][str(m_val)].get(trend_key, 0))
                
                if len(d_values) >= 2:  # Only plot if we have at least 2 points
                    linestyle = M_STYLES.get(m_val, '-')
                    ax.plot(d_values, metric_values, 
                           linestyle=linestyle, color=color, marker='o',
                           linewidth=2, markersize=4,
                           label=f'{label_prefix} M={m_val}', alpha=0.8)
        
        ax.set_xlabel('D Parameter')
        ax.set_ylabel(label)
        ax.set_title(benchmark)
        ax.set_ylim([0, 1.05])
        ax.grid(True, alpha=0.3)
        ax.legend(fontsize=7, ncol=2)
    
    # Hide unused subplots
    for idx in range(len(benchmarks_to_plot), len(axes)):
        axes[idx].set_visible(False)
    
    plt.suptitle(f'M Parameter Effect Across D: {label}', fontsize=14, y=0.995)
    plt.tight_layout()
    output_path = GRAPHS_DIR / f'{metric_type}_m_across_d_comparison.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"Saved: {output_path}")
    plt.close()

def plot_metric_by_sensitivity(analysis: dict, metric_type: str = 'precision'):
    """Plot metric distribution across different D parameter values."""
    config = METRIC_CONFIG[metric_type]
    label = config['label']
    trend_key = config['trend_key']
    
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    
    for analysis_type, ax, title in [('dmcfa', ax1, 'DMCFA'), ('dmcfae', ax2, 'DMCFA-Exp')]:
        # Collect metric by D parameter
        by_d = defaultdict(list)
        
        for benchmark, stats in analysis.items():
            if analysis_type in stats and 'd_trends' in stats[analysis_type]:
                for d_str, trend_data in stats[analysis_type]['d_trends'].items():
                    by_d[int(d_str)].append(trend_data.get(trend_key, 0))
        
        if not by_d:
            continue
        
        # Create grouped histogram
        d_values = sorted(by_d.keys())
        bins = np.linspace(0, 1, 11)  # 10 bins from 0 to 1
        
        width = 0.12
        x = np.arange(len(bins) - 1)
        
        for i, d_val in enumerate(d_values):
            values = by_d[d_val]
            counts, _ = np.histogram(values, bins=bins)
            color = D_COLORS.get(d_val, '#888888')
            offset = (i - len(d_values)/2) * width
            ax.bar(x + offset, counts, width, label=f'D={d_val}', 
                   color=color, alpha=0.7, edgecolor='black', linewidth=0.5)
        
        ax.set_xlabel(label)
        ax.set_ylabel('Number of Benchmarks')
        ax.set_title(f'{title}: {label} Distribution by D Parameter')
        ax.set_xticks(x)
        ax.set_xticklabels([f'{bins[i]:.1f}' for i in range(len(bins)-1)], rotation=45)
        ax.legend()
        ax.grid(True, alpha=0.3, axis='y')
    
    plt.tight_layout()
    output_path = GRAPHS_DIR / f'{metric_type}_by_sensitivity.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"Saved: {output_path}")
    plt.close()

def main():
    """Generate all visualizations."""
    print("Loading analysis data...")
    analysis = load_analysis()
    
    GRAPHS_DIR.mkdir(parents=True, exist_ok=True)
    
    print("\nGenerating visualizations...")
    
    # Generate graphs for each metric
    for metric_type in ['precision', 'proxy']:
        label = METRIC_CONFIG[metric_type]['label']
        print(f"\n--- Analysis for {label} ---")
        
        print(f"  - {label} vs Cost")
        plot_metric_vs_cost(analysis, metric_type)
        
        print(f"  - {label} Parameter Sensitivity")
        plot_parameter_sensitivity(analysis, metric_type)
        
        print(f"  - {label} by Sensitivity Distribution")
        plot_metric_by_sensitivity(analysis, metric_type)
        
        print(f"  - {label} M across D Comparison")
        plot_m_across_d_lines(analysis, metric_type)
    
    print("\n--- Additional Analyis ---")
    print("  - Cost Distribution")
    plot_cost_distribution(analysis)
    
    print(f"\nAll graphs saved to {GRAPHS_DIR}/")

if __name__ == '__main__':
    main()
