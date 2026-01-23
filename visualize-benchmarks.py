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
    },
    'proxy_k': {
        'label': 'Proxy Precision (1/AvgK)',
        'filename_suffix': '_proxy_k',
        'json_key': 'proxy_precision_k',
        'trend_key': 'proxy_precision_k_mean'
    },
    'cost': {
        'label': 'Execution Time (s)',
        'filename_suffix': '_cost',
        'json_key': 'time',
        'trend_key': 'time_mean'
    },
    'cost_loc': {
        'label': 'Cost per LOC (s/LOC)',
        'filename_suffix': '_cost_loc',
        'json_key': 'cost_per_loc',
        'trend_key': 'cost_per_loc'
    },
    'prec_eval': {
        'label': 'Evaluation Precision (Ratio)',
        'filename_suffix': '_prec_eval',
        'json_key': 'prec_eval_ratio',
        'trend_key': 'prec_eval_ratio_mean'
    },
    'prec_stack': {
        'label': 'Stack Precision (Ratio)',
        'filename_suffix': '_prec_stack',
        'json_key': 'prec_s_ratio',
        'trend_key': 'prec_s_ratio_mean'
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
    
    fig, axes = plt.subplots(2, 3, figsize=(18, 12))
    axes = axes.flatten()
    
    for idx, benchmark in enumerate(benchmarks_to_plot):
        if idx >= len(axes):
            break
        
        ax = axes[idx]
        
        all_lines = []
        ax2 = None
        if metric_type != 'cost':
            ax2 = ax.twinx()

        for a_type, base_color, a_label in [('dmcfa', '#1f77b4', 'DMCFA'), 
                                           ('dmcfae', '#ff7f0e', 'DMCFAE')]:
            if a_type not in analysis[benchmark]:
                continue
                
            m_trends = analysis[benchmark][a_type].get('m_trends', {})
            d_values = sorted([int(d) for d in m_trends.keys()])
            
            # Show trends for both M=0 and M=1
            for m_val, linestyle in [(0, '--'), (1, '-')]:
                plot_d = []
                plot_times = []
                plot_metrics = []
                
                for d in d_values:
                    if str(m_val) in m_trends[str(d)]:
                        trend = m_trends[str(d)][str(m_val)]
                        plot_d.append(d)
                        plot_times.append(trend['time_mean'])
                        plot_metrics.append(trend.get(trend_key, 0))
                
                if not plot_d: continue

                # Map D values to X positions
                x_pos = []
                for d in plot_d:
                    if d <= 3: x_pos.append(float(d))
                    elif d == 20: x_pos.append(4.5)
                    elif d == 100: x_pos.append(5.5)
                
                if metric_type == 'cost':
                    l = ax.plot(x_pos, plot_times, color=base_color, linestyle=linestyle,
                               marker='o', markersize=4, linewidth=1.5,
                               label=f'{a_label} M={m_val}')
                    all_lines.extend(l)
                else:
                    # Performance lines (Metric)
                    l2 = ax2.plot(x_pos, plot_metrics, color=base_color, linestyle=linestyle,
                                 marker='s', markersize=4, linewidth=1.5,
                                 label=f'{a_label} M={m_val}')
                    all_lines.extend(l2)
                    
                    # Add execution time as light underlay only for M=1 to avoid clutter
                    if m_val == 1:
                        ax.plot(x_pos, plot_times, color=base_color, linestyle=':', 
                               alpha=0.2, linewidth=1)

        # Visual break and axis config
        ax.axvline(x=3.75, color='gray', linestyle=':', alpha=0.5, linewidth=1)
        x_ticks = [0, 1, 2, 3, 4.5, 5.5]
        ax.set_xticks(x_ticks)
        ax.set_xticklabels(['0', '1', '2', '3', '20', '100'])
        
        ax.set_xlabel('D Parameter')
        ax.set_title(benchmark, fontsize=10)
        ax.grid(True, alpha=0.2)
        
        if metric_type == 'cost':
            ax.set_ylabel('Execution Time (s)')
        else:
            ax.set_ylabel('Time (s)', color='gray', alpha=0.5)
            ax2.set_ylabel(label)
            ax2.set_ylim([0, 1.05])
            
        ax.legend(all_lines, [l.get_label() for l in all_lines], 
                 loc='upper left', fontsize=6, ncol=2)

    # Final cleanup and save
    for idx in range(len(benchmarks_to_plot), len(axes)):
        axes[idx].set_visible(False)
    
    plt.suptitle(f'Parameter Sensitivity: D Effect for M=0 vs M=1', fontsize=14, y=0.98)
    plt.tight_layout(rect=[0, 0.03, 1, 0.95])
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
                
                all_d_sorted = sorted([int(d) for d in m_trends.keys()])
                for d_val in all_d_sorted:
                    if str(m_val) in m_trends[str(d_val)]:
                        d_values.append(d_val)
                        metric_values.append(m_trends[str(d_val)][str(m_val)].get(trend_key, 0))
                
                if len(d_values) >= 2:  # Only plot if we have at least 2 points
                    # Map D values to X positions for axis breaks
                    x_positions = []
                    for d in d_values:
                        if d <= 3:
                            x_positions.append(float(d))
                        elif d == 20:
                            x_positions.append(4.5)
                        elif d == 100:
                            x_positions.append(5.5)
                        else:
                            x_positions.append(float(d))

                    linestyle = M_STYLES.get(m_val, '-')
                    ax.plot(x_positions, metric_values, 
                           linestyle=linestyle, color=color, marker='o',
                           linewidth=2, markersize=4,
                           label=f'{label_prefix} M={m_val}', alpha=0.8)
        
        # Consistent X-axis labels for broken axis
        x_ticks = []
        x_labels = []
        possible_d = [0, 1, 2, 3, 20, 100]
        for d in possible_d:
            if d <= 3: x_ticks.append(float(d))
            elif d == 20: x_ticks.append(4.5)
            elif d == 100: x_ticks.append(5.5)
            x_labels.append(str(d))
            
        ax.set_xticks(x_ticks)
        ax.set_xticklabels(x_labels)
        
        # Add visual break line if 20 or 100 are present
        ax.axvline(x=3.75, color='gray', linestyle=':', alpha=0.5, linewidth=1)
        
        ax.set_xlabel('D Parameter')
        ax.set_ylabel(label)
        ax.set_title(benchmark)
        if metric_type != 'cost':
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
        
        if metric_type == 'cost':
            # Use different bins for execution time: 0, 0.1, 1, 10, 100, 300
            bins = [0, 0.1, 1, 5, 20, 60, 120, 300]
            x_labels = ['<0.1', '0.1-1', '1-5', '5-20', '20-60', '60-120', '120-300']
        else:
            bins = np.linspace(0, 1, 11)  # 10 bins from 0 to 1
            x_labels = [f'{b:.1f}' for b in bins[1:]]
            
        width = 0.8 / len(d_values)
        x = np.arange(len(bins) - 1)
        
        for i, d_val in enumerate(d_values):
            values = by_d[d_val]
            counts, _ = np.histogram(values, bins=bins)
            color = D_COLORS.get(d_val, '#888888')
            offset = (i - len(d_values)/2 + 0.5) * width
            ax.bar(x + offset, counts, width, label=f'D={d_val}', 
                   color=color, alpha=0.7, edgecolor='black', linewidth=0.5)
        
        ax.set_xlabel(label)
        ax.set_ylabel('Number of Benchmarks')
        ax.set_title(f'{title}: {label} Distribution by D Parameter')
        ax.set_xticks(x)
        ax.set_xticklabels(x_labels, rotation=45 if metric_type == 'cost' else 0)
        ax.legend()
        ax.grid(True, alpha=0.3, axis='y')
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
    for metric_type in METRIC_CONFIG.keys():
        label = METRIC_CONFIG[metric_type]['label']
        print(f"\n--- Analysis for {label} ---")
        
        if metric_type != 'cost':
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
    
    print("\n--- Additional Analyis ---")
    print("  - Cost Distribution")
    plot_cost_distribution(analysis)
    
    print(f"\nAll graphs saved to {GRAPHS_DIR}/")

if __name__ == '__main__':
    main()
