#!/usr/bin/env python3
"""
Simplified benchmark analysis focusing on precision, proxy metrics, and costs.
Integrates LOC data as an additional dimension.
"""

import csv
import json
from pathlib import Path
from collections import defaultdict
from statistics import mean, median, stdev
from typing import Dict, List, Optional

RESULTS_BASE = Path("benchmarks/results")
ANALYSIS_DIR = Path("benchmarks/analysis")
OUTPUT_FILE = ANALYSIS_DIR / "benchmark-summary.json"

def load_loc_data() -> Dict[str, int]:
    """
    Load LOC data from Koka analysis output.
    Expected format: function_name => total LOC
    """
    # For now, we'll need to run the Koka analysis and capture output
    # This is a placeholder - we'll integrate properly
    return {}

def get_benchmark_category(filepath: Path) -> str:
    """Determine benchmark category from file path."""
    parts = filepath.parts
    for part in parts:
        if part in ['suite', 'handlers', 'koka-gen', 'rosetta']:
            return part
    return 'unknown'

def load_all_benchmark_results() -> Dict[str, List[Dict]]:
    """
    Load all benchmark results organized by benchmark name.
    Returns: {benchmark_name: [result_rows]}
    """
    all_results = defaultdict(list)
    
    if not RESULTS_BASE.exists():
        return {}
    
    # Iterate through D/M directories
    for d_dir in sorted(RESULTS_BASE.iterdir()):
        if not d_dir.is_dir() or not d_dir.name.isdigit():
            continue
            
        for m_dir in sorted(d_dir.iterdir()):
            if not m_dir.is_dir() or not m_dir.name.isdigit():
                continue
            
            # Find all CSV files
            for csv_file in m_dir.rglob("*.csv"):
                category = get_benchmark_category(csv_file)
                benchmark_name = csv_file.stem
                
                with open(csv_file, 'r') as f:
                    reader = csv.DictReader(f)
                    for row in reader:
                        # Add metadata
                        row['benchmark'] = benchmark_name
                        row['category'] = category
                        row['d_param'] = int(d_dir.name)
                        row['m_param'] = int(m_dir.name)
                        
                        # Parse numeric fields
                        try:
                            row['D'] = int(row.get('D', 0))
                            row['M(K)'] = int(row.get('M(K)', 0))
                            row['Precise'] = float(row.get('Precise', 0))
                            row['NEval'] = int(row.get('NEval', 0))
                            row['NApply'] = int(row.get('NApply', 0))
                            row['AvgEval'] = float(row.get('AvgEval', 0))
                            row['AvgApply'] = float(row.get('AvgApply', 0))
                            row['AvgK'] = float(row.get('AvgK', 0))
                            row['AvgS'] = float(row.get('AvgS', 0))
                            
                            # Compute average time
                            times = []
                            for t in ['Time1', 'Time2', 'Time3']:
                                if t in row and row[t]:
                                    times.append(float(row[t]))
                            row['Time'] = mean(times) if times else 0.0
                            
                            all_results[benchmark_name].append(row)
                        except (ValueError, TypeError) as e:
                            print(f"Warning: Failed to parse row in {csv_file}: {e}")
                            continue
    
    return dict(all_results)

def compute_benchmark_stats(results: List[Dict]) -> Dict:
    """Compute statistics for a benchmark across all runs."""
    if not results:
        return {}
    
    # Group by analysis type
    by_analysis = defaultdict(list)
    for r in results:
        by_analysis[r['Analysis']].append(r)
    
    stats = {}
    for analysis, rows in by_analysis.items():
        # Compute statistics
        precisions = [r['Precise'] for r in rows]
        times = [r['Time'] for r in rows]
        avg_s_values = [r['AvgS'] for r in rows]
        avg_k_values = [r['AvgK'] for r in rows]
        
        # Proxy metric: 1/AvgS (higher is better, represents precision)
        proxies = [1.0/s if s > 0 else 0 for s in avg_s_values]
        
        stats[analysis] = {
            'num_examples': len(rows),
            'precision': {
                'mean': mean(precisions),
                'median': median(precisions),
                'min': min(precisions),
                'max': max(precisions),
                'stdev': stdev(precisions) if len(precisions) > 1 else 0
            },
            'time': {
                'mean': mean(times),
                'median': median(times),
                'min': min(times),
                'max': max(times),
                'stdev': stdev(times) if len(times) > 1 else 0
            },
            'proxy_precision': {
                'mean': mean(proxies),
                'median': median(proxies),
                'min': min(proxies),
                'max': max(proxies)
            },
            'avg_s': {
                'mean': mean(avg_s_values),
                'median': median(avg_s_values)
            },
            'avg_k': {
                'mean': mean(avg_k_values),
                'median': median(avg_k_values)
            },
            'category': rows[0]['category']
        }
    
    return stats

def analyze_parameter_sensitivity(results: List[Dict], analysis_type: str) -> Dict:
    """Analyze how metrics change with D and M parameters."""
    filtered = [r for r in results if r['Analysis'] == analysis_type]
    
    # Group by D parameter
    by_d = defaultdict(list)
    for r in filtered:
        by_d[r['D']].append(r)
    
    d_trends = {}
    for d_val, rows in sorted(by_d.items()):
        times = [r['Time'] for r in rows]
        precisions = [r['Precise'] for r in rows]
        avg_s = [r['AvgS'] for r in rows]
        # Proxy metric: 1/AvgS
        proxies = [1.0/s if s > 0 else 0 for s in avg_s]
        
        d_trends[d_val] = {
            'time_mean': mean(times),
            'precision_mean': mean(precisions),
            'proxy_precision_mean': mean(proxies),
            'avg_s_mean': mean(avg_s),
            'count': len(rows)
        }
    
    # Also track M parameter trends for each D value
    m_trends = {}
    for d_val in sorted(set(r['D'] for r in filtered)):
        m_trends[d_val] = {}
        d_filtered = [r for r in filtered if r['D'] == d_val]
        
        by_m = defaultdict(list)
        for r in d_filtered:
            by_m[r['M(K)']].append(r)
        
        for m_val, rows in sorted(by_m.items()):
            times = [r['Time'] for r in rows]
            precisions = [r['Precise'] for r in rows]
            avg_s = [r['AvgS'] for r in rows]
            # Proxy metric: 1/AvgS
            proxies = [1.0/s if s > 0 else 0 for s in avg_s]
            
            m_trends[d_val][m_val] = {
                'time_mean': mean(times),
                'precision_mean': mean(precisions),
                'proxy_precision_mean': mean(proxies),
                'avg_s_mean': mean(avg_s),
                'count': len(rows)
            }
    
    return {'d_trends': d_trends, 'm_trends': m_trends}

def main():
    """Generate simplified benchmark analysis."""
    print("Loading benchmark results...")
    all_results = load_all_benchmark_results()
    
    print(f"Found {len(all_results)} benchmarks")
    
    # Compute per-benchmark statistics
    summary = {}
    for benchmark, results in all_results.items():
        print(f"  Analyzing {benchmark}...")
        stats = compute_benchmark_stats(results)
        
        # Add parameter sensitivity analysis
        for analysis_type in ['dmcfa', 'dmcfae']:
            if analysis_type in stats:
                param_trends = analyze_parameter_sensitivity(results, analysis_type)
                stats[analysis_type]['d_trends'] = param_trends['d_trends']
                stats[analysis_type]['m_trends'] = param_trends['m_trends']
        
        summary[benchmark] = stats
    
    # Save summary
    ANALYSIS_DIR.mkdir(exist_ok=True)
    with open(OUTPUT_FILE, 'w') as f:
        json.dump(summary, f, indent=2)
    
    print(f"\nSummary saved to {OUTPUT_FILE}")
    
    # Print quick overview
    print("\n" + "="*80)
    print("QUICK OVERVIEW")
    print("="*80)
    
    # Count by category
    by_category = defaultdict(int)
    for benchmark, stats in summary.items():
        if 'dmcfa' in stats:
            category = stats['dmcfa'].get('category', 'unknown')
            by_category[category] += 1
    
    print("\nBenchmarks by category:")
    for category, count in sorted(by_category.items()):
        print(f"  {category}: {count}")
    
    # Show precision issues
    print("\nBenchmarks with < 100% precision (DMCFA):")
    issues = []
    for benchmark, stats in summary.items():
        if 'dmcfa' in stats:
            precision = stats['dmcfa']['precision']['mean']
            if precision < 1.0:
                issues.append((benchmark, precision))
    
    if issues:
        for benchmark, precision in sorted(issues, key=lambda x: x[1]):
            print(f"  {benchmark}: {precision:.1%}")
    else:
        print("  None - all benchmarks have 100% precision!")

if __name__ == '__main__':
    main()
