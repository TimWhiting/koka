#!/usr/bin/env python3
"""
Generate detailed comparisons and insights from benchmark results.
"""

import os
import csv
import json
from pathlib import Path
from collections import defaultdict
from statistics import mean, median
from typing import Dict, List, Tuple

RESULTS_DIR = Path("benchmarks/results/suite")
ANALYSIS_JSON = Path("benchmarks/analysis/suite-analysis.json")

SUITE_FILES = [
    "basic",
    "nondet", 
    "nested",
    "multi-effect",
    "recursion",
    "state-handler",
    "complex-flow",
    "nested-nondet"
]

def load_json_analysis() -> Dict:
    """Load the analysis JSON file."""
    if ANALYSIS_JSON.exists():
        with open(ANALYSIS_JSON, 'r') as f:
            return json.load(f)
    return {}

def analyze_precision_issues(analysis: Dict):
    """Identify benchmarks with precision issues."""
    print("\n" + "="*100)
    print("PRECISION ANALYSIS")
    print("="*100 + "\n")
    
    issues = []
    
    for benchmark, analyses in analysis.items():
        for analysis_key, data in analyses.items():
            if data.get('precision') and data['precision'].get('mean'):
                precision = data['precision']['mean']
                if precision < 1.0:
                    issues.append({
                        'benchmark': benchmark,
                        'analysis': analysis_key,
                        'precision': precision,
                        'count': data['precision'].get('count', 0)
                    })
    
    # Sort by precision (lowest first)
    issues.sort(key=lambda x: x['precision'])
    
    if issues:
        print("Benchmarks with less than 100% precision:")
        print("-" * 80)
        for issue in issues:
            print(f"  {issue['benchmark']:20s} {issue['analysis']:10s}: {issue['precision']:.1%} ({issue['count']} examples)")
    else:
        print("All benchmarks have 100% precision!")

def analyze_complexity_trends(analysis: Dict):
    """Analyze trends in complexity metrics."""
    print("\n" + "="*100)
    print("COMPLEXITY TRENDS")
    print("="*100 + "\n")
    
    # Group by benchmark
    benchmarks_by_size = []
    
    for benchmark, analyses in sorted(analysis.items()):
        dmcfa_data = analyses.get('dmcfa', {})
        if dmcfa_data:
            num_examples = dmcfa_data.get('num_examples', 0)
            avg_time = dmcfa_data.get('time', {}).get('mean', 0)
            avg_nevals = dmcfa_data.get('nevals', {}).get('mean', 0)
            
            benchmarks_by_size.append({
                'name': benchmark,
                'examples': num_examples,
                'avg_time': avg_time,
                'avg_nevals': avg_nevals
            })
    
    # Sort by number of examples
    benchmarks_by_size.sort(key=lambda x: x['examples'])
    
    print("Benchmarks ranked by number of examples:")
    print("-" * 80)
    print(f"{'Benchmark':<20} {'Examples':<12} {'Avg Time':<15} {'Avg NEval':<15}")
    print("-" * 80)
    
    for b in benchmarks_by_size:
        print(f"{b['name']:<20} {b['examples']:<12} {b['avg_time']:<15.4f} {b['avg_nevals']:<15.1f}")

def analyze_time_distribution(analysis: Dict):
    """Analyze time distribution across benchmarks."""
    print("\n" + "="*100)
    print("TIME DISTRIBUTION ANALYSIS")
    print("="*100 + "\n")
    
    # Identify fast, normal, and slow benchmarks
    benchmarks_by_time = []
    
    for benchmark, analyses in analysis.items():
        dmcfa_data = analyses.get('dmcfa', {})
        if dmcfa_data and dmcfa_data.get('time'):
            avg_time = dmcfa_data['time'].get('mean', 0)
            max_time = dmcfa_data['time'].get('max', 0)
            benchmarks_by_time.append({
                'name': benchmark,
                'avg': avg_time,
                'max': max_time,
                'examples': dmcfa_data.get('num_examples', 0)
            })
    
    # Sort by average time
    benchmarks_by_time.sort(key=lambda x: x['avg'], reverse=True)
    
    print("Benchmarks ranked by average execution time:")
    print("-" * 80)
    print(f"{'Benchmark':<20} {'Avg Time':<15} {'Max Time':<15} {'Examples':<10}")
    print("-" * 80)
    
    for b in benchmarks_by_time:
        print(f"{b['name']:<20} {b['avg']:<15.4f}s {b['max']:<15.4f}s {b['examples']:<10}")
    
    # Categorize
    fast = [b for b in benchmarks_by_time if b['avg'] < 0.01]
    normal = [b for b in benchmarks_by_time if 0.01 <= b['avg'] < 0.05]
    slow = [b for b in benchmarks_by_time if b['avg'] >= 0.05]
    
    print("\nBenchmark categories:")
    print(f"  Fast   (<10ms):    {len(fast)} benchmarks")
    print(f"  Normal (10-50ms):  {len(normal)} benchmarks")
    print(f"  Slow   (>50ms):    {len(slow)} benchmarks")

def find_anomalies(analysis: Dict):
    """Find anomalous results (outliers)."""
    print("\n" + "="*100)
    print("ANOMALY DETECTION")
    print("="*100 + "\n")
    
    anomalies = []
    
    for benchmark, analyses in analysis.items():
        dmcfa_data = analyses.get('dmcfa', {})
        if dmcfa_data and dmcfa_data.get('time'):
            max_time = dmcfa_data['time'].get('max', 0)
            mean_time = dmcfa_data['time'].get('mean', 0)
            
            # Flag if max is significantly higher than mean (e.g., 10x or more)
            if mean_time > 0 and max_time / mean_time > 10:
                anomalies.append({
                    'benchmark': benchmark,
                    'max_time': max_time,
                    'mean_time': mean_time,
                    'ratio': max_time / mean_time
                })
    
    if anomalies:
        print("Benchmarks with outlier results (max >> mean):")
        print("-" * 80)
        for anom in sorted(anomalies, key=lambda x: x['ratio'], reverse=True):
            print(f"  {anom['benchmark']:<20}: {anom['ratio']:.1f}x (mean={anom['mean_time']:.4f}s, max={anom['max_time']:.4f}s)")
    else:
        print("No significant anomalies detected.")

def generate_comparison_table(analysis: Dict):
    """Generate a comparison table of all benchmarks."""
    print("\n" + "="*100)
    print("SUMMARY COMPARISON TABLE")
    print("="*100 + "\n")
    
    print(f"{'Benchmark':<20} {'Examples':<10} {'Avg Time':<12} {'Precision':<12} {'Avg NEval':<12} {'Avg NApply':<12}")
    print("-" * 100)
    
    for benchmark in sorted(SUITE_FILES):
        if benchmark not in analysis:
            continue
        
        dmcfa_data = analysis[benchmark].get('dmcfa', {})
        examples = dmcfa_data.get('num_examples', 0)
        avg_time = dmcfa_data.get('time', {}).get('mean', 0)
        precision = dmcfa_data.get('precision', {}).get('mean', 0)
        avg_nevals = dmcfa_data.get('nevals', {}).get('mean', 0)
        avg_napplies = dmcfa_data.get('napplies', {}).get('mean', 0)
        
        print(f"{benchmark:<20} {examples:<10} {avg_time:<12.4f}s {precision:<12.1%} {avg_nevals:<12.1f} {avg_napplies:<12.1f}")

def main():
    """Main entry point."""
    print("Loading benchmark analysis...")
    
    analysis = load_json_analysis()
    if not analysis:
        print("Error: Could not load analysis data")
        return
    
    # Run analyses
    generate_comparison_table(analysis)
    analyze_complexity_trends(analysis)
    analyze_time_distribution(analysis)
    analyze_precision_issues(analysis)
    find_anomalies(analysis)
    
    print("\n" + "="*100)
    print("Analysis report generation complete!")
    print("="*100)

if __name__ == "__main__":
    main()
