#!/usr/bin/env python3
"""
Analyze and aggregate benchmark results from the suite, handlers, and rosetta.
"""

import os
import csv
import json
from pathlib import Path
from collections import defaultdict
from statistics import mean, stdev, median
from typing import Dict, List, Tuple

# Configuration
RESULTS_BASE = Path("benchmarks/results")
RESULTS_DIRS = [RESULTS_BASE / "suite", RESULTS_BASE / "handlers", RESULTS_BASE / "rosetta"]
OUTPUT_DIR = Path("benchmarks/analysis")

def load_benchmark_names() -> List[str]:
    """Load benchmark names by scanning the results directory structure."""
    benchmarks = set()
    
    # Walk through the results directory
    # Structure: benchmarks/results/<d>/<m>/<category>/<benchmark>.csv
    if not RESULTS_BASE.exists():
        return []
        
    for d_dir in RESULTS_BASE.iterdir():
        if not d_dir.is_dir(): continue
        for m_dir in d_dir.iterdir():
            if not m_dir.is_dir(): continue
            
            # Now we are at specific sensitivity level
            # Walk recursively to find all .csv files
            for csv_file in m_dir.rglob("*.csv"):
                # Get path relative to m_dir (e.g., suite/basic.csv)
                rel_path = csv_file.relative_to(m_dir)
                # Remove .csv extension
                bench_name = str(rel_path.with_suffix(''))
                benchmarks.add(bench_name)
                
    return sorted(list(benchmarks))

SUITE_FILES = load_benchmark_names()

ANALYSIS_TYPES = {
    "dmcfa": "DMCFA",
    "dmcfae": "DMCFA-Exp",
    "kcfa": "KCFA"
}

def load_csv_results(filepath: Path) -> List[Dict]:
    """Load results from a CSV file."""
    results = []
    try:
        with open(filepath, 'r') as f:
            reader = csv.DictReader(f)
            for row in reader:
                results.append(row)
    except FileNotFoundError:
        print(f"Warning: {filepath} not found")
    return results

def parse_metrics(row: Dict) -> Dict:
    """Parse a result row and convert numeric fields."""
    parsed = dict(row)
    
    # Fields to handle
    int_fields = ['NEval', 'NApply', 'NK', 'NS', 'SumEval', 'SumApply', 'SumK', 'SumS', 'PrecEval', 'PrecApply', 'PrecK', 'PrecS']
    float_fields = ['D', 'M(K)', 'Precise', 'Time1', 'Time2', 'Time3', 'Time']
    
    for field in int_fields:
        if field in parsed and parsed[field]:
            try:
                val_str = str(parsed[field]).strip().lower()
                if val_str == 'timeout':
                    parsed[field] = 0
                else:
                    parsed[field] = int(float(parsed[field]))
            except ValueError:
                parsed[field] = 0
                
    for field in float_fields:
        if field in parsed and parsed[field]:
            try:
                val_str = str(parsed[field]).strip().lower()
                if val_str == 'timeout':
                    parsed[field] = 300.0
                else:
                    parsed[field] = float(parsed[field])
            except ValueError:
                pass

    # Compute Averages from Sums if they don't exist
    if 'SumS' in parsed and 'NS' in parsed:
        parsed['AvgS'] = float(parsed['SumS']) / float(parsed['NS']) if parsed['NS'] > 0 else 0.0
    
    if 'SumK' in parsed and 'NK' in parsed:
        parsed['AvgK'] = float(parsed['SumK']) / float(parsed['NK']) if parsed['NK'] > 0 else 0.0
        parsed['AvgMK'] = parsed['AvgK']

    if 'SumEval' in parsed and 'NEval' in parsed:
        parsed['AvgEval'] = float(parsed['SumEval']) / float(parsed['NEval']) if parsed['NEval'] > 0 else 0.0

    if 'SumApply' in parsed and 'NApply' in parsed:
        parsed['AvgApply'] = float(parsed['SumApply']) / float(parsed['NApply']) if parsed['NApply'] > 0 else 0.0
    
    # New precision metrics
    if 'PrecEval' in parsed and 'NEval' in parsed:
        parsed['PrecRatioEval'] = float(parsed['PrecEval']) / float(parsed['NEval']) if parsed['NEval'] > 0 else 0.0
    if 'PrecApply' in parsed and 'NApply' in parsed:
        parsed['PrecRatioApply'] = float(parsed['PrecApply']) / float(parsed['NApply']) if parsed['NApply'] > 0 else 0.0
    if 'PrecS' in parsed and 'NS' in parsed:
        parsed['PrecRatioS'] = float(parsed['PrecS']) / float(parsed['NS']) if parsed['NS'] > 0 else 0.0
    if 'PrecK' in parsed and 'NK' in parsed:
        parsed['PrecRatioK'] = float(parsed['PrecK']) / float(parsed['NK']) if parsed['NK'] > 0 else 0.0

    # Compute composite Time if missing but components exist
    if 'Time' not in parsed or not parsed['Time']:
        times = []
        for t_col in ['Time1', 'Time2', 'Time3']:
            if t_col in parsed and parsed[t_col]:
                try:
                    times.append(float(parsed[t_col]))
                except ValueError:
                    pass
        if times:
            parsed['Time'] = mean(times)
            
    return parsed

def extract_sensitivity_params(results: List[Dict]) -> Tuple[set, set]:
    """Extract unique D and M(K) values from results."""
    d_values = set()
    m_values = set()
    
    for row in results:
        if 'D' in row and row['D']:
            try:
                d_values.add(int(float(row['D'])))
            except (ValueError, TypeError):
                pass
        if 'M(K)' in row and row['M(K)']:
            try:
                m_values.add(int(float(row['M(K)'])))
            except (ValueError, TypeError):
                pass
    
    return d_values, m_values

def aggregate_by_analysis(results: List[Dict]) -> Dict[str, List[Dict]]:
    """Group results by analysis type using the 'Analysis' column."""
    by_analysis = defaultdict(list)
    for row in results:
        # The 'Analysis' column contains the analysis name (e.g. 'dmcfa')
        analysis = row.get('Analysis')
        if analysis and analysis in ANALYSIS_TYPES:
            by_analysis[analysis].append(row)
    return by_analysis

def compute_statistics(values: List[float]) -> Dict:
    """Compute statistics for a list of values."""
    if not values:
        return {}
    
    valid_values = [v for v in values if isinstance(v, (int, float))]
    if not valid_values:
        return {}
    
    return {
        'count': len(valid_values),
        'min': min(valid_values),
        'max': max(valid_values),
        'mean': mean(valid_values),
        'median': median(valid_values),
        'stdev': stdev(valid_values) if len(valid_values) > 1 else 0
    }


def collect_benchmark_results(benchmark_name: str) -> List[Dict]:
    """Collect all results for a benchmark across all sensitivity levels."""
    all_results = []
    
    # Iterate over all d/m directories
    if not RESULTS_BASE.exists():
        return []
        
    for d_dir in RESULTS_BASE.iterdir():
        if not d_dir.is_dir(): continue
        # Try to parse d from directory name
        try:
            # Skip non-numeric directories if any (though run-benchmarks produces numeric)
            if not d_dir.name.isdigit(): continue
            d_val = int(d_dir.name)
        except ValueError:
            continue
            
        for m_dir in d_dir.iterdir():
            if not m_dir.is_dir(): continue
            try:
                if not m_dir.name.isdigit(): continue
                m_val = int(m_dir.name)
            except ValueError:
                continue

            # Check if benchmark file exists in this d/m combination
            # benchmark_name is like "suite/basic"
            csv_path = m_dir / f"{benchmark_name}.csv"
            
            if csv_path.exists():
                file_results = load_csv_results(csv_path)
                # Ensure D and M(K) are set correctly in case they are missing or parsed wrong
                # But they should be in the CSV content. 
                # Older run-benchmarks put them there. 
                # The gathering logic below expects to extract them.
                all_results.extend(file_results)
                
    return all_results

def analyze_suite_benchmark(benchmark_name: str) -> Dict:
    """Analyze a single suite benchmark across all analyses and sensitivity parameters."""
    
    analysis_results = {}
    
    # Collect all raw results from all d/m directories
    all_raw_results = collect_benchmark_results(benchmark_name)
    
    if not all_raw_results:
        # print(f"Warning: No results found for {benchmark_name}")
        return {}

    # Separate by analysis type
    by_analysis = aggregate_by_analysis(all_raw_results)
    
    for analysis_key, rows in by_analysis.items():
        if not rows:
            continue
        
        analysis_name = ANALYSIS_TYPES[analysis_key]
        
        # Parse and analyze
        parsed_results = [parse_metrics(r) for r in rows]
        
        # Extract sensitivity parameters
        d_values, m_values = extract_sensitivity_params(parsed_results)
        
        # Organize results by D and M(K) independently
        by_d = defaultdict(list)
        by_m = defaultdict(list)
        by_d_m = defaultdict(lambda: defaultdict(list))
        
        for result in parsed_results:
            try:
                d_val = result.get('D')
                m_val = result.get('M(K)')
                d = int(float(d_val)) if d_val is not None else 0
                m = int(float(m_val)) if m_val is not None else 0
            except (ValueError, TypeError):
                continue
            by_d[d].append(result)
            by_m[m].append(result)
            by_d_m[d][m].append(result)
            
        # Extract metrics for overall analysis
        times = [r.get('Time') for r in parsed_results if isinstance(r.get('Time'), (int, float))]
        nevals = [r.get('NEval') for r in parsed_results if isinstance(r.get('NEval'), (int, float))]
        napplies = [r.get('NApply') for r in parsed_results if isinstance(r.get('NApply'), (int, float))]
        nks = [r.get('NK') for r in parsed_results if isinstance(r.get('NK'), (int, float))]
        nss = [r.get('NS') for r in parsed_results if isinstance(r.get('NS'), (int, float))]
        precisions = [r.get('Precise') for r in parsed_results if isinstance(r.get('Precise'), (int, float))]
        
        # New precision ratios
        prec_evals = [r.get('PrecRatioEval', 0.0) for r in parsed_results]
        prec_applies = [r.get('PrecRatioApply', 0.0) for r in parsed_results]
        prec_s = [r.get('PrecRatioS', 0.0) for r in parsed_results]
        prec_k = [r.get('PrecRatioK', 0.0) for r in parsed_results]

        # Analyze trends across D values
        d_trends = {}
        for d in sorted(d_values):
            d_results = by_d[d]
            d_trends[d] = {
                'time': compute_statistics([r.get('Time') for r in d_results]),
                'nevals': compute_statistics([r.get('NEval') for r in d_results]),
                'napplies': compute_statistics([r.get('NApply') for r in d_results]),
                'precision': compute_statistics([r.get('Precise') for r in d_results])
            }
        
        # Analyze trends across M(K) values
        m_trends = {}
        for m in sorted(m_values):
            m_results = by_m[m]
            m_trends[m] = {
                'time': compute_statistics([r.get('Time') for r in m_results]),
                'nevals': compute_statistics([r.get('NEval') for r in m_results]),
                'napplies': compute_statistics([r.get('NApply') for r in m_results]),
                'precision': compute_statistics([r.get('Precise') for r in m_results])
            }
        
        # Analyze trends across both D and M(K) (2D breakdown)
        d_m_trends = {}
        for d in sorted(d_values):
            d_m_trends[d] = {}
            for m in sorted(m_values):
                d_m_results = by_d_m[d][m]
                d_m_trends[d][m] = {
                    'time': compute_statistics([r.get('Time') for r in d_m_results]),
                    'nevals': compute_statistics([r.get('NEval') for r in d_m_results]),
                    'napplies': compute_statistics([r.get('NApply') for r in d_m_results]),
                    'precision': compute_statistics([r.get('Precise') for r in d_m_results])
                }
        
        analysis_results[analysis_key] = {
            'name': analysis_name,
            'num_examples': len(parsed_results),
            'd_values': sorted(d_values),
            'm_values': sorted(m_values),
            'time': compute_statistics(times),
            'nevals': compute_statistics(nevals),
            'napplies': compute_statistics(napplies),
            'nks': compute_statistics(nks),
            'nss': compute_statistics(nss),
            'precision': compute_statistics(precisions),
            'prec_eval_ratio': compute_statistics(prec_evals),
            'prec_apply_ratio': compute_statistics(prec_applies),
            'prec_s_ratio': compute_statistics(prec_s),
            'prec_k_ratio': compute_statistics(prec_k),
            'd_trends': d_trends,
            'm_trends': m_trends,
            'd_m_trends': d_m_trends,
            'raw_results': parsed_results
        }
    
    return analysis_results

def generate_summary_report() -> Dict:
    """Generate a summary report for all suite benchmarks."""
    summary = {}
    
    for benchmark in SUITE_FILES:
        print(f"Analyzing {benchmark}...")
        analysis = analyze_suite_benchmark(benchmark)
        if analysis:
            summary[benchmark] = analysis
    
    return summary

def print_summary_table(summary: Dict):
    """Print a nicely formatted summary table."""
    print("\n" + "="*100)
    print("BENCHMARK SUITE ANALYSIS SUMMARY")
    print("="*100 + "\n")
    
    for benchmark, analyses in summary.items():
        print(f"\n{benchmark.upper()}")
        print("-" * 80)
        
        for analysis_key, data in analyses.items():
            print(f"\n  {data['name']}:")
            print(f"    Examples: {data['num_examples']}")
            print(f"    D values: {data.get('d_values', [])}")
            print(f"    M(K) values: {data.get('m_values', [])}")
            
            if data['time']:
                t = data['time']
                print(f"    Overall Time (s):    min={t['min']:.4f}, max={t['max']:.4f}, mean={t['mean']:.4f}, median={t['median']:.4f}")
            
            # Show D trends
            if data.get('d_trends'):
                print(f"    Time by D value:")
                for d in sorted(data['d_trends'].keys()):
                    d_stats = data['d_trends'][d]['time']
                    if d_stats:
                        print(f"      D={d}: {d_stats['mean']:.4f}s (n={d_stats['count']})")
            
            # Show M(K) trends
            if data.get('m_trends'):
                print(f"    Time by M(K) value:")
                for m in sorted(data['m_trends'].keys()):
                    m_stats = data['m_trends'][m]['time']
                    if m_stats:
                        print(f"      M(K)={m}: {m_stats['mean']:.4f}s (n={m_stats['count']})")
            
            if data['nevals']:
                n = data['nevals']
                print(f"    NEval:       min={n['min']:.0f}, max={n['max']:.0f}, mean={n['mean']:.1f}")
            
            if data['napplies']:
                na = data['napplies']
                print(f"    NApply:      min={na['min']:.0f}, max={na['max']:.0f}, mean={na['mean']:.1f}")
            
            if data['precision']:
                p = data['precision']
                print(f"    Precision:   count={p['count']}, mean={p['mean']:.3f}")

def save_json_report(summary: Dict, output_file: Path):
    """Save the summary as a JSON file."""
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    # Convert for JSON serialization
    json_data = {}
    for benchmark, analyses in summary.items():
        json_data[benchmark] = {}
        for analysis_key, data in analyses.items():
            # Convert d_m_trends to use string keys for JSON
            d_m_trends = {}
            if 'd_m_trends' in data:
                for d_key, m_dict in data['d_m_trends'].items():
                    d_m_trends[str(d_key)] = {str(m_key): v for m_key, v in m_dict.items()}
            
            json_data[benchmark][analysis_key] = {
                'name': data['name'],
                'num_examples': data['num_examples'],
                'd_values': data.get('d_values', []),
                'm_values': data.get('m_values', []),
                'time': data['time'],
                'nevals': data['nevals'],
                'napplies': data['napplies'],
                'nks': data.get('nks', {}),
                'nss': data.get('nss', {}),
                'precision': data['precision'],
                'prec_eval_ratio': data.get('prec_eval_ratio', {}),
                'prec_apply_ratio': data.get('prec_apply_ratio', {}),
                'prec_s_ratio': data.get('prec_s_ratio', {}),
                'prec_k_ratio': data.get('prec_k_ratio', {}),
                'd_trends': {str(k): v for k, v in data.get('d_trends', {}).items()},
                'm_trends': {str(k): v for k, v in data.get('m_trends', {}).items()},
                'd_m_trends': d_m_trends
            }
    
    with open(output_file, 'w') as f:
        json.dump(json_data, f, indent=2)
    
    print(f"\nJSON report saved to {output_file}")

def compare_analyses(summary: Dict):
    """Compare different analysis types."""
    print("\n" + "="*100)
    print("ANALYSIS COMPARISON")
    print("="*100 + "\n")
    
    # Compare execution times across all benchmarks
    times_by_analysis = defaultdict(list)
    
    for benchmark, analyses in summary.items():
        for analysis_key, data in analyses.items():
            if data.get('time'):
                times_by_analysis[analysis_key].append(data['time']['mean'])
    
    print("\nAverage Time per Benchmark (seconds):")
    print("-" * 60)
    for analysis_key in sorted(times_by_analysis.keys()):
        times = times_by_analysis[analysis_key]
        if times:
            avg_time = mean(times)
            print(f"  {ANALYSIS_TYPES[analysis_key]:15s}: {avg_time:10.4f}s (across {len(times)} benchmarks)")

def main():
    """Main entry point."""
    print("Starting benchmark result analysis...")
    
    if not RESULTS_BASE.exists():
        print(f"Error: Results directory {RESULTS_BASE} not found")
        return
    
    # Generate summary
    summary = generate_summary_report()
    
    # Print reports
    print_summary_table(summary)
    compare_analyses(summary)
    
    # Save JSON report
    output_dir = OUTPUT_DIR
    output_dir.mkdir(parents=True, exist_ok=True)
    json_file = output_dir / "suite-analysis.json"
    save_json_report(summary, json_file)
    
    print("\n" + "="*100)
    print("Analysis complete!")
    print("="*100)

if __name__ == "__main__":
    main()
