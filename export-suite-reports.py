#!/usr/bin/env python3
"""
Export and generate comparison reports for benchmark results.
"""

import csv
import json
from pathlib import Path
from typing import Dict, List
from collections import defaultdict

RESULTS_DIR = Path("benchmarks/results")
ANALYSIS_JSON = Path("benchmarks/analysis/suite-analysis.json")
EXPORT_DIR = Path("benchmarks/analysis/exports")

def load_suite_files_from_results() -> List[str]:
    """Load benchmark names by scanning the results directory structure."""
    benchmarks = set()
    
    if not RESULTS_DIR.exists():
        return []
        
    for d_dir in RESULTS_DIR.iterdir():
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

def export_summary_csv(analysis: Dict):
    """Export summary statistics as CSV."""
    output_file = EXPORT_DIR / "benchmark-summary.csv"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    rows = []
    for benchmark in SUITE_FILES:
        if benchmark not in analysis:
            continue
        
        for analysis_key, data in analysis[benchmark].items():
            row = {
                'Benchmark': benchmark,
                'Analysis': data['name'],
                'Examples': data.get('num_examples', 0),
                'Time_Min': data.get('time', {}).get('min', ''),
                'Time_Max': data.get('time', {}).get('max', ''),
                'Time_Mean': data.get('time', {}).get('mean', ''),
                'Time_Median': data.get('time', {}).get('median', ''),
                'Time_StDev': data.get('time', {}).get('stdev', ''),
                'NEval_Min': data.get('nevals', {}).get('min', ''),
                'NEval_Max': data.get('nevals', {}).get('max', ''),
                'NEval_Mean': data.get('nevals', {}).get('mean', ''),
                'NApply_Min': data.get('napplies', {}).get('min', ''),
                'NApply_Max': data.get('napplies', {}).get('max', ''),
                'NApply_Mean': data.get('napplies', {}).get('mean', ''),
                'Precision': data.get('precision', {}).get('mean', '')
            }
            rows.append(row)
    
    if rows:
        fieldnames = list(rows[0].keys())
        with open(output_file, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)
        
        print(f"Summary CSV exported to {output_file}")

def export_per_analysis_csv(analysis: Dict):
    """Export separate CSV for each analysis type."""
    analysis_types = set()
    for benchmark_data in analysis.values():
        analysis_types.update(benchmark_data.keys())
    
    for analysis_type in analysis_types:
        output_file = EXPORT_DIR / f"benchmark-summary-{analysis_type}.csv"
        output_file.parent.mkdir(parents=True, exist_ok=True)
        
        rows = []
        for benchmark in SUITE_FILES:
            if benchmark not in analysis or analysis_type not in analysis[benchmark]:
                continue
            
            data = analysis[benchmark][analysis_type]
            row = {
                'Benchmark': benchmark,
                'Examples': data.get('num_examples', 0),
                'Avg_Time_s': f"{data.get('time', {}).get('mean', 0):.6f}",
                'Max_Time_s': f"{data.get('time', {}).get('max', 0):.6f}",
                'Avg_NEval': f"{data.get('nevals', {}).get('mean', 0):.1f}",
                'Avg_NApply': f"{data.get('napplies', {}).get('mean', 0):.1f}",
                'Precision': f"{data.get('precision', {}).get('mean', 0):.3f}"
            }
            rows.append(row)
        
        if rows:
            fieldnames = list(rows[0].keys())
            with open(output_file, 'w', newline='') as f:
                writer = csv.DictWriter(f, fieldnames=fieldnames)
                writer.writeheader()
                writer.writerows(rows)
            
            print(f"Analysis CSV exported to {output_file}")

def generate_performance_report(analysis: Dict):
    """Generate a human-readable performance report."""
    output_file = EXPORT_DIR / "PERFORMANCE_REPORT.md"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_file, 'w') as f:
        f.write("# Benchmark Suite Performance Report\n\n")
        
        # Executive Summary
        f.write("## Executive Summary\n\n")
        total_examples = sum(
            data.get('num_examples', 0)
            for benchmark in analysis.values()
            for data in benchmark.values()
        )
        f.write(f"Total examples analyzed: {total_examples}\n")
        f.write(f"Total benchmarks: {len(SUITE_FILES)}\n")
        f.write(f"Analysis types: 3 (DMCFA, DMCFA-Exp, KCFA)\n\n")
        
        # Benchmark Details
        f.write("## Benchmark Details\n\n")
        for benchmark in SUITE_FILES:
            if benchmark not in analysis:
                f.write(f"### {benchmark}\n*No data available*\n\n")
                continue
            
            f.write(f"### {benchmark.replace('-', ' ').title()}\n\n")
            
            for analysis_key, data in analysis[benchmark].items():
                f.write(f"**{data['name']}**\n\n")
                f.write(f"- Examples: {data.get('num_examples', 0)}\n")
                
                if data.get('time'):
                    t = data['time']
                    f.write(f"- Execution Time:\n")
                    f.write(f"  - Average: {t.get('mean', 0):.4f}s\n")
                    f.write(f"  - Median: {t.get('median', 0):.4f}s\n")
                    f.write(f"  - Range: {t.get('min', 0):.4f}s - {t.get('max', 0):.4f}s\n")
                
                if data.get('nevals'):
                    n = data['nevals']
                    f.write(f"- Evaluations (NEval):\n")
                    f.write(f"  - Average: {n.get('mean', 0):.1f}\n")
                    f.write(f"  - Range: {n.get('min', 0):.0f} - {n.get('max', 0):.0f}\n")
                
                if data.get('napplies'):
                    na = data['napplies']
                    f.write(f"- Applications (NApply):\n")
                    f.write(f"  - Average: {na.get('mean', 0):.1f}\n")
                    f.write(f"  - Range: {na.get('min', 0):.0f} - {na.get('max', 0):.0f}\n")
                
                if data.get('precision'):
                    p = data['precision']
                    f.write(f"- Precision: {p.get('mean', 0):.1%}\n")
                
                f.write("\n")
        
        # Performance Analysis
        f.write("## Performance Analysis\n\n")
        
        # Fastest benchmarks
        f.write("### Fastest Benchmarks (Average Time)\n\n")
        fastest = []
        for benchmark, analyses in analysis.items():
            dmcfa_data = analyses.get('dmcfa', {})
            if dmcfa_data and dmcfa_data.get('time'):
                fastest.append((benchmark, dmcfa_data['time'].get('mean', float('inf'))))
        
        for bench, time in sorted(fastest, key=lambda x: x[1])[:3]:
            f.write(f"- **{bench}**: {time:.4f}s\n")
        f.write("\n")
        
        # Slowest benchmarks
        f.write("### Slowest Benchmarks (Average Time)\n\n")
        for bench, time in sorted(fastest, key=lambda x: x[1], reverse=True)[:3]:
            f.write(f"- **{bench}**: {time:.4f}s\n")
        f.write("\n")
        
        # Precision notes
        f.write("## Precision Analysis\n\n")
        f.write("Perfect precision (100%) indicates the analysis produces exact results.\n")
        f.write("Lower precision indicates some losses or approximations in the analysis.\n\n")
        
        f.write("Benchmarks with less than 100% precision:\n\n")
        for benchmark, analyses in sorted(analysis.items()):
            dmcfa = analyses.get('dmcfa', {})
            if dmcfa and dmcfa.get('precision'):
                prec = dmcfa['precision'].get('mean', 1.0)
                if prec < 1.0:
                    f.write(f"- **{benchmark}**: {prec:.1%} ({dmcfa.get('num_examples', 0)} examples)\n")
    
    print(f"Performance report exported to {output_file}")

def generate_comparison_html(analysis: Dict):
    """Generate an HTML comparison report."""
    output_file = EXPORT_DIR / "benchmark-comparison.html"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    html_content = """<!DOCTYPE html>
<html>
<head>
    <title>Benchmark Suite Comparison</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; background-color: #f5f5f5; }
        h1, h2 { color: #333; }
        table { border-collapse: collapse; width: 100%; margin: 20px 0; background-color: white; }
        th, td { padding: 12px; text-align: left; border-bottom: 1px solid #ddd; }
        th { background-color: #4CAF50; color: white; }
        tr:hover { background-color: #f5f5f5; }
        .fast { color: #2ecc71; font-weight: bold; }
        .slow { color: #e74c3c; font-weight: bold; }
        .perfect { color: #27ae60; }
        .imperfect { color: #e67e22; }
        .section { background-color: white; padding: 20px; margin: 20px 0; border-radius: 5px; }
    </style>
</head>
<body>
    <h1>Benchmark Suite Comparison Report</h1>
"""
    
    # Summary table
    html_content += "<div class='section'>\n<h2>Summary Statistics</h2>\n"
    html_content += """
    <table>
        <tr>
            <th>Benchmark</th>
            <th>Examples</th>
            <th>Avg Time (s)</th>
            <th>Precision</th>
            <th>Avg NEval</th>
            <th>Avg NApply</th>
        </tr>
"""
    
    for benchmark in SUITE_FILES:
        if benchmark not in analysis:
            continue
        
        dmcfa = analysis[benchmark].get('dmcfa', {})
        avg_time = dmcfa.get('time', {}).get('mean', 0)
        precision = dmcfa.get('precision', {}).get('mean', 0)
        
        time_class = 'fast' if avg_time < 0.01 else 'slow' if avg_time > 0.05 else ''
        prec_class = 'perfect' if precision >= 0.99 else 'imperfect' if precision < 0.9 else ''
        
        html_content += f"""    <tr>
        <td><strong>{benchmark}</strong></td>
        <td>{dmcfa.get('num_examples', 0)}</td>
        <td class="{time_class}">{avg_time:.4f}</td>
        <td class="{prec_class}">{precision:.1%}</td>
        <td>{dmcfa.get('nevals', {}).get('mean', 0):.1f}</td>
        <td>{dmcfa.get('napplies', {}).get('mean', 0):.1f}</td>
    </tr>
"""
    
    html_content += """    </table>
</div>
</body>
</html>
"""
    
    with open(output_file, 'w') as f:
        f.write(html_content)
    
    print(f"HTML report exported to {output_file}")

def main():
    """Main entry point."""
    print("Generating benchmark reports...\n")
    
    analysis = load_json_analysis()
    if not analysis:
        print("Error: Could not load analysis data")
        return
    
    # Export various formats
    export_summary_csv(analysis)
    export_per_analysis_csv(analysis)
    generate_performance_report(analysis)
    generate_comparison_html(analysis)
    
    print(f"\nAll reports exported to {EXPORT_DIR}")

if __name__ == "__main__":
    main()
