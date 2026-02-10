#!/usr/bin/env python3
"""
Comprehensive analysis of dmcfae d=2, m=2 benchmark results
"""
import json
from pathlib import Path

# Find all JSON files in dmcfae/2/2
base_path = Path('benchmarks/old-results/dmcfar/0/0')
json_files = list(base_path.rglob('*.json'))

total_configs = 0
total_time = 0
files_with_data = 0
max_configs = 0
max_file = None
benchmark_details = []
timeout_count = 0

for json_file in json_files:
    try:
        with open(json_file, 'r') as f:
            data = json.load(f)
            if data:
                benchmark_name = data.get('benchmarkName', json_file.name)
                is_timeout = data.get('isTimeout', False)
                analysis_times = data.get('analysisTimes', [])
                
                if is_timeout:
                    timeout_count += 1
                
                if 'storeMetrics' in data:
                    metrics = data.get('storeMetrics')
                    if metrics and 'numTotalFixInputStates' in metrics:
                        configs = metrics['numTotalFixInputStates']
                        total_configs += configs
                        files_with_data += 1
                        
                        # Calculate average analysis time
                        avg_time = sum(analysis_times) / len(analysis_times) if analysis_times else 0
                        total_time += avg_time
                        
                        benchmark_details.append({
                            'name': benchmark_name,
                            'configs': configs,
                            'time': avg_time,
                            'timeout': is_timeout
                        })
                        
                        if configs > max_configs:
                            max_configs = configs
                            max_file = benchmark_name
    except Exception as e:
        print(f'Error reading {json_file.name}: {e}')

print("=" * 80)
print("DMCFA d=2, m=2 Configuration Analysis")
print("=" * 80)
print()
print(f"Total benchmark files: {len(json_files)}")
print(f"Files with configuration data: {files_with_data}")
print(f"Timeouts: {timeout_count}")
print()
print(f"TOTAL CONFIGURATIONS: {total_configs:,}")
print(f"Average per benchmark: {total_configs / files_with_data if files_with_data > 0 else 0:,.1f}")
print(f"Total analysis time: {total_time:.2f} seconds")
print(f"Average time per benchmark: {total_time / files_with_data if files_with_data > 0 else 0:.4f} seconds")
print()
print(f"Largest benchmark: {max_file}")
print(f"  Configurations: {max_configs:,}")
print(f"  Percentage of total: {max_configs / total_configs * 100:.1f}%")
print()

# Show top 15 benchmarks by config count
print("=" * 80)
print("Top 15 benchmarks by configuration count:")
print("=" * 80)
benchmark_details.sort(key=lambda x: x['configs'], reverse=True)
for i, item in enumerate(benchmark_details[:15], 1):
    timeout_mark = " [TIMEOUT]" if item['timeout'] else ""
    print(f"{i:2d}. {item['configs']:>9,} configs | {item['time']:>8.4f}s | {item['name']}{timeout_mark}")

print()
print("=" * 80)
print("Configuration Distribution:")
print("=" * 80)
bins = [0, 100, 500, 1000, 5000, 10000, 50000, float('inf')]
bin_labels = ['0-100', '101-500', '501-1K', '1K-5K', '5K-10K', '10K-50K', '50K+']
bin_counts = [0] * len(bin_labels)

for item in benchmark_details:
    configs = item['configs']
    for i, (low, high) in enumerate(zip(bins[:-1], bins[1:])):
        if low < configs <= high:
            bin_counts[i] += 1
            break

for label, count in zip(bin_labels, bin_counts):
    print(f"  {label:>10s}: {count:3d} benchmarks")

print()
print("=" * 80)
print(f"KEY INSIGHT: The single benchmark '{max_file}'")
print(f"accounts for {max_configs:,} configurations ({max_configs / total_configs * 100:.1f}% of total)")
print("=" * 80)
