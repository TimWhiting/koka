#!/usr/bin/env python3
import json
from pathlib import Path

# Find all JSON files in dmcfae/0/0
base_path = Path('benchmarks/old-results/dmcfar/0/0')
json_files = list(base_path.rglob('*.json'))

total_configs = 0
files_with_data = 0
max_configs = 0
max_file = None
benchmark_details = []

for json_file in json_files:
    try:
        with open(json_file, 'r') as f:
            data = json.load(f)
            if data and 'storeMetrics' in data:
                metrics = data.get('storeMetrics')
                if metrics and 'numTotalFixInputStates' in metrics:
                    configs = metrics['numTotalFixInputStates'] - metrics['numStoreAddresses']
                    total_configs += configs
                    files_with_data += 1
                    benchmark_name = data.get('benchmarkName', json_file.name)
                    benchmark_details.append((benchmark_name, configs))
                    if configs > max_configs:
                        max_configs = configs
                        max_file = benchmark_name
    except Exception as e:
        print(f'Error reading {json_file.name}: {e}')

print(f'Total JSON files found: {len(json_files)}')
print(f'Files with configuration data: {files_with_data}')
print(f'Total configurations: {total_configs:,}')
print(f'Average per benchmark: {total_configs / files_with_data if files_with_data > 0 else 0:,.1f}')
print(f'Max configurations: {max_configs:,} in {max_file}')
print()

# Show top 10 benchmarks by config count
print("Top 10 benchmarks by configuration count:")
benchmark_details.sort(key=lambda x: x[1], reverse=True)
for i, (name, count) in enumerate(benchmark_details[:10], 1):
    print(f"{i}. {name}: {count:,}")
