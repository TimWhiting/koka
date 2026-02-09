#!/usr/bin/env python3
"""
Compare state space explosion for the largest benchmarks
"""
import json
from pathlib import Path

base_path = Path('benchmarks/results')
json_files = list(base_path.rglob('0/100/**/*.json')) + list(base_path.rglob('100/100/**/*.json'))

benchmark_configs = []
for json_file in json_files:
    try:
        with open(json_file, 'r') as f:
            data = json.load(f)
            if data and not data.get('isTimeout', False) and 'storeMetrics' in data:
                metrics = data.get('storeMetrics')
                if metrics and 'preciseResult' in metrics:
                    if not metrics['preciseResult']:
                        print(f"Warning: Benchmark {data.get('benchmarkName', '')} has preciseResult=False.")
                    else:
                        print(f"{json_file}")

    except:
        pass
