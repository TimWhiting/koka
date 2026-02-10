#!/usr/bin/env python3
"""
Compare state space explosion for the largest benchmarks
"""
import json
from pathlib import Path

# Get the top benchmarks from d=0,m=0
base_path = Path('benchmarks/results/dmcfar/0/0')
json_files = list(base_path.rglob('*.json'))
benchmark_configs = []
for json_file in json_files:
    try:
        with open(json_file, 'r') as f:
            data = json.load(f)
            if data and not data.get('isTimeout', False) and 'storeMetrics' in data:
                metrics = data.get('storeMetrics')
                if metrics and 'numTotalFixpointStates' in metrics:
                    configs = metrics['numTotalFixpointStates']
                    benchmark_name = data.get('benchmarkName', '')
                    # Clean up the name
                    clean_name = benchmark_name.replace('analysis/benchmarks/', '')
                    benchmark_configs.append((clean_name, configs))
    except:
        pass

# Sort by config count and get top 10
benchmark_configs.sort(key=lambda x: x[1], reverse=True)
top_benchmarks = benchmark_configs[:10]

print("=" * 100)
print("State Space Explosion Analysis: Top 10 Largest Benchmarks")
print("=" * 100)
print()

results = []

for benchmark_name, d0m0_configs in top_benchmarks:
    # Try to find the 0-CFA version
    benchmark_path = benchmark_name.replace('/', '/')  # Already clean
    
    # Find the JSON file in 0/0
    d0m0_path = None
    d2m2_path = None
    
    for json_file in Path('benchmarks/results/dmcfar/0/0').rglob('*.json'):
        with open(json_file, 'r') as f:
            data = json.load(f)
            if data.get('benchmarkName', '').replace('analysis/benchmarks/', '') == benchmark_name:
                d0m0_path = json_file
                break
    
    for json_file in Path('benchmarks/results/dmcfar/2/2').rglob('*.json'):
        with open(json_file, 'r') as f:
            data = json.load(f)
            if data.get('benchmarkName', '').replace('analysis/benchmarks/', '') == benchmark_name:
                d2m2_path = json_file
                break
    
    d2m2_configs = None
    d0m0_time = None
    d2m2_time = None
    
    if d0m0_path and d0m0_path.exists():
        with open(d0m0_path, 'r') as f:
            data = json.load(f)
            if not data.get('isTimeout', False) and 'storeMetrics' in data:
                metrics = data.get('storeMetrics')
                if metrics and 'numTotalFixpointStates' in metrics:
                    times = data.get('analysisTimes', [])
                    if times:
                        d0m0_time = sum(times) / len(times)
    
    if d2m2_path and d2m2_path.exists():
        with open(d2m2_path, 'r') as f:
            data = json.load(f)
            if not data.get('isTimeout', False):   
                metrics = data.get('storeMetrics')    
                if metrics and 'numTotalFixpointStates' in metrics:
                    d2m2_configs = metrics['numTotalFixpointStates']
                times = data.get('analysisTimes', [])
                if times:
                    d2m2_time = sum(times) / len(times)
    
    results.append({
        'name': benchmark_name,
        'd0m0_configs': d0m0_configs,
        'd2m2_configs': d2m2_configs,
        'd0m0_time': d0m0_time,
        'd2m2_time': d2m2_time
    })

# Print results table
print(f"{'Benchmark':<50} {'0-CFA':<12} {'d=2,m=2':<12} {'Explosion':<12} {'Time 0-CFA':<12} {'Time d=2,m=2':<12}")
print("-" * 100)

for r in results:
    name_short = r['name'][:48] + '..' if len(r['name']) > 50 else r['name']
    
    if r['d0m0_configs']:
        d0m0_str = f"{r['d0m0_configs']:,}"
        d2m2_str = f"{r['d2m2_configs']:,}"
        explosion = r['d2m2_configs'] / r['d0m0_configs']
        explosion_str = f"{explosion:.1f}x"
    else:
        d0m0_str = "N/A"
        d2m2_str = f"{r['d2m2_configs']:,}"
        explosion_str = "N/A"
    
    time_d0m0_str = f"{r['d0m0_time']:.2f}s" if r['d0m0_time'] else "N/A"
    time_d2m2_str = f"{r['d2m2_time']:.2f}s" if r['d2m2_time'] else "N/A"
    
    print(f"{name_short:<50} {d0m0_str:<12} {d2m2_str:<12} {explosion_str:<12} {time_d0m0_str:<12} {time_d2m2_str:<12}")

print()
print("=" * 100)
print("Summary Statistics:")
print("=" * 100)

valid_explosions = [r['d2m2_configs'] / r['d0m0_configs'] for r in results if r['d0m0_configs']]
if valid_explosions:
    avg_explosion = sum(valid_explosions) / len(valid_explosions)
    max_explosion = max(valid_explosions)
    min_explosion = min(valid_explosions)
    
    print(f"Among top 10 largest benchmarks:")
    print(f"  Average explosion factor: {avg_explosion:.1f}x")
    print(f"  Min explosion factor: {min_explosion:.1f}x")
    print(f"  Max explosion factor: {max_explosion:.1f}x")
    print()
    
    max_benchmark = results[valid_explosions.index(max_explosion)]
    print(f"  Largest explosion: {max_benchmark['name']}")
    print(f"    {max_benchmark['d0m0_configs']:,} → {max_benchmark['d2m2_configs']:,} ({max_explosion:.1f}x)")
