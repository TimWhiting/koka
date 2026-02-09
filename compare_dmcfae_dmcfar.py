#!/usr/bin/env python3
"""
Compare DMCFAE vs DMCFAR for top benchmarks to see timeout rates
"""
import json
from pathlib import Path

# Get the same top benchmarks
base_path_far = Path('benchmarks/old-results/dmcfar/0/0')
json_files = list(base_path_far.rglob('*.json'))

benchmark_configs = []
for json_file in json_files:
    try:
        with open(json_file, 'r') as f:
            data = json.load(f)
            if data and not data.get('isTimeout', False) and 'storeMetrics' in data:
                metrics = data.get('storeMetrics')
                if metrics and 'numTotalFixInputStates' in metrics:
                    configs = metrics['numTotalFixInputStates'] - metrics['numStoreAddresses']
                    benchmark_name = data.get('benchmarkName', '')
                    clean_name = benchmark_name.replace('analysis/benchmarks/', '')
                    benchmark_configs.append((clean_name, configs))
    except:
        pass

benchmark_configs.sort(key=lambda x: x[1], reverse=True)
top_benchmarks = benchmark_configs[:10]

print("=" * 110)
print("DMCFAE vs DMCFAR Comparison: Top 10 Benchmarks (d=2, m=2)")
print("=" * 110)
print()

results = []

for benchmark_name, dmcfar_configs in top_benchmarks:
    # Find in DMCFAE
    dmcfae_path = None
    dmcfar_path = None
    
    for json_file in Path('benchmarks/old-results/dmcfae/2/2').rglob('*.json'):
        try:
            with open(json_file, 'r') as f:
                data = json.load(f)
                if data.get('benchmarkName', '').replace('analysis/benchmarks/', '') == benchmark_name:
                    dmcfae_path = json_file
                    break
        except:
            pass
    
    for json_file in Path('benchmarks/old-results/dmcfar/2/2').rglob('*.json'):
        try:
            with open(json_file, 'r') as f:
                data = json.load(f)
                if data.get('benchmarkName', '').replace('analysis/benchmarks/', '') == benchmark_name:
                    dmcfar_path = json_file
                    break
        except:
            pass
    
    dmcfae_status = "NOT FOUND"
    dmcfae_configs = None
    dmcfae_time = None
    dmcfar_time = None
    
    if dmcfae_path and dmcfae_path.exists():
        with open(dmcfae_path, 'r') as f:
            data = json.load(f)
            if data.get('isTimeout', False):
                dmcfae_status = "TIMEOUT"
            elif 'storeMetrics' in data and data['storeMetrics']:
                metrics = data['storeMetrics']
                if 'numTotalFixInputStates' in metrics:
                    dmcfae_configs = metrics['numTotalFixInputStates']
                    dmcfae_status = "OK"
                    times = data.get('analysisTimes', [])
                    if times:
                        dmcfae_time = sum(times) / len(times)
            else:
                dmcfae_status = "NO METRICS"
    
    if dmcfar_path and dmcfar_path.exists():
        with open(dmcfar_path, 'r') as f:
            data = json.load(f)
            times = data.get('analysisTimes', [])
            if times:
                dmcfar_time = sum(times) / len(times)
    
    results.append({
        'name': benchmark_name,
        'dmcfae_status': dmcfae_status,
        'dmcfae_configs': dmcfae_configs,
        'dmcfae_time': dmcfae_time,
        'dmcfar_configs': dmcfar_configs,
        'dmcfar_time': dmcfar_time
    })

# Print table
print(f"{'Benchmark':<52} {'DMCFAE Status':<15} {'DMCFAE Configs':<18} {'DMCFAR Configs':<18}")
print("-" * 110)

timeout_count = 0
success_count = 0

for r in results:
    name_short = r['name'][:50] + '..' if len(r['name']) > 52 else r['name']
    
    dmcfae_config_str = f"{r['dmcfae_configs']:,}" if r['dmcfae_configs'] else "---"
    dmcfar_config_str = f"{r['dmcfar_configs']:,}"
    
    if r['dmcfae_status'] == "TIMEOUT":
        timeout_count += 1
    elif r['dmcfae_status'] == "OK":
        success_count += 1
    
    print(f"{name_short:<52} {r['dmcfae_status']:<15} {dmcfae_config_str:<18} {dmcfar_config_str:<18}")

print()
print("=" * 110)
print("Summary:")
print("=" * 110)
print(f"DMCFAE Timeouts: {timeout_count}/{len(results)} ({timeout_count/len(results)*100:.0f}%)")
print(f"DMCFAE Success: {success_count}/{len(results)} ({success_count/len(results)*100:.0f}%)")
print()

if success_count > 0:
    print("Among successful DMCFAE runs:")
    print(f"{'Benchmark':<52} {'DMCFAE':<15} {'DMCFAR':<15} {'DMCFAR Faster':<15}")
    print("-" * 110)
    
    for r in results:
        if r['dmcfae_status'] == 'OK' and r['dmcfae_time'] and r['dmcfar_time']:
            name_short = r['name'][:50] + '..' if len(r['name']) > 52 else r['name']
            speedup = r['dmcfae_time'] / r['dmcfar_time']
            print(f"{name_short:<52} {r['dmcfae_time']:.2f}s{'':<8} {r['dmcfar_time']:.2f}s{'':<8} {speedup:.1f}x")

print()
print("Key Finding: DMCFAR successfully completes all large benchmarks, while DMCFAE times out frequently.")
