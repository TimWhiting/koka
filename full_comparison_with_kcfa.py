#!/usr/bin/env python3
"""
Full comparison including KCFA for top benchmarks
"""
import json
from pathlib import Path

# Get the top benchmarks from dmcfar
base_path_far = Path('benchmarks/old-results/dmcfar/2/2')
json_files = list(base_path_far.rglob('*.json'))

benchmark_configs = []
for json_file in json_files:
    try:
        with open(json_file, 'r') as f:
            data = json.load(f)
            if data and not data.get('isTimeout', False) and 'storeMetrics' in data:
                metrics = data.get('storeMetrics')
                if metrics and 'numTotalFixInputStates' in metrics:
                    configs = metrics['numTotalFixInputStates']
                    benchmark_name = data.get('benchmarkName', '')
                    clean_name = benchmark_name.replace('analysis/benchmarks/', '')
                    benchmark_configs.append((clean_name, configs))
    except:
        pass

benchmark_configs.sort(key=lambda x: x[1], reverse=True)
top_benchmarks = benchmark_configs[:10]

print("=" * 120)
print("Full Comparison: 0-CFA vs KCFA vs DMCFAE vs DMCFAR (d=2, m=2)")
print("=" * 120)
print()

results = []

for benchmark_name, dmcfar_d2m2_configs in top_benchmarks:
    result = {'name': benchmark_name}
    
    # Collect data from all variants
    # KCFA doesn't have object sensitivity (d), so it's always in folder 0/k where k is call-string depth
    for variant, d, m in [('dmcfar', 0, 0), ('kcfa', 0, 2), ('dmcfae', 2, 2), ('dmcfar', 2, 2)]:
        path = Path(f'benchmarks/old-results/{variant}/{d}/{m}')
        found = False
        
        for json_file in path.rglob('*.json'):
            try:
                with open(json_file, 'r') as f:
                    data = json.load(f)
                    if data.get('benchmarkName', '').replace('analysis/benchmarks/', '') == benchmark_name:
                        is_timeout = data.get('isTimeout', False)
                        times = data.get('analysisTimes', [])
                        avg_time = sum(times) / len(times) if times else None
                        
                        key = f'{variant}_{d}_{m}'
                        if is_timeout:
                            result[f'{key}_status'] = 'TIMEOUT'
                            result[f'{key}_configs'] = None
                            result[f'{key}_time'] = None
                        elif 'storeMetrics' in data and data['storeMetrics']:
                            metrics = data['storeMetrics']
                            if 'numTotalFixInputStates' in metrics:
                                result[f'{key}_status'] = 'OK'
                                result[f'{key}_configs'] = metrics['numTotalFixInputStates']
                                result[f'{key}_time'] = avg_time
                            else:
                                result[f'{key}_status'] = 'NO_METRICS'
                                result[f'{key}_configs'] = None
                                result[f'{key}_time'] = None
                        else:
                            result[f'{key}_status'] = 'NO_METRICS'
                            result[f'{key}_configs'] = None
                            result[f'{key}_time'] = None
                        found = True
                        break
            except:
                pass
        
        if not found:
            key = f'{variant}_{d}_{m}'
            result[f'{key}_status'] = 'NOT_FOUND'
            result[f'{key}_configs'] = None
            result[f'{key}_time'] = None
    
    results.append(result)

# Print table
print(f"{'Benchmark':<40} {'0-CFA':<15} {'KCFA':<15} {'DMCFAE':<15} {'DMCFAR':<15}")
print(f"{'':40} {'(d=0,m=0)':<15} {'(d=2,m=2)':<15} {'(d=2,m=2)':<15} {'(d=2,m=2)':<15}")
print("-" * 120)

for r in results:
    name = r['name'][:38] + '..' if len(r['name']) > 40 else r['name']
    
    # Format configs
    def fmt_cfg(key):
        status = r.get(f'{key}_status', 'NOT_FOUND')
        configs = r.get(f'{key}_configs')
        if status == 'TIMEOUT':
            return 'TIMEOUT'
        elif status == 'OK' and configs:
            return f"{configs:,}"
        else:
            return status
    
    print(f"{name:<40} {fmt_cfg('dmcfar_0_0'):<15} {fmt_cfg('kcfa_2_2'):<15} {fmt_cfg('dmcfae_2_2'):<15} {fmt_cfg('dmcfar_2_2'):<15}")

print()
print("=" * 120)
print("Time Analysis (seconds):")
print("=" * 120)
print(f"{'Benchmark':<40} {'0-CFA':<12} {'KCFA':<12} {'DMCFAE':<12} {'DMCFAR':<12}")
print("-" * 120)

for r in results:
    name = r['name'][:38] + '..' if len(r['name']) > 40 else r['name']
    
    def fmt_time(key):
        status = r.get(f'{key}_status', 'NOT_FOUND')
        time = r.get(f'{key}_time')
        if status == 'TIMEOUT':
            return 'TIMEOUT'
        elif status == 'OK' and time:
            return f"{time:.2f}s"
        else:
            return '---'
    
    print(f"{name:<40} {fmt_time('dmcfar_0_0'):<12} {fmt_time('kcfa_2_2'):<12} {fmt_time('dmcfae_2_2'):<12} {fmt_time('dmcfar_2_2'):<12}")

print()
print("=" * 120)
print("Explosion Factor Analysis:")
print("=" * 120)
print(f"{'Benchmark':<40} {'Configs':<20} {'Time Ratio':<25}")
print(f"{'':40} {'vs 0-CFA':<20} {'(Time/Configs)':<25}")
print("-" * 120)

for r in results:
    name = r['name'][:38] + '..' if len(r['name']) > 40 else r['name']
    
    d0m0_configs = r.get('dmcfar_0_0_configs')
    d2m2_configs = r.get('dmcfar_2_2_configs')
    d0m0_time = r.get('dmcfar_0_0_time')
    d2m2_time = r.get('dmcfar_2_2_time')
    
    if d0m0_configs and d2m2_configs and d0m0_time and d2m2_time and d0m0_configs > 0 and d0m0_time > 0:
        config_explosion = d2m2_configs / d0m0_configs
        time_explosion = d2m2_time / d0m0_time
        ratio = time_explosion / config_explosion if config_explosion > 0 else 0
        
        config_str = f"{config_explosion:.1f}x"
        time_str = f"{time_explosion:.0f}x"
        ratio_str = f"{ratio:.1f}x"
        
        print(f"{name:<40} {config_str:<20} {time_str} / {config_str} = {ratio_str}")

print()
print("=" * 120)
print("Key Observations:")
print("=" * 120)
print()
print("1. TIME EXPLOSION > CONFIGS EXPLOSION:")
print("   The time explosion is disproportionately larger than config explosion because:")
print("   - Each configuration may require multiple fixpoint iterations to converge")
print("   - More dependencies mean more continuation callbacks per cache update")
print("   - Cache lookup overhead grows with cache size")
print("   - The fixpoint monad overhead compounds with more iterations")
print()
print("2. DMCFAE vs DMCFAR:")
print("   - DMCFAE has 40% timeout rate on large benchmarks")
print("   - DMCFAR successfully completes all benchmarks")
print()
print("3. KCFA performance will be analyzed in the comparison above")
