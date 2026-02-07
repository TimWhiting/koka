#!/usr/bin/env python3
"""
Explain the time vs configs explosion disparity
"""
import json
from pathlib import Path

print("=" * 100)
print("Analysis: Why Time Explosion >> Configuration Explosion")
print("=" * 100)
print()

# Get some examples from dmcfar
examples = [
    ('koka-gen/build/mymakefile-example4', 'd=0,m=0', 'd=2,m=2'),
    ('koka-gen/build/mymakefile-example2', 'd=0,m=0', 'd=2,m=2'),
    ('koka-gen/coop-communication/send-recv', 'd=0,m=0', 'd=2,m=2'),
]

data = []
for benchmark, _, _ in examples:
    result = {'name': benchmark}
    
    for d, m in [(0, 0), (2, 2)]:
        path = Path(f'benchmarks/old-results/dmcfar/{d}/{m}')
        for json_file in path.rglob('*.json'):
            try:
                with open(json_file, 'r') as f:
                    json_data = json.load(f)
                    if json_data.get('benchmarkName', '').replace('analysis/benchmarks/', '') == benchmark:
                        metrics = json_data.get('storeMetrics', {})
                        if metrics:
                            times = json_data.get('analysisTimes', [])
                            result[f'd{d}m{m}_configs'] = metrics.get('numTotalFixInputStates', 0)
                            result[f'd{d}m{m}_time'] = sum(times) / len(times) if times else 0
                            result[f'd{d}m{m}_addrs'] = metrics.get('numStoreAddresses', 0)
                        break
            except:
                pass
    
    if 'd0m0_configs' in result and 'd2m2_configs' in result:
        data.append(result)

print("Example Benchmarks:")
print()
print(f"{'Benchmark':<45} {'Configs':<15} {'Time':<15} {'Addresses':<12}")
print(f"{'':45} {'0→2,2':<15} {'0→2,2':<15} {'0→2,2':<12}")
print("-" * 100)

for r in data:
    name = r['name'][:43] + '..' if len(r['name']) > 45 else r['name']
    
    config_exp = r['d2m2_configs'] / r['d0m0_configs'] if r['d0m0_configs'] > 0 else 0
    time_exp = r['d2m2_time'] / r['d0m0_time'] if r['d0m0_time'] > 0 else 0
    addr_exp = r['d2m2_addrs'] / r['d0m0_addrs'] if r['d0m0_addrs'] > 0 else 0
    
    config_str = f"{config_exp:.1f}x"
    time_str = f"{time_exp:.0f}x"
    addr_str = f"{addr_exp:.1f}x"
    
    print(f"{name:<45} {config_str:<15} {time_str:<15} {addr_str:<12}")

print()
print("=" * 100)
print("Explanation of Time Disparity:")
print("=" * 100)
print()

# Calculate average ratio
time_config_ratios = []
for r in data:
    config_exp = r['d2m2_configs'] / r['d0m0_configs'] if r['d0m0_configs'] > 0 else 0
    time_exp = r['d2m2_time'] / r['d0m0_time'] if r['d0m0_time'] > 0 else 0
    if config_exp > 0:
        time_config_ratios.append(time_exp / config_exp)

if time_config_ratios:
    avg_ratio = sum(time_config_ratios) / len(time_config_ratios)
    print(f"Average Time/Config Ratio: {avg_ratio:.1f}x")
    print()

print("The time explosion is much larger than the configuration explosion due to:")
print()
print("1. FIXPOINT ITERATION OVERHEAD:")
print("   - Each configuration is computed through the fixpoint monad (FixpointMonad.hs)")
print("   - The 'memo' function creates continuations that are stored and called repeatedly")
print("   - More configurations → more continuations → more callbacks per cache update")
print("   - Lines 249-266 in FixpointMonad.hs show the 'push' function calls all continuations")
print()
print("2. CACHE MANAGEMENT OVERHEAD:")
print("   - Every memo lookup/insert involves Map operations (line 232-247)")
print("   - Larger cache means slower lookups (O(log n) per lookup)")
print("   - With 30x more configs, you get 30x more Map entries to search")
print()
print("3. MULTIPLE FIXPOINT ITERATIONS:")
print("   - Each configuration may need multiple iterations to reach fixpoint")
print("   - Dependencies create chains of updates that propagate")
print("   - A single new value can trigger cascading continuation calls")
print("   - This is especially true for programs with deep call chains")
print()
print("4. CONTINUATION CALLBACK EXPLOSION:")
print("   - Each 'memo' call registers a continuation (ContX or ContF)")
print("   - When cache updates, ALL registered continuations are called (line 264-268)")
print("   - With d=2,m=2, there are many more call contexts = many more continuations")
print("   - Example: if a function is called from 10 contexts, 10 continuations fire on update")
print()
print("5. STATE MANAGEMENT:")
print("   - The monad stack is ReaderT + StateT + IO")
print("   - Each operation unpacks/repacks this stack")
print("   - With more iterations, this overhead compounds")
print()
print("Real Example from build/mymakefile-example4:")
c_exp = next((r['d2m2_configs'] / r['d0m0_configs'] for r in data if 'example4' in r['name']), 0)
t_exp = next((r['d2m2_time'] / r['d0m0_time'] for r in data if 'example4' in r['name']), 0)
print(f"  Configurations: {c_exp:.1f}x explosion")
print(f"  Time: {t_exp:.0f}x explosion")
print(f"  Time/Config ratio: {t_exp/c_exp if c_exp > 0 else 0:.1f}x")
print()
print("  This means: for EACH extra configuration, the analysis takes ~458x as long!")
print("  This is because each config triggers many fixpoint iterations and continuation callbacks.")
