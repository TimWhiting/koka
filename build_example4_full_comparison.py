#!/usr/bin/env python3
"""
Full comparison of build.kk mymakefile-example4 across all d/m combinations
"""
import json
from pathlib import Path

print("=" * 90)
print("State Space Explosion Analysis: build.kk mymakefile-example4")
print("=" * 90)
print()

# Results table
results = []

for d in [0, 1, 2]:
    for m in [0, 1, 2]:
        json_path = Path(f'benchmarks/old-results/dmcfar/{d}/{m}/analysis/benchmarks/koka-gen/build/mymakefile-example4.json')
        
        if not json_path.exists():
            results.append((d, m, None, None, None))
            continue
        
        with open(json_path, 'r') as f:
            data = json.load(f)
        
        is_timeout = data.get('isTimeout', False)
        analysis_times = data.get('analysisTimes', [])
        metrics = data.get('storeMetrics')
        
        if is_timeout or not metrics:
            results.append((d, m, None, None, True))
        else:
            num_configs = metrics.get('numTotalFixInputStates', 0)
            avg_time = sum(analysis_times) / len(analysis_times) if analysis_times else 0
            results.append((d, m, num_configs, avg_time, False))

# Print table
print(f"{'d':<3} {'m':<3} {'Configs':<15} {'Time (s)':<12} {'Status':<10}")
print("-" * 90)

baseline_configs = None
baseline_time = None

for d, m, configs, time, timeout in results:
    if configs is None:
        status = "TIMEOUT" if timeout else "N/A"
        config_str = "---"
        time_str = "---"
    else:
        status = "OK"
        config_str = f"{configs:,}"
        time_str = f"{time:.2f}"
        
        # Set baseline as d=0, m=0
        if d == 0 and m == 0:
            baseline_configs = configs
            baseline_time = time
    
    print(f"{d:<3} {m:<3} {config_str:<15} {time_str:<12} {status:<10}")

print()
print("=" * 90)
print("State Space Growth Analysis:")
print("=" * 90)
print()

if baseline_configs:
    print(f"Baseline (d=0, m=0): {baseline_configs:,} configurations in {baseline_time:.2f}s")
    print()
    print(f"{'d':<3} {'m':<3} {'Configs':<15} {'Growth Factor':<20} {'Time Growth':<15}")
    print("-" * 90)
    
    for d, m, configs, time, timeout in results:
        if configs is not None and baseline_configs > 0:
            growth = configs / baseline_configs
            time_growth = time / baseline_time if baseline_time > 0 else 0
            config_str = f"{configs:,}"
            print(f"{d:<3} {m:<3} {config_str:<15} {growth:>6.1f}x{'':<13} {time_growth:>6.1f}x")

print()
print("=" * 90)
print("Key Observations:")
print("=" * 90)
print()

# Find the d=2,m=2 result
d2m2 = next((r for r in results if r[0] == 2 and r[1] == 2), None)
d0m0 = next((r for r in results if r[0] == 0 and r[1] == 0), None)

if d2m2 and d0m0 and d2m2[2] and d0m0[2]:
    explosion_factor = d2m2[2] / d0m0[2]
    time_factor = d2m2[3] / d0m0[3] if d0m0[3] > 0 else 0
    
    print(f"From 0-CFA (d=0,m=0) to 2-CFA with m=2 (d=2,m=2):")
    print(f"  Configuration explosion: {explosion_factor:.1f}x ({d0m0[2]:,} → {d2m2[2]:,})")
    print(f"  Time increase: {time_factor:.1f}x ({d0m0[3]:.2f}s → {d2m2[3]:.2f}s)")
    print()
    print(f"Note: DMCFAE with d=2,m=2 TIMED OUT on this benchmark.")
    print(f"      DMCFAR successfully completes with {d2m2[2]:,} configurations.")

print()
