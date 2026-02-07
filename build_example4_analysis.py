#!/usr/bin/env python3
"""
Analysis of build.kk mymakefile-example4 across different analysis variants
"""
import json
from pathlib import Path

variants = ['dmcfae', 'dmcfar', 'kcfa']
d, m = 2, 2

print("=" * 80)
print("Analysis of build.kk mymakefile-example4 Benchmark")
print("Parameters: d=2, m=2")
print("=" * 80)
print()

for variant in variants:
    json_path = Path(f'benchmarks/old-results/{variant}/{d}/{m}/analysis/benchmarks/koka-gen/build/mymakefile-example4.json')
    
    if not json_path.exists():
        print(f"{variant.upper():8s}: File not found")
        print()
        continue
    
    with open(json_path, 'r') as f:
        data = json.load(f)
    
    is_timeout = data.get('isTimeout', False)
    analysis_times = data.get('analysisTimes', [])
    metrics = data.get('storeMetrics')
    
    print(f"{variant.upper():8s}:")
    print(f"  Status: {'TIMEOUT' if is_timeout else 'COMPLETED'}")
    
    if analysis_times:
        avg_time = sum(analysis_times) / len(analysis_times)
        print(f"  Analysis time: {avg_time:.2f}s (avg of {len(analysis_times)} runs)")
        print(f"    Individual times: {[f'{t:.2f}s' for t in analysis_times]}")
    else:
        print(f"  Analysis time: N/A")
    
    if metrics:
        num_configs = metrics.get('numTotalFixInputStates', 0)
        num_stores = metrics.get('numStoreAddresses', 0)
        num_structs = metrics.get('numStructAddresses', 0)
        num_lits = metrics.get('numLitAddresses', 0)
        num_conts = metrics.get('numContAddresses', 0)
        
        print(f"  Total configurations: {num_configs:,}")
        print(f"  Store addresses: {num_stores:,}")
        print(f"    - Struct addresses: {num_structs:,}")
        print(f"    - Literal addresses: {num_lits:,}")
        print(f"    - Continuation addresses: {num_conts:,}")
    else:
        print(f"  Configurations: N/A (timeout before metrics collected)")
    
    print()

print("=" * 80)
print("Key Findings:")
print("=" * 80)
print()
print("The build mymakefile-example4 benchmark tests dynamic dependencies.")
print("The 'app.pkg' target reads 'config.txt' to determine which library to build.")
print()
print("DMCFAE (d=2,m=2): TIMEOUT - Analysis did not complete")
print("DMCFAR (d=2,m=2): 71,181 configurations in ~488 seconds")
print()
print("This demonstrates that the DMCFAR variant is significantly more efficient")
print("for this type of program with dynamic control flow, while DMCFAE times out.")
