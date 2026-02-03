#!/usr/bin/env python3
"""Check timeout status for recently run benchmarks."""

import json
import os

# Check various configurations that were previously timing out
test_cases = [
    ('dmcfa', '0', '0', 'example2'),
    ('dmcfa', '0', '0', 'example4'),
    ('dmcfa', '100', '100', 'example2'),
    ('dmcfae', '0', '0', 'example2'),
    ('dmcfae', '0', '0', 'example4'),
]

print('='*80)
print('SCOPED HANDLER EXAMPLES - TIMEOUT STATUS')
print('='*80)
print()

for variant, d, m, example in test_cases:
    path = f'benchmarks/results/{variant}/{d}/{m}/analysis/benchmarks/handlers/scoped/{example}.json'
    if os.path.exists(path):
        with open(path) as f:
            data = json.load(f)
        status = '✅ SUCCESS' if not data.get('isTimeout') else '❌ TIMEOUT'
        print(f'{status} | {variant} ({d},{m}) | {example}')
        if not data.get('isTimeout'):
            times = data.get('analysisTimes', [])
            if times:
                avg = sum(times)/len(times)
                print(f'         Times: {[f"{t:.3f}" for t in times]} (avg: {avg:.3f}s)')
        else:
            print(f'         storeMetrics: {"present" if data.get("storeMetrics") else "null"}')
    else:
        print(f'⚠️  NOT RUN | {variant} ({d},{m}) | {example}')
    print()
