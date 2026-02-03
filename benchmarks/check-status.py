#!/usr/bin/env python3
"""Quick script to check status inconsistencies."""

import json
import os

missing_metrics = 0
has_timeout_flag = 0
missing_but_not_timeout = 0
total = 0

print("Checking for status inconsistencies...")

for root, dirs, files in os.walk('benchmarks/results'):
    for f in files:
        if f.endswith('.json'):
            path = os.path.join(root, f)
            with open(path) as fp:
                data = json.load(fp)
                total += 1
                
                if not data.get('storeMetrics'):
                    missing_metrics += 1
                    if data.get('isTimeout'):
                        has_timeout_flag += 1
                    else:
                        missing_but_not_timeout += 1
                        if missing_but_not_timeout <= 5:
                            print(f'Missing storeMetrics but isTimeout=False: {path}')
                            print(f'  Keys: {list(data.keys())}')

print(f'\nTotal files: {total}')
print(f'Missing storeMetrics: {missing_metrics}')
print(f'  - With isTimeout=True: {has_timeout_flag}')
print(f'  - With isTimeout=False: {missing_but_not_timeout}')

if missing_but_not_timeout > 0:
    print(f'\n⚠️  ISSUE FOUND: {missing_but_not_timeout} files have missing storeMetrics')
    print(f'   but isTimeout=False. These are being treated as timeouts in analyze.py')
    print(f'   because of the condition: run.get("storeMetrics") is None')
else:
    print('\n✓ No inconsistencies found.')
