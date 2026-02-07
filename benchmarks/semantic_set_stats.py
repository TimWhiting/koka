import json
import os
import numpy as np

# List of problematic and reasonable benchmarks (DMCFAR h=2,m=2)
benchmarks = [
    ('koka-gen/build/mymakefile-example4', 'problematic'),
    ('koka-gen/build/mymakefile-example1', 'problematic'),
    ('koka-gen/mini-ppl/burglar', 'reasonable'),
    ('koka-gen/music/search-love', 'reasonable'),
    ('koka-gen/interp/interp', 'reasonable'),
]

results_dir = 'benchmarks/old-results/dmcfar/2/2/analysis/benchmarks/'

stats = []

for name, category in benchmarks:
    path = os.path.join(results_dir, f'{name}.json')
    if not os.path.exists(path):
        stats.append({'name': name, 'category': category, 'error': 'NOT_FOUND'})
        continue

    with open(path) as f:
        data = json.load(f)
    sm = data['storeMetrics']
    def get_sizes(map_metric):
        sizes = []
        if map_metric in sm:
            for v in sm[map_metric].values():
                sizes.extend(v)
        return sizes

    valSem_sizes = get_sizes('exprToValSemSizes')
    valStr_sizes = get_sizes('exprToValStrSizes')
    contSem_sizes = get_sizes('structToContSemSizes')
    strRet_sizes = get_sizes('structToStrRetSizes')

    stats.append({
        'name': name,
        'category': category,
        'numStoreAddresses': sm['numStoreAddresses'],
        'numTotalFixInputStates': sm['numTotalFixInputStates'],
        'valSemSingletons': sm.get('valSemSingletons', 0),
        'valSemMax': max(valSem_sizes) if valSem_sizes else 0,
        'valSemAvg': float(np.mean(valSem_sizes)) if valSem_sizes else 0,
        'valStrSingletons': sm.get('valStrSingletons', 0),
        'valStrMax': max(valStr_sizes) if valStr_sizes else 0,
        'valStrAvg': float(np.mean(valStr_sizes)) if valStr_sizes else 0,
        'contSemSingletons': sm.get('contSemSingletons', 0),
        'contSemMax': max(contSem_sizes) if contSem_sizes else 0,
        'contSemAvg': float(np.mean(contSem_sizes)) if contSem_sizes else 0,
        'strRetMax': max(strRet_sizes) if strRet_sizes else 0,
        'strRetAvg': float(np.mean(strRet_sizes)) if strRet_sizes else 0,
    })

print(f"{'Benchmark':<35} {'Category':<12} {'States':<8} {'StoreAddrs':<10} {'Avg':<6} {'Min':<6} {'Max':<6}")
print(f"{'Benchmark':<35} {'Category':<12} {'States':<8} {'StoreAddrs':<10} {'ValSem':<7} {'ContSem':<7} {'ValStr':<7} {'ContStr':<7}")
print(f"{'Benchmark':<35} {'Category':<12} {'States':<8} {'StoreAddrs':<10} {'ValSemMax':<10} {'ValSemAvg':<10} {'ValStrMax':<10} {'ValStrAvg':<10} {'ContSemMax':<10} {'ContSemAvg':<10} {'StrRetMax':<10} {'StrRetAvg':<10}")
for s in stats:
    if 'error' in s:
        print(f"{s['name']:<35} {s['category']:<12} {'ERROR':<8} {'ERROR':<10} {'-':<10} {'-':<10} {'-':<10} {'-':<10} {'-':<10} {'-':<10} {'-':<10} {'-':<10}")
    else:
        print(f"{s['name']:<35} {s['category']:<12} {s['numTotalFixInputStates']:<8} {s['numStoreAddresses']:<10} {s['valSemMax']:<10} {s['valSemAvg']:<10.2f} {s['valStrMax']:<10} {s['valStrAvg']:<10.2f} {s['contSemMax']:<10} {s['contSemAvg']:<10.2f} {s['strRetMax']:<10} {s['strRetAvg']:<10.2f}")
