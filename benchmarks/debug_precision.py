
import json
import sys

def analyze(path, name):
    with open(path) as f:
        data = json.load(f)
    
    m = data.get('storeMetrics', {})
    
    cont_map = m.get('structToContSemSizes', {})
    if not cont_map:
        cont_map = m.get('structToContStrSizes', {})

    print(f"--- {name} ---")
    
    total_contexts = 0
    precise_contexts = 0
    imprecise_contexts = 0
    
    imprecise_keys = {}
    
    for k, sizes in cont_map.items():
        for s in sizes:
            total_contexts += 1
            if s <= 1:
                precise_contexts += 1
            else:
                imprecise_contexts += 1
                if k not in imprecise_keys: imprecise_keys[k] = 0
                imprecise_keys[k] += 1
                
    print(f"Total Contexts: {total_contexts}")
    print(f"Precise: {precise_contexts}")
    print(f"Imprecise: {imprecise_contexts}")
    print(f"Metric (AbsContPrecision): {precise_contexts/total_contexts if total_contexts else 0:.4f}")
    
    print("Imprecise Keys and Counts:")
    for k, count in imprecise_keys.items():
        print(f"  {k}: {count} imprecise contexts (Total sizes: {cont_map[k]})")

analyze("/Users/timwhiting/koka/benchmarks/old-results/kcfa/0/0/analysis/benchmarks/koka-gen/build/mymakefile-example3.json", "0CFA")
analyze("/Users/timwhiting/koka/benchmarks/old-results/kcfa/0/1/analysis/benchmarks/koka-gen/build/mymakefile-example3.json", "1CFA")
