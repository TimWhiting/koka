
import json

def check_map_sizes(path, name):
    with open(path) as f:
        data = json.load(f)
    
    m = data.get('storeMetrics', {})
    
    print(f"--- {name} ---")
    print(f"numContAddresses (Metric): {m.get('numContAddresses')}")
    print(f"contStrSingletons (Metric): {m.get('contStrSingletons')}")
    
    maps = [
        'structToContStrSizes',
        'structToContSemSizes',
        'structToStrRetSizes',
        'contSemSingletons', # Likely an int, but checking
        'semCallTargetSizes'
    ]
    
    for map_name in maps:
        val = m.get(map_name)
        if isinstance(val, dict):
            count = len(val)
            total_elements = sum(len(v) for v in val.values()) if val and isinstance(list(val.values())[0], list) else 0
            print(f"{map_name}: {count} keys, {total_elements} total elements")
        else:
             print(f"{map_name}: {val} (Type: {type(val)})")

check_map_sizes("/Users/timwhiting/koka/benchmarks/old-results/kcfa/0/0/analysis/benchmarks/koka-gen/build/mymakefile-example3.json", "0CFA")
check_map_sizes("/Users/timwhiting/koka/benchmarks/old-results/kcfa/0/1/analysis/benchmarks/koka-gen/build/mymakefile-example3.json", "1CFA")
