import json
import sys

def load_json(path):
    with open(path, 'r') as f:
        return json.load(f)

def compare_metrics(file1, file2):
    data1 = load_json(file1)
    data2 = load_json(file2)

    # 1. Check structToContStrSizes
    metric = "structToContStrSizes"
    print(f"\n--- {metric} ---")
    m1 = data1.get("storeMetrics", {}).get(metric, {})
    m2 = data2.get("storeMetrics", {}).get(metric, {})

    if not m1 and not m2:
        print(f"Metric {metric} not found in storeMetrics.")
    else:
        # Check for keys in KCFA (m1) but missing in DMCFAR (m2)
        missing_in_2 = 0
        hits_from_missing = 0
        
        for k, v1 in m1.items():
            if k not in m2:
                missing_in_2 += 1
                if v1 > 1:
                    hits_from_missing += 1
                    print(f"Key MISSING in DMCFAR (Dead/Precise): {k} | KCFA Value: {v1}")
        
        print(f"Total Missing in DMCFAR: {missing_in_2}")
        print(f"Hits from Missing (KCFA > 1): {hits_from_missing}")

    # 2. Check literal0CFAPrecise
    metric = "literal0CFAPrecise"
    print(f"\n--- {metric} ---")
    # Note: literal0CFAPrecise is a top-level key in some versions or inside storeMetrics or elsewhere?
    # Based on calc_literal_prod_stats, it seems to be in the root object passed to it.
    # The 'm' passed to calc_literal_prod_stats might be the whole object or storeMetrics?
    # Looking at plot_utils cleanup: m = compute_metrics(r, baseline) -> r is the run object.
    # So literal0CFAPrecise is likely at the top level or inside storeMetrics.
    
    m1 = data1.get(metric)
    if m1 is None: m1 = data1.get("storeMetrics", {}).get(metric)
    
    m2 = data2.get(metric)
    if m2 is None: m2 = data2.get("storeMetrics", {}).get(metric)
    
    if not m1 and not m2:
        print(f"Metric {metric} not found.")
    else:
        imprecise_in_kcfa = 0
        improved_in_dmcfar = 0
        dead_in_dmcfar = 0
        
        for k, v1 in m1.items():
            if v1 is False: # Imprecise in KCFA
                imprecise_in_kcfa += 1
                
                v2 = m2.get(k)
                if v2 is None: # Missing in DMCFAR -> Dead -> Precise
                    dead_in_dmcfar += 1
                    print(f"Literal MISSING in DMCFAR (Dead): {k}")
                elif v2 is True: # Precise in DMCFAR
                    improved_in_dmcfar += 1
                    print(f"Literal PRECISE in DMCFAR (Improved): {k}")
        
        print(f"Total Imprecise in KCFA: {imprecise_in_kcfa}")
        print(f"  -> Dead in DMCFAR (Missing): {dead_in_dmcfar}")
        print(f"  -> Improved in DMCFAR (True): {improved_in_dmcfar}")

if __name__ == "__main__":
    compare_metrics(
        "benchmarks/results/kcfa/0/0/analysis/benchmarks/koka-gen/coop-communication/yield.json",
        "benchmarks/results/dmcfar/0/0/analysis/benchmarks/koka-gen/coop-communication/yield.json"
    )
