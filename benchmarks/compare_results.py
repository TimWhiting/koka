import json
import sys

def load_json(path):
    with open(path, 'r') as f:
        return json.load(f)

def compare_metrics(file1, file2):
    # Set up
    data1 = load_json(file1)
    data2 = load_json(file2)
    
    print(f"Comparing {file1} (KCFA) vs {file2} (DMCFAR)")

    # Define metrics to check
    # Based on plot_utils.py, RIR and Real Precision use:
    # - storeToStrSizes (Store Precision)
    # - structToContStrSizes (Continuation Precision)
    # - literal0CFAPrecise (Literal Precision)
    
    metrics = ["storeToStrSizes", "structToContStrSizes", "literal0CFAPrecise"]

    for metric in metrics:
        print(f"\n--- Metric: {metric} ---")
        
        # Locate metric map
        # It could be at top level or in storeMetrics
        m1 = data1.get(metric)
        if m1 is None: m1 = data1.get("storeMetrics", {}).get(metric)
        
        m2 = data2.get(metric)
        if m2 is None: m2 = data2.get("storeMetrics", {}).get(metric)
        
        if m1 is None and m2 is None:
            print("  (Metric not found in either file)")
            continue
            
        m1 = m1 or {}
        m2 = m2 or {}
        
        all_keys = set(m1.keys()) | set(m2.keys())
        
        diff_count = 0
        missing_in_kcfa = 0
        missing_in_dmcfar = 0
        precise_in_dmcfar_wins = 0 # Missing in DMCFAR or <=1 in DMCFAR whilst >1 in KCFA
        
        print(f"  Total keys in union: {len(all_keys)}")
        
        for k in all_keys:
            v1 = m1.get(k)
            v2 = m2.get(k)
            
            # Helper for booleans (literal0CFAPrecise)
            # Logic: False is Imprecise (>1 equivalent), True is Precise (<=1 equivalent)
            if isinstance(v1, bool): v1 = 1 if v1 else 2 # True -> 1 (Precise), False -> 2 (Imprecise)
            if isinstance(v2, bool): v2 = 1 if v2 else 2

            # Check for missing
            if v1 is None:
                missing_in_kcfa += 1
                # If missing in KCFA (Dead) but present in DMCFAR
                # This could be a regression if DMCFAR > 1
                if v2 > 1:
                    print(f"  [REGRESSION] Key missing in KCFA (Dead/Precise) but Imprecise in DMCFAR: {k[:80]}... | DMCFAR: {v2}")
                continue
                
            if v2 is None:
                missing_in_dmcfar += 1
                # Missing in DMCFAR (Dead) -> Precise (Size 0)
                # If KCFA was Imprecise (>1), this is a WIN for DMCFAR
                if v1 > 1:
                    precise_in_dmcfar_wins += 1
                    print(f"  [PRECISION WIN] Key Imprecise in KCFA but Missing (Dead) in DMCFAR: {k[:80]}... | KCFA: {v1}")
                continue
            
            # Both present
            if v1 != v2:
                diff_count += 1
                # Check for precision difference
                if v1 > 1 and v2 <= 1:
                     precise_in_dmcfar_wins += 1
                     print(f"  [PRECISION WIN] Key Imprecise in KCFA but Precise in DMCFAR: {k[:80]}... | KCFA: {v1} -> DMCFAR: {v2}")
                elif v1 <= 1 and v2 > 1:
                     print(f"  [REGRESSION] Key Precise in KCFA but Imprecise in DMCFAR: {k[:80]}... | KCFA: {v1} -> DMCFAR: {v2}")
                else:
                     # just different values (e.g. 2 vs 3, or bottom vs bottom?)
                     # If both > 1, it's just different degrees of imprecision
                     print(f"  [DIFF] Both Imprecise/Precise but different values: {k[:80]}... | KCFA: {v1} -> DMCFAR: {v2}")

        print(f"  Summary for {metric}:")
        print(f"    Missing in KCFA: {missing_in_kcfa}")
        print(f"    Missing in DMCFAR: {missing_in_dmcfar}")
        print(f"    Total Differences: {diff_count}")
        print(f"    Precision Wins for DMCFAR (KCFA > 1, DMCFAR <= 1 or Missing): {precise_in_dmcfar_wins}")

if __name__ == "__main__":
    compare_metrics(
        "benchmarks/results/kcfa/0/0/analysis/benchmarks/koka-gen/coop-communication/yield.json",
        "benchmarks/results/dmcfar/0/0/analysis/benchmarks/koka-gen/coop-communication/yield.json"
    )
