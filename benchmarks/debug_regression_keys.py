
import json
import os

def load_json(path):
    with open(path, 'r') as f:
        return json.load(f)

def check_benchmark(name, base_path, m1_path, m2_path):
    print(f"--- Analyzing {name} ---")
    base = load_json(base_path)['storeMetrics']['literal0CFAPrecise']
    m1 = load_json(m1_path)['storeMetrics']['literal0CFAPrecise']
    m2 = load_json(m2_path)['storeMetrics']['literal0CFAPrecise']
    
    # Analyze Impact on Score (Base=False keys only)
    relevant_keys = [k for k, v in base.items() if v is False]
    print(f"Total Relevant Keys (Base=False): {len(relevant_keys)}")
    
    m1_hits = 0
    m2_hits = 0
    
    loss_keys = []
    gain_keys = []
    
    for k in relevant_keys:
        # m1 Status
        # Hit if Missing OR True
        m1_hit = (k not in m1) or (m1[k] is True)
        
        # m2 Status
        m2_hit = (k not in m2) or (m2[k] is True)
        
        if m1_hit: m1_hits += 1
        if m2_hit: m2_hits += 1
        
        if m1_hit and not m2_hit:
            loss_keys.append(k)
        if not m1_hit and m2_hit:
            gain_keys.append(k)
            
    print(f"m=1 Hits: {m1_hits}")
    print(f"m=2 Hits: {m2_hits}")
    print(f"Net Change: {m2_hits - m1_hits}")
    
    print(f"\nLosses (m1 Hit -> m2 Miss): {len(loss_keys)}")
    # Loss Logic: m1 was (Dead or Precise), m2 is (Reachable & Imprecise)
    for k in loss_keys[:10]:
        status_m1 = "Dead" if k not in m1 else ("Precise" if m1[k] else "Imprecise")
        status_m2 = "Dead" if k not in m2 else ("Precise" if m2[k] else "Imprecise")
        print(f"  {k}: m1={status_m1} -> m2={status_m2}")

    print(f"\nGains (m1 Miss -> m2 Hit): {len(gain_keys)}")
    for k in gain_keys[:10]:
        status_m1 = "Dead" if k not in m1 else ("Precise" if m1[k] else "Imprecise")
        status_m2 = "Dead" if k not in m2 else ("Precise" if m2[k] else "Imprecise")
        print(f"  {k}: m1={status_m1} -> m2={status_m2}")

base = "benchmarks/results-cached/kcfa/0/0/analysis/benchmarks/koka-gen/mini-ppl/burglar.json"
m1 = "benchmarks/results-cached/dmcfar/1/1/analysis/benchmarks/koka-gen/mini-ppl/burglar.json"
m2 = "benchmarks/results-cached/dmcfar/1/2/analysis/benchmarks/koka-gen/mini-ppl/burglar.json"

check_benchmark("Burglar", base, m1, m2)
