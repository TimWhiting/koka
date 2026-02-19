import os
import json

BASE_DIR = 'benchmarks/results/dmcfae/0/0'
NEW_DIR = 'benchmarks/results/dmcfar/1/1'

def load_json(path):
    with open(path, 'r') as f:
        return json.load(f)

import re

CRITICAL_MAPS = {
    'storeToStrSizes', 
    'structToContStrSizes', 
    'literal0CFAPrecise'
}

# Regex for invalid keys (name:number), e.g., "exn:1906", "nim:1000"

def check_subset(base_data, new_data, filename):
    base_metrics = base_data.get('storeMetrics', {})
    new_metrics = new_data.get('storeMetrics', {})
    
    violations = []
    
    # Check only critical maps used for graphs/metrics
    for map_name in CRITICAL_MAPS:
        new_map = new_metrics.get(map_name)
        if not new_map or not isinstance(new_map, dict):
            continue
            
        base_map = base_metrics.get(map_name, {})
        if not isinstance(base_map, dict):
            base_map = {}

        # Filter keys to separate stable from invalid
        new_stable_keys = {k for k in new_map.keys()}
        base_stable_keys = {k for k in base_map.keys()}
        
        # Check subset: New Stable MUST be in Base Stable
        missing = new_stable_keys - base_stable_keys
        
        if missing:
            # Format examples for readability
            examples = list(missing)[:5]
            violations.append(f"Map '{map_name}': {len(missing)} stable keys found in New but not in Base. Examples: {examples}")
            
    if violations:
        print(f"\n[VIOLATION] {filename}")
        for v in violations:
            print(f"  - {v}")
        return False
    return True

def main():
    print(f"Verifying reachability consistency: New ({NEW_DIR}) <= Base ({BASE_DIR})")
    
    count_checked = 0
    count_violations = 0
    
    for root, dirs, files in os.walk(NEW_DIR):
        for file in files:
            if not file.endswith('.json'):
                continue
                
            new_path = os.path.join(root, file)
            rel_path = os.path.relpath(new_path, NEW_DIR)
            base_path = os.path.join(BASE_DIR, rel_path)
            
            if not os.path.exists(base_path):
                print(f"[SKIP] Base result not found for {rel_path}")
                continue
                
            try:
                new_data = load_json(new_path)
                base_data = load_json(base_path)
                
                # verify parameters
                # print(f"Checking {rel_path} (New: m={new_data.get('m')}, d={new_data.get('d')} | Base: m={base_data.get('m')}, d={base_data.get('d')})")
                
                if not check_subset(base_data, new_data, rel_path):
                    count_violations += 1
                
                count_checked += 1
                
            except Exception as e:
                print(f"[ERROR] Failed to process {rel_path}: {e}")

    print(f"\n--- Summary ---")
    print(f"Checked: {count_checked}")
    print(f"Violations: {count_violations}")
    if count_violations == 0:
        print("SUCCESS: 1,1-HMCFAR reachability is a subset of 0,0-HMCFAR.")
    else:
        print("FAILURE: Found spurious reachability in 1,1-HMCFAR.")

if __name__ == "__main__":
    main()
