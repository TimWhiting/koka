import json

path = "benchmarks/results/kcfa/0/0/analysis/benchmarks/koka-gen/coop-communication/yield.json"

with open(path, 'r') as f:
    data = json.load(f)

print("Top level keys:")
for k in data.keys():
    print(f" - {k}")

print("\nstoreMetrics keys:")
if "storeMetrics" in data:
    for k in data["storeMetrics"].keys():
        print(f" - {k}")
