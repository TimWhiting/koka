from pathlib import Path

RESULTS_BASE = Path("benchmarks/results")

print(f"Checking {RESULTS_BASE}")
if not RESULTS_BASE.exists():
    print("RESULTS_BASE does not exist")
else:
    print("RESULTS_BASE exists")
    count = 0
    for d_dir in RESULTS_BASE.iterdir():
        if d_dir.is_dir() and d_dir.name.isdigit():
            for m_dir in d_dir.iterdir():
                if m_dir.is_dir() and m_dir.name.isdigit():
                    for csv_file in m_dir.rglob("*.csv"):
                        count += 1
                        if count <= 5:
                            print(f"Found: {csv_file}")
    print(f"Total CSV files found: {count}")
