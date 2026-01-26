#!/usr/bin/env python3
"""
Find and report all benchmark results that contain timeouts.
Scans benchmarks/results/ directory for CSV files.
"""

import csv
import sys
from pathlib import Path
from typing import List, Tuple

# ANSI Colors
BOLD = "\033[1m"
RESET = "\033[0m"
RED = "\033[31m"
CYAN = "\033[36m"
MAGENTA = "\033[35m"

TIME_COLUMNS = {'Time', 'Time1', 'Time2', 'Time3'}

def parse_sensitivity(path: Path) -> Tuple[int, int]:
    """Extract D and M from path: benchmarks/results/D/M/..."""
    parts = path.parts
    try:
        # Expected: (..., 'results', 'D', 'M', ...)
        idx = parts.index('results')
        d = int(parts[idx+1])
        m = int(parts[idx+2])
        return (d, m)
    except (ValueError, IndexError):
        return (0, 0)

def main():
    results_dir = Path("benchmarks/results")
    if not results_dir.exists():
        print(f"Error: {results_dir} not found.")
        sys.exit(1)

    csv_files = list(results_dir.glob("**/*.csv"))
    if not csv_files:
        print("No CSV files found in benchmarks/results.")
        return

    # Sort files by sensitivity and then by name
    sorted_files = sorted(csv_files, key=lambda p: (parse_sensitivity(p), str(p)))

    found_any = False
    current_benchmark = None

    for filepath in sorted_files:
        p = Path(filepath)
        # Get relative path after D/M/
        parts = p.parts
        try:
            idx = parts.index('results')
            rel_path = "/".join(parts[idx+3:])
        except (ValueError, IndexError):
            rel_path = str(filepath)

        timeouts = []
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                reader = csv.DictReader(f)
                for row in reader:
                    if any(row.get(col) == 'timeout' for col in TIME_COLUMNS):
                        timeouts.append(row)
        except Exception as e:
            print(f"Error reading {filepath}: {e}")
            continue

        if timeouts:
            found_any = True
            if rel_path != current_benchmark:
                current_benchmark = rel_path
                print(f"\n{BOLD}{CYAN}Benchmark: {rel_path}{RESET}")
                
            d, m = parse_sensitivity(filepath)
            
            for row in timeouts:
                analysis = row.get('Analysis', 'unknown')
                example = row.get('File/Example', 'unknown')
                
                # Identify which specific column timed out
                cols = [c for c in TIME_COLUMNS if row.get(c) == 'timeout']
                cols_str = ", ".join(cols)
                
                print(f"  {BOLD}{MAGENTA}{analysis}{RESET} | {example:40} | D={d}, M={m} | {BOLD}{RED}Timeout in {cols_str}{RESET}")

    if not found_any:
        print("No results with timeouts found.")

if __name__ == "__main__":
    main()
