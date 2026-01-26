#!/usr/bin/env python3
"""
Find significant differences in benchmark results using git diff.
Aggregated by benchmark, ordered by sensitivity, formatted as a single-line table.
"""

import csv
import subprocess
import sys
import io
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# ANSI Color Codes
BOLD = "\033[1m"
RESET = "\033[0m"
RED = "\033[31m"
GREEN = "\033[32m"
YELLOW = "\033[33m"
BLUE = "\033[34m"
PURPLE = "\033[35m"
CYAN = "\033[36m"
MAGENTA = "\033[35m"

# Configuration
IGNORE_TIME_CHANGES_EXCEPT_TIMEOUTS = True
TIME_DIFF_THRESHOLD = 0.20
TIME_COLUMNS = {'Time', 'Time1', 'Time2', 'Time3'}

# The order of columns to display
COLUMN_ORDER = [
    'Analysis', 'File/Example', 'D', 'M(K)', 'Precise',
    'NEval', 'SumEval', 'PrecEval', 
    'NApply', 'SumApply', 'PrecApply', 
    'NK', 'SumK', 'PrecK', 
    'NS', 'SumS', 'PrecS', 
    'Time1', 'Time2', 'Time3'
]

def run_command(cmd: List[str]) -> str:
    """Run a shell command and return its output."""
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        return result.stdout
    except subprocess.CalledProcessError:
        return ""

def parse_sensitivity(path: str) -> Tuple[int, int]:
    """Extract D and M from path: benchmarks/results/D/M/..."""
    parts = Path(path).parts
    try:
        # Expected: ('benchmarks', 'results', 'D', 'M', ...)
        d = int(parts[2])
        m = int(parts[3])
        return (d, m)
    except (ValueError, IndexError):
        return (0, 0)

def get_changed_files() -> List[Tuple[int, int, str]]:
    """Get list of changed CSV files in benchmarks/results sorted by sensitivity."""
    output = run_command(['git', 'diff', '--name-only', 'benchmarks/results'])
    files = []
    for f in output.splitlines():
        if f.endswith('.csv'):
            d, m = parse_sensitivity(f)
            files.append((d, m, f))
    return sorted(files)

def get_git_file_content(filepath: str) -> Optional[str]:
    """Get the content of a file from the last git commit."""
    try:
        return run_command(['git', 'show', f'HEAD:{filepath}'])
    except:
        return None

def parse_csv(content: str) -> Dict[Tuple[str, str], Dict]:
    """Parse CSV content into a dictionary keyed by (Analysis, File/Example)."""
    results = {}
    f = io.StringIO(content)
    reader = csv.DictReader(f)
    for row in reader:
        key = (row.get('Analysis', ''), row.get('File/Example', ''))
        results[key] = row
    return results

def is_significant_change(col: str, old_val: str, new_val: str, old_row: Dict, new_row: Dict) -> bool:
    """Check if a change should be reported and highlighted."""
    old_val = str(old_val) if old_val is not None else ""
    new_val = str(new_val) if new_val is not None else ""
    
    # Row-level timeout status transition
    old_is_timeout = any(old_row.get(c) == 'timeout' for c in TIME_COLUMNS)
    new_is_timeout = any(new_row.get(c) == 'timeout' for c in TIME_COLUMNS)
    
    if old_is_timeout != new_is_timeout:
        # If row timeout status changed, show diff for all metrics/results
        # but skip the metadata/sensitivity columns that shouldn't change
        if col not in {'Analysis', 'File/Example', 'D', 'M(K)'}:
            return True

    if old_val == new_val:
        return False
    
    if col in TIME_COLUMNS:
        if IGNORE_TIME_CHANGES_EXCEPT_TIMEOUTS:
            return (old_val == 'timeout') != (new_val == 'timeout')
        try:
            ov = float(old_val)
            nv = float(new_val)
            return abs(nv - ov) / max(ov, 0.001) > TIME_DIFF_THRESHOLD
        except (ValueError, TypeError):
            return True
    return True

def is_worse(col: str, old_val: str, new_val: str, old_row: Dict, new_row: Dict) -> bool:
    """Determine if a change is a regression (worse)."""
    # Row-level timeout status transition: any -> timeout is worse, timeout -> any is better
    old_is_timeout = any(old_row.get(c) == 'timeout' for c in TIME_COLUMNS)
    new_is_timeout = any(new_row.get(c) == 'timeout' for c in TIME_COLUMNS)
    
    if new_is_timeout and not old_is_timeout:
        return True
    if old_is_timeout and not new_is_timeout:
        return False

    try:
        ov = float(old_val)
        nv = float(new_val)
    except (ValueError, TypeError):
        return False

    # N or Sum increased
    if col.startswith('N') or col.startswith('Sum') or col in TIME_COLUMNS:
        if col != 'NS' or len(col) == 2: # Avoid NS matches matching NSxxx if any
            return nv > ov

    # Prec decreased more than N decreased
    if col.startswith('Prec') and col != 'Precise':
        n_col = 'N' + col[4:] # e.g. PrecEval -> NEval
        try:
            old_n = float(old_row.get(n_col, 0))
            new_n = float(new_row.get(n_col, 0))
            # worse if (new_n - new_prec) > (old_n - old_prec)
            return (new_n - nv) > (old_n - ov)
        except (ValueError, TypeError):
            return nv < ov

    if col == 'Precise':
        return nv < ov # 1 -> 0 is worse

    return False

def format_cell(col: str, old_val: str, new_val: str, is_diff: bool, old_row: Dict, new_row: Dict) -> str:
    """Format a cell with ANSI colors if changed."""
    if not is_diff:
        return new_val
    
    worse = is_worse(col, old_val, new_val, old_row, new_row)
    arrow_color = RED if worse else GREEN
    
    return f"{BOLD}{BLUE}{old_val}{RESET}{BOLD}{arrow_color}→{RESET}{BOLD}{PURPLE}{new_val}{RESET}"

def print_table_diff(old_row: Optional[Dict], new_row: Optional[Dict], headers: List[str]):
    """Print a single row of the diff table."""
    cells = []
    
    # Use empty dicts for lookup if one row is missing
    orow = old_row if old_row else {}
    nrow = new_row if new_row else {}

    for col in headers:
        ov = str(orow.get(col, '') if orow.get(col) is not None else "")
        nv = str(nrow.get(col, '') if nrow.get(col) is not None else "")
        
        if old_row and new_row:
            diff = is_significant_change(col, ov, nv, orow, nrow)
            cells.append(format_cell(col, ov, nv, diff, orow, nrow))
        elif new_row:
            cells.append(f"{BOLD}{GREEN}{nv}{RESET}")
        else:
            cells.append(f"{BOLD}{RED}{ov}{RESET}")
            
    print(" | ".join(cells))

def main():
    changed_files = get_changed_files()
    if not changed_files:
        print("No changes found in benchmark results.")
        return

    # Group files by benchmark path (stripping sensitivity)
    groups = {}
    for d, m, path in changed_files:
        p = Path(path)
        # rel_path is everything after results/D/M/
        rel_path = "/".join(p.parts[4:])
        if rel_path not in groups:
            groups[rel_path] = []
        groups[rel_path].append((d, m, path))

    for benchmark_rel_path, files in sorted(groups.items()):
        # Aggregate all diffs for this benchmark across all sensitivities
        all_diff_records = []

        for d, m, filepath in files:
            old_raw = get_git_file_content(filepath)
            with open(filepath, 'r') as f:
                new_raw = f.read()
            
            old_data = parse_csv(old_raw) if old_raw else {}
            new_data = parse_csv(new_raw)
            all_keys = set(old_data.keys()) | set(new_data.keys())
            
            for key in all_keys:
                old_row = old_data.get(key)
                new_row = new_data.get(key)
                
                # Check if this specific row has significant diffs
                has_diff = False
                if not old_row or not new_row:
                    has_diff = True
                else:
                    for col in COLUMN_ORDER:
                        if is_significant_change(col, old_row.get(col, ''), new_row.get(col, ''), old_row, new_row):
                            has_diff = True
                            break
                
                if has_diff:
                    # key is (Analysis, File/Example)
                    analysis, file_example = key
                    all_diff_records.append({
                        'sort_key': (file_example, analysis, d, m),
                        'old_row': old_row,
                        'new_row': new_row
                    })

        if all_diff_records:
            print(f"\n{BOLD}{CYAN}Benchmark: {benchmark_rel_path}{RESET}")
            
            # Print header
            header_line = " | ".join([f"{BOLD}{MAGENTA}{h}{RESET}" for h in COLUMN_ORDER])
            print(header_line)
            print("-" * (len(header_line) // 2))

            # Sort aggregated diffs by (File/Example, Analysis, D, M)
            all_diff_records.sort(key=lambda x: x['sort_key'])

            for record in all_diff_records:
                print_table_diff(record['old_row'], record['new_row'], COLUMN_ORDER)

if __name__ == "__main__":
    main()
