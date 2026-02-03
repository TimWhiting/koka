#!/usr/bin/env python3
"""
Check for missing benchmark result files.
Identifies cases where some benchmarks from a file ran but others didn't.
"""

import json
import os
import re
from collections import defaultdict
from pathlib import Path

def extract_benchmark_functions(file_path):
    """Extract analyze-* function names from a Koka file."""
    functions = []
    try:
        with open(file_path, 'r') as f:
            content = f.read()
            # Match pub fun analyze-name() or fun analyze-name()
            pattern = r'(?:pub\s+)?fun\s+analyze-([a-zA-Z0-9_-]+)\s*\('
            matches = re.findall(pattern, content)
            functions = matches
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
    return functions

def get_benchmark_files():
    """Get all benchmark .kk files and their expected functions."""
    benchmark_root = Path('analysis/benchmarks')
    benchmark_files = {}
    
    for kk_file in benchmark_root.rglob('*.kk'):
        # Get relative path from benchmark root
        rel_path = kk_file.relative_to('analysis')
        # Remove .kk extension for the benchmark name
        bench_name = str(rel_path.with_suffix(''))
        
        functions = extract_benchmark_functions(kk_file)
        if functions:
            benchmark_files[bench_name] = {
                'file': str(kk_file),
                'functions': functions
            }
    
    return benchmark_files

def check_results(benchmark_files):
    """Check which result files exist for each benchmark."""
    results_root = Path('benchmarks/results')
    
    # Get all variants and configurations
    variants = []
    if results_root.exists():
        variants = [d.name for d in results_root.iterdir() if d.is_dir()]
    
    missing = defaultdict(lambda: defaultdict(list))
    
    for bench_name, info in benchmark_files.items():
        expected_functions = info['functions']
        
        for variant in variants:
            variant_path = results_root / variant
            
            # Find all d/m configurations for this variant
            configs = []
            for d_dir in variant_path.iterdir():
                if d_dir.is_dir() and d_dir.name.isdigit():
                    for m_dir in d_dir.iterdir():
                        if m_dir.is_dir() and m_dir.name.isdigit():
                            configs.append((d_dir.name, m_dir.name))
            
            for d, m in configs:
                config_key = f"{variant} ({d},{m})"
                result_dir = variant_path / d / m / bench_name
                
                if result_dir.exists():
                    # Check which functions have result files
                    existing_files = {f.stem for f in result_dir.glob('*.json')}
                    
                    # Find missing functions
                    missing_functions = [f for f in expected_functions if f not in existing_files]
                    
                    if missing_functions and len(existing_files) > 0:
                        # Only report if some (but not all) files exist
                        missing[bench_name][config_key] = {
                            'missing': missing_functions,
                            'existing': list(existing_files),
                            'expected': len(expected_functions)
                        }
    
    return missing

def main():
    print("=" * 80)
    print("CHECKING FOR MISSING BENCHMARK RESULTS")
    print("=" * 80)
    print()
    
    print("Scanning benchmark files...")
    benchmark_files = get_benchmark_files()
    print(f"Found {len(benchmark_files)} benchmark files with analyze-* functions")
    print()
    
    print("Checking for missing results...")
    missing = check_results(benchmark_files)
    
    if not missing:
        print("\n✓ No missing benchmark results found!")
        print("  All benchmark functions that ran produced complete results.")
        return
    
    print(f"\n⚠️  Found {len(missing)} benchmark files with missing results:\n")
    
    for bench_name in sorted(missing.keys()):
        print(f"\n{bench_name}")
        print(f"  File: {benchmark_files[bench_name]['file']}")
        
        configs = missing[bench_name]
        for config_key in sorted(configs.keys()):
            info = configs[config_key]
            print(f"\n  {config_key}:")
            print(f"    Expected: {info['expected']} functions")
            print(f"    Got: {len(info['existing'])} results")
            print(f"    Missing ({len(info['missing'])}): {', '.join(info['missing'])}")
        print()
    
    # Summary
    total_missing = sum(len(configs) for configs in missing.values())
    print("=" * 80)
    print(f"SUMMARY: {len(missing)} benchmark files have incomplete results")
    print(f"         across {total_missing} configurations")
    print("=" * 80)

if __name__ == "__main__":
    main()
