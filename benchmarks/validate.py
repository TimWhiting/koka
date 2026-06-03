#!/usr/bin/env python3
"""
validate.py — Compare benchmark results against the reference data in results-cached/.

Usage (from the koka repository root):
    python3 benchmarks/validate.py

For each JSON file in benchmarks/results-cached/, locate the corresponding file
in benchmarks/results/ and compare all fields except `analysisTimes`.  A
mismatch in `isTimeout` is a WARN (expected on machines faster/slower than the
reference M3 Max); a mismatch in any other field is a FAIL.

Exit code: 0 if no FAILs, 1 if any FAILs.
"""

import json
import os
import sys

CACHED_DIR = "benchmarks/results-cached"
RESULTS_DIR = "benchmarks/results"
TIMING_KEYS = {"analysisTimes"}


def load(path):
    with open(path) as f:
        return json.load(f)


def strip_timing(obj):
    """Recursively remove timing keys from dicts."""
    if isinstance(obj, dict):
        return {k: strip_timing(v) for k, v in obj.items() if k not in TIMING_KEYS}
    if isinstance(obj, list):
        return [strip_timing(v) for v in obj]
    return obj


def deep_diff(ref, new, path=""):
    """Yield (path, ref_val, new_val) for every differing leaf."""
    if isinstance(ref, dict) and isinstance(new, dict):
        for k in ref:
            child = f"{path}.{k}" if path else k
            if k not in new:
                yield child, ref[k], "<missing>"
            else:
                yield from deep_diff(ref[k], new[k], child)
        for k in new:
            if k not in ref:
                child = f"{path}.{k}" if path else k
                yield child, "<missing>", new[k]
    elif ref != new:
        yield path, ref, new


def compare(ref_path, new_path):
    """Return ("PASS"|"WARN"|"FAIL", [messages])."""
    ref = strip_timing(load(ref_path))
    new = strip_timing(load(new_path))

    # Split out isTimeout so we can warn rather than fail on it.
    ref_timeout = ref.pop("isTimeout", None)
    new_timeout = new.pop("isTimeout", None)

    messages = []
    status = "PASS"

    if ref_timeout != new_timeout:
        messages.append(
            f"  WARN isTimeout: reference={ref_timeout}, yours={new_timeout}"
            " (expected on machines with different speed)"
        )
        status = "WARN"

    for field_path, ref_val, new_val in deep_diff(ref, new):
        # Summarise large diffs to avoid flooding the terminal.
        if isinstance(ref_val, dict) and len(ref_val) > 5:
            ref_val = f"<dict with {len(ref_val)} keys>"
        if isinstance(new_val, dict) and len(new_val) > 5:
            new_val = f"<dict with {len(new_val)} keys>"
        messages.append(f"  FAIL {field_path}: reference={ref_val!r}, yours={new_val!r}")
        status = "FAIL"

    return status, messages


def main():
    if not os.path.isdir(CACHED_DIR):
        print(f"ERROR: reference directory not found: {CACHED_DIR}")
        sys.exit(1)

    counts = {"PASS": 0, "WARN": 0, "FAIL": 0, "MISSING": 0}
    fail_files = []

    cached_files = sorted(
        os.path.join(root, fname)
        for root, _, files in os.walk(CACHED_DIR)
        for fname in files
        if fname.endswith(".json")
    )

    if not cached_files:
        print(f"No reference JSON files found in {CACHED_DIR}.")
        sys.exit(0)

    results_empty = not os.path.isdir(RESULTS_DIR) or not any(
        True for _, _, fs in os.walk(RESULTS_DIR) for f in fs if f.endswith(".json")
    )

    if results_empty:
        print(
            f"No results found in {RESULTS_DIR}. "
            "Run the benchmarks first (Step 3 in the README), "
            "or this step can be skipped."
        )
        sys.exit(0)

    for ref_path in cached_files:
        rel = os.path.relpath(ref_path, CACHED_DIR)
        new_path = os.path.join(RESULTS_DIR, rel)

        if not os.path.exists(new_path):
            counts["MISSING"] += 1
            continue

        try:
            status, messages = compare(ref_path, new_path)
        except Exception as exc:
            status, messages = "FAIL", [f"  ERROR reading files: {exc}"]

        counts[status] += 1
        label = f"[{status}]"
        print(f"{label:<8} {rel}")
        for msg in messages:
            print(msg)
        if status == "FAIL":
            fail_files.append(rel)

    total = sum(counts.values())
    print()
    print("=" * 60)
    print(f"Results: {total} files checked")
    print(f"  PASS   : {counts['PASS']}")
    print(f"  WARN   : {counts['WARN']}  (isTimeout mismatch — machine speed differs)")
    print(f"  FAIL   : {counts['FAIL']}")
    print(f"  MISSING: {counts['MISSING']}  (not yet generated on your machine)")
    print("=" * 60)

    if fail_files:
        print(f"\nFailed files ({len(fail_files)}):")
        for f in fail_files:
            print(f"  {f}")
        sys.exit(1)
    else:
        if counts["WARN"]:
            print(
                "\nWARNINGs indicate timeout status differs from the reference M3 Max."
                "\nThis is expected — precision metrics matched."
            )
        print("\nValidation passed.")
        sys.exit(0)


if __name__ == "__main__":
    main()
