"""
Compare three ways of resuming a local-variable read in HMCFA (DMCFAR):
  lose  resume with the dynamic context outside the variable (the original code)
  add   re-enter the variable: a new delimiter level, with one more call
  keep  resume with the read's own dynamic context, from the variable's level outwards

Uses the metrics of benchmarks/plot_utils.py: strict RIR against the 0CFA DMCFA baseline (dmcfae d=0 m=0),
for values (store + literals) and continuations, aggregated by the shifted geometric mean like
plot_categorical_metrics.py. All modes share the same baseline, k-CFA, and d=0 runs.

usage: python compare.py <merged-dir> <plot_utils-dir>   (merged-dir/<mode>/benchmarks/results)
"""
import sys, os
import numpy as np
import pandas as pd

merged, utils_dir = sys.argv[1], sys.argv[2]
sys.path.insert(0, utils_dir)
from plot_utils import load_results_with_baselines, get_benchmark_category, shifted_geometric_mean

MODES = ['lose', 'add', 'keep']
CONFIGS = [('kcfa', 0, 1, '1-kCFA'), ('kcfa', 0, 2, '2-kCFA'),
           ('dmcfar', 0, 1, 'H(0,1)'), ('dmcfar', 0, 2, 'H(0,2)'),
           ('dmcfar', 1, 0, 'H(1,0)'), ('dmcfar', 1, 1, 'H(1,1)'), ('dmcfar', 1, 2, 'H(1,2)'),
           ('dmcfar', 2, 0, 'H(2,0)'), ('dmcfar', 2, 1, 'H(2,1)'), ('dmcfar', 2, 2, 'H(2,2)')]
METRICS = [('prec_val_rir_strict', 'Value RIR'), ('prec_cont_rir_strict', 'Cont RIR')]

frames = []
for mode in MODES:
    df = pd.DataFrame(load_results_with_baselines(os.path.join(merged, mode, 'benchmarks', 'results')))
    df['mode'] = mode
    frames.append(df)
df = pd.concat(frames, ignore_index=True)
df['d'] = df['d'].astype(int); df['m'] = df['m'].astype(int)
df['bench'] = df['benchmarkName'].str.replace('analysis/benchmarks/', '', regex=False)
label = {(v, d, m): l for v, d, m, l in CONFIGS}
df['config'] = [label.get((v, d, m)) for v, d, m in zip(df['variant'], df['d'], df['m'])]
df = df[df['config'].notna()]

def agg(sub, col):
    vals = sub[~sub['isTimeout']][col].dropna()
    return shifted_geometric_mean(vals) if len(vals) else np.nan

print(f"Benchmark examples: {df['bench'].nunique()} (from {df['bench'].str.rsplit('/', n=1).str[0].nunique()} programs)\n")

# 1. per configuration and mode, over the examples each run finished
print("## Strict RIR vs 0CFA DMCFA, per configuration (shifted geomean over finished examples)\n")
rows = []
for v, d, m, l in CONFIGS:
    row = {'config': l}
    for mode in MODES:
        sub = df[(df['config'] == l) & (df['mode'] == mode)]
        for col, name in METRICS:
            row[f'{name} {mode}'] = agg(sub, col)
        row[f'T/O {mode}'] = int(sub['isTimeout'].sum())
        row[f'n {mode}'] = len(sub)
    rows.append(row)
t1 = pd.DataFrame(rows).set_index('config')
with pd.option_context('display.width', 250, 'display.max_columns', 50, 'display.float_format', '{:.3f}'.format):
    print(t1.to_string()); print()

# 2. the same, restricted to examples every mode finished for that configuration (a like-for-like comparison)
print("## Same, only examples finished in all three modes\n")
rows = []
for v, d, m, l in CONFIGS:
    sub = df[df['config'] == l]
    ok = sub[~sub['isTimeout']].groupby('bench')['mode'].nunique()
    common = set(ok[ok == len(MODES)].index)
    row = {'config': l, 'examples': len(common)}
    for col, name in METRICS:
        for mode in MODES:
            s = sub[(sub['mode'] == mode) & sub['bench'].isin(common)]
            row[f'{name} {mode}'] = agg(s, col)
    for mode in MODES:
        s = sub[(sub['mode'] == mode) & sub['bench'].isin(common)]
        row[f'Median states {mode}'] = s['States'].median() if len(s) else np.nan
        row[f'Total time (s) {mode}'] = s['Time'].sum() if len(s) else np.nan
    rows.append(row)
t2 = pd.DataFrame(rows).set_index('config')
with pd.option_context('display.width', 250, 'display.max_columns', 50, 'display.float_format', '{:.3f}'.format):
    print(t2.to_string()); print()

# 3. per example: where the modes differ (d >= 1 only; d = 0 runs are shared)
print("## Per example, where the modes differ (Value RIR / Cont RIR / States, T/O = timeout)\n")
def cell(r):
    if r is None: return '-'
    if r['isTimeout']: return 'T/O'
    return f"{r['prec_val_rir_strict']:.2f}/{r['prec_cont_rir_strict']:.2f}/{int(r['States'])}"
lines = []
for (bench, conf), g in df[df['d'] >= 1].groupby(['bench', 'config']):
    by = {r['mode']: r for _, r in g.iterrows()}
    cells = [cell(by.get(mode)) for mode in MODES]
    if len(set(cells)) > 1:
        lines.append((bench, conf, cells))
print(f"{'example':<55} {'config':<7} " + ' '.join(f'{m:<22}' for m in MODES))
for bench, conf, cells in sorted(lines):
    print(f"{bench:<55} {conf:<7} " + ' '.join(f'{c:<22}' for c in cells))
print(f"\n{len(lines)} (example, configuration) pairs differ between modes.")
