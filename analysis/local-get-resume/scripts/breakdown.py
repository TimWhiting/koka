"""
Per-example view of how the local-read resume modes change results (companion to compare.py).

For each example and each HMCFA configuration with d >= 1 (d = 0 and k-CFA are the same in every mode),
compare lose (the original code) with keep and with add:
  precision  change in strict value / continuation RIR vs 0CFA DMCFA (|delta| > 0.005, as get_tradeoff_color)
  cost       ratio of analysis states and time
  status     timeouts fixed or introduced
Writes a per-example table, a per-program summary, and tradeoff plots in the style of
plot_expert_tradeoff_metrics.py (an x at lose, a line to an o at keep).

usage: python breakdown.py <merged-dir> <plot_utils-dir> <out-dir>
"""
import sys, os
import numpy as np
import pandas as pd
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import seaborn as sns
from matplotlib.lines import Line2D

merged, utils_dir, out = sys.argv[1], sys.argv[2], sys.argv[3]
os.makedirs(out, exist_ok=True)
sys.path.insert(0, utils_dir)
from plot_utils import load_results_with_baselines, get_tradeoff_color

MODES = ['lose', 'add', 'keep']
EPS = 0.005
frames = []
for mode in MODES:
    df = pd.DataFrame(load_results_with_baselines(os.path.join(merged, mode, 'benchmarks', 'results')))
    df['mode'] = mode
    frames.append(df)
df = pd.concat(frames, ignore_index=True)
df['d'] = df['d'].astype(int); df['m'] = df['m'].astype(int)
df['bench'] = df['benchmarkName'].str.replace('analysis/benchmarks/', '', regex=False)
df['program'] = df['bench'].str.rsplit('/', n=1).str[0]
df = df[(df['variant'] == 'dmcfar') & (df['d'] >= 1)].copy()
df['config'] = 'H(' + df['d'].astype(str) + ',' + df['m'].astype(str) + ')'
df['ok'] = df['status'] == 'OK'

cols = ['prec_val_rir_strict', 'prec_cont_rir_strict', 'States', 'Time', 'ok']
wide = df.pivot_table(index=['program', 'bench', 'config'], columns='mode', values=cols, aggfunc='first')
wide.columns = [f'{c}_{m}' for c, m in wide.columns]
wide = wide.reset_index()

def classify(r, new):
    okb, okn = bool(r['ok_lose']), bool(r[f'ok_{new}'])
    if not okb and not okn: return 'both time out'
    if not okb: return 'timeout fixed'
    if not okn: return 'new timeout'
    dv = r[f'prec_val_rir_strict_{new}'] - r['prec_val_rir_strict_lose']
    dc = r[f'prec_cont_rir_strict_{new}'] - r['prec_cont_rir_strict_lose']
    better, worse = (dv > EPS or dc > EPS), (dv < -EPS or dc < -EPS)
    if better and worse: return 'mixed precision'
    if better: return 'more precise'
    if worse: return 'less precise'
    sr = r[f'States_{new}'] / r['States_lose']
    if sr < 0.9: return 'same precision, fewer states'
    if sr > 1.1: return 'same precision, more states'
    return 'unchanged'

for new in ['keep', 'add']:
    wide[f'class_{new}'] = wide.apply(lambda r: classify(r, new), axis=1)
    wide[f'dval_{new}'] = wide[f'prec_val_rir_strict_{new}'] - wide['prec_val_rir_strict_lose']
    wide[f'dcont_{new}'] = wide[f'prec_cont_rir_strict_{new}'] - wide['prec_cont_rir_strict_lose']
    wide[f'states_ratio_{new}'] = wide[f'States_{new}'] / wide['States_lose']
    wide[f'time_ratio_{new}'] = wide[f'Time_{new}'] / wide['Time_lose']

pd.set_option('display.width', 250); pd.set_option('display.max_rows', 500); pd.set_option('display.max_columns', 50)
order = ['more precise', 'less precise', 'mixed precision', 'timeout fixed', 'new timeout',
         'same precision, fewer states', 'same precision, more states', 'unchanged', 'both time out']

with open(os.path.join(out, 'breakdown.txt'), 'w') as f:
    def p(*a): print(*a); print(*a, file=f)
    for new in ['keep', 'add']:
        p(f'\n## lose -> {new}: (example, config) pairs per outcome, configs H(1..2, 0..2)\n')
        p(wide[f'class_{new}'].value_counts().reindex(order, fill_value=0).to_string())
        p(f'\n## lose -> {new}, per program: outcome counts over its (example, config) pairs, '
          f'and the median states / time ratio ({new}/lose) where both finished\n')
        t = pd.crosstab(wide['program'], wide[f'class_{new}']).reindex(columns=order, fill_value=0)
        t = t.loc[:, (t != 0).any()]
        both = wide[wide['ok_lose'].astype(bool) & wide[f'ok_{new}'].astype(bool)]
        t['states x'] = both.groupby('program')[f'states_ratio_{new}'].median().round(2)
        t['time x'] = both.groupby('program')[f'time_ratio_{new}'].median().round(2)
        p(t.to_string())
    p('\n## Per example where lose and keep differ in precision or status '
      '(RIR value/cont: lose -> keep, add; states lose -> keep)\n')
    sel = wide[~wide['class_keep'].str.startswith('same') & (wide['class_keep'] != 'unchanged')
               | ~wide['class_add'].str.startswith('same') & (wide['class_add'] != 'unchanged')]
    def fmt(r, m):
        if not r[f'ok_{m}']: return 'T/O'
        return f"{r[f'prec_val_rir_strict_{m}']:.2f}/{r[f'prec_cont_rir_strict_{m}']:.2f}"
    for _, r in sel.iterrows():
        st = lambda m: f"{int(r[f'States_{m}'])}" if r[f'ok_{m}'] else 'T/O'
        p(f"{r['bench']:<46} {r['config']:<7} {fmt(r,'lose'):>9} -> {fmt(r,'keep'):>9}, {fmt(r,'add'):>9}   "
          f"states {st('lose'):>7} -> {st('keep'):>7}   [{r['class_keep']}]")
wide.to_csv(os.path.join(out, 'breakdown.csv'), index=False)

# Tradeoff plots, lose (x) -> keep (o), one row per configuration, value and continuation RIR against time.
sns.set_theme(style='whitegrid', font_scale=1.1)
configs = ['H(1,0)', 'H(1,1)', 'H(1,2)', 'H(2,0)', 'H(2,1)', 'H(2,2)']
for new in ['keep', 'add']:
    fig, axs = plt.subplots(len(configs), 2, figsize=(13, 3.6 * len(configs)))
    for row, cfg in enumerate(configs):
        sub = wide[wide['config'] == cfg]
        for col, (metric, title) in enumerate([('prec_val_rir_strict', 'Value RIR'), ('prec_cont_rir_strict', 'Continuation RIR')]):
            ax = axs[row][col]
            for _, r in sub.iterrows():
                okb, okn = bool(r['ok_lose']), bool(r[f'ok_{new}'])
                p0 = (r['Time_lose'], r[f'{metric}_lose']); p1 = (r[f'Time_{new}'], r[f'{metric}_{new}'])
                if okb and okn:
                    gain = p1[1] - p0[1]
                    ratio = p1[0] / p0[0] if p0[0] > 1e-12 else 1.0
                    if abs(gain) <= EPS and 0.9 <= ratio <= 1.1: continue   # same filter as the paper's plot
                    color, _ = get_tradeoff_color(gain, ratio)
                    ax.plot([p0[0], p1[0]], [p0[1], p1[1]], color=color, alpha=0.3, linewidth=3)
                    ax.scatter(*p0, color='gray', s=40, marker='x', alpha=0.6, zorder=2)
                    ax.scatter(*p1, color=color, s=45, marker='o', alpha=0.8, zorder=3)
                    if abs(gain) > EPS:
                        ax.annotate(r['bench'].split('/')[-2] + '/' + r['bench'].split('/')[-1], p1, fontsize=7,
                                    xytext=(4, 2), textcoords='offset points')
                elif okn:
                    ax.scatter(*p1, color='green', s=55, marker='o', alpha=0.9, zorder=3)
                    ax.annotate(r['bench'].split('/')[-1] + ' (lose T/O)', p1, fontsize=7, xytext=(4, 2), textcoords='offset points')
                elif okb:
                    ax.scatter(*p0, color='red', s=50, marker='x', alpha=0.8, zorder=2)
            ax.set_xscale('log'); ax.set_title(f'{cfg}: {title}')
            ax.set_xlabel('Analysis Time (s)'); ax.set_ylabel('RIR' if col == 0 else '')
    legend = [Line2D([0], [0], color='green', lw=5, label='more precise, faster'),
              Line2D([0], [0], color='blue', lw=5, label='more precise, slower'),
              Line2D([0], [0], color='red', lw=5, label='less precise'),
              Line2D([0], [0], color='gray', lw=5, label='same precision'),
              Line2D([0], [0], marker='x', color='gray', label='lose', linestyle='None', markersize=9),
              Line2D([0], [0], marker='o', color='gray', label=new, linestyle='None', markersize=9)]
    fig.legend(handles=legend, loc='upper center', ncol=6, bbox_to_anchor=(0.5, 1.0))
    plt.tight_layout(rect=(0, 0, 1, 0.985))
    plt.savefig(os.path.join(out, f'tradeoff_lose_to_{new}.png'), bbox_inches='tight', dpi=110)
    plt.close(fig)
print('wrote', out)
