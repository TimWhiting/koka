
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import seaborn as sns
import pandas as pd
import numpy as np
from plot_utils import (
    load_results_with_baselines, resolve_results_dir, get_benchmark_category,
    filter_common_benchmarks, get_large_benchmarks, shifted_geometric_mean
)

def plot_violin_rir(output_path="benchmarks/images/plot_violin_rir.png"):
    print("Loading results...")
    results = load_results_with_baselines(resolve_results_dir())
    df = pd.DataFrame(results)
    print(len(df), "total runs loaded.")

    configs = [
        {'variant': 'kcfa',   'd': 0, 'm': 1, 'label': '1-kCFA'},
        {'variant': 'kcfa',   'd': 0, 'm': 2, 'label': '2-kCFA'},
        {'variant': 'dmcfar', 'd': 1, 'm': 0, 'label': 'H(1,0)'},
        {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': 'H(1,1)'},
        {'variant': 'dmcfar', 'd': 1, 'm': 2, 'label': 'H(1,2)'},
    ]

    # Keep only non-trivial benchmarks (>300 0-CFA states) present in all configs
    # large = get_large_benchmarks(df, threshold=0)
    df_large = df # df[df['benchmarkName'].isin(large)]
    df_filtered = filter_common_benchmarks(df_large, configs, exclude_timeouts=True)
    print(f"Benchmarks in violin: {df_filtered['benchmarkName'].nunique()}")

    # Build long-form data for both metrics
    rows = []
    for cfg in configs:
        sub = df_filtered[
            (df_filtered['variant'] == cfg['variant']) &
            (df_filtered['d'] == cfg['d']) &
            (df_filtered['m'] == cfg['m'])
        ]
        for _, row in sub.iterrows():
            rows.append({
                'Configuration': cfg['label'],
                'RIR': row.get('prec_val_rir_strict', np.nan),
                'Metric': 'Value RIR',
            })
            rows.append({
                'Configuration': cfg['label'],
                'RIR': row.get('prec_cont_rir_strict', np.nan),
                'Metric': 'Continuation RIR',
            })

    df_long = pd.DataFrame(rows).dropna(subset=['RIR'])
    config_order = [c['label'] for c in configs]

    # Compute shifted geometric mean per (config, metric) for overlay
    def sgm(s):
        return shifted_geometric_mean(s)

    geomeans = (
        df_long.groupby(['Configuration', 'Metric'])['RIR']
        .apply(sgm)
        .reset_index(name='SGM')
    )

    # --- Plot ---
    sns.set_theme(style="whitegrid", font_scale=1.2)
    fig, axs = plt.subplots(1, 2, figsize=(12, 4), sharey=False)

    palette = sns.color_palette("Set2", len(configs))
    color_map = {c['label']: palette[i] for i, c in enumerate(configs)}

    for ax, metric in zip(axs, ['Value RIR', 'Continuation RIR']):
        data = df_long[df_long['Metric'] == metric]
        gm = geomeans[geomeans['Metric'] == metric].set_index('Configuration')

        # Violin
        sns.violinplot(
            data=data, x='Configuration', y='RIR',
            order=config_order, hue='Configuration',
            hue_order=config_order, palette=color_map,
            inner=None, cut=0, linewidth=0.8, legend=False, ax=ax
        )
        # Overlay shifted geomean as a white diamond
        for i, label in enumerate(config_order):
            if label in gm.index:
                val = gm.loc[label, 'SGM']
                ax.scatter(i, val, color='white', edgecolors='black',
                           s=60, zorder=5, marker='D', linewidths=1.2,
                           label='Shifted geomean' if i == 0 else '_nolegend_')

        ax.set_title(metric)
        ax.set_xlabel('')
        ax.set_ylabel('RIR' if ax is axs[0] else '')
        ax.yaxis.set_major_formatter(mticker.PercentFormatter(xmax=1, decimals=0))
        ax.set_ylim(-0.05, 1.05)

    # Shared legend
    from matplotlib.lines import Line2D
    handles = [Line2D([0], [0], marker='D', color='w', markerfacecolor='white',
                      markeredgecolor='black', markersize=8, label='Shifted geomean')]
    fig.legend(handles=handles, loc='upper left', bbox_to_anchor=(0.0, 1.0))

    # fig.suptitle('Per-benchmark RIR distribution (non-trivial benchmarks, common configurations)',
    #              fontsize=11, y=1.02)
    plt.tight_layout()
    plt.savefig(output_path, bbox_inches='tight', dpi=150)
    print(f"Saved {output_path}")
    plt.close()

if __name__ == '__main__':
    import os
    os.makedirs("benchmarks/images", exist_ok=True)
    plot_violin_rir("benchmarks/images/plot_violin_rir.png")
