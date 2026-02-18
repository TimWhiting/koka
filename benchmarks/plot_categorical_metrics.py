
import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, get_benchmark_category, filter_common_benchmarks, get_large_benchmarks

def shifted_geomean(series):
    """
    Calculates shifted geometric mean: exp(mean(log(1+x))) - 1.
    """
    vals = pd.to_numeric(series, errors='coerce') + 1.0
    vals = vals[vals > 0]
    if len(vals) == 0: return 0.0
    return np.exp(np.mean(np.log(vals))) - 1.0

def plot_categorical():
    print("Loading results...")
    results = load_results_with_baselines("benchmarks/results-cached")
    df = pd.DataFrame(results)
    
    # Tag Categories
    df['Category'] = df['benchmarkName'].apply(get_benchmark_category)
    
    # Rename categories for plotting if needed
    # (Micro, Handlers, Rosetta, Koka-Gen) are already good labels
    
    # Define configurations of interest
    configs = [
        {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': '1-kCFA'},
        {'variant': 'kcfa', 'd': 0, 'm': 2, 'label': '2-kCFA'},
        {'variant': 'dmcfar', 'd': 1, 'm': 0, 'label': 'H(1,0)'},
        {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': 'H(1,1)'},
        {'variant': 'dmcfar', 'd': 1, 'm': 2, 'label': 'H(1,2)'},
    ]
    
    config_labels = [c['label'] for c in configs]
    
    # Filter for benchmarks present in ALL these configs
    # (To ensure fair comparison)
    df_filtered = filter_common_benchmarks(df, configs, exclude_timeouts=True)
    print(f"Common benchmarks: {len(df_filtered['benchmarkName'].unique())}")

    # For the "All" aggregate, apply >300 0-CFA states filter
    large_benchmarks = get_large_benchmarks(df, threshold=300)
    df_filtered_large = df_filtered[df_filtered['benchmarkName'].isin(large_benchmarks)]
    print(f"Large benchmarks for 'All' aggregate (States > 300): {len(df_filtered_large['benchmarkName'].unique())}")
    
    # Metrics to plot
    metrics = [
        ('prec_val_rir_strict', 'Value RIR (Shifted Geomean)', 'plot_categorical_val_rir.png'),
        ('prec_cont_rir_strict', 'Continuation RIR (Shifted Geomean)', 'plot_categorical_cont_rir.png')
    ]
    
    # Create side-by-side subplots
    fig, axs = plt.subplots(1, 2, figsize=(14, 4), sharey=True)
    sns.set_theme(style="whitegrid", font_scale=1.4)
    
    # Pre-calculate data for both plots
    metrics = [
        ('prec_val_rir_strict', 'Value RIR', axs[0]),
        ('prec_cont_rir_strict', 'Continuation RIR', axs[1])
    ]
    
    cat_order = ['Micro-Suite', 'Koka-Samples', 'Koka-Gen', 'All (>300 states)']

    for col, title, ax in metrics:
        print(f"Processing {title}...")
        plot_data = []
        
        for config in configs:
            # 1. Calculate Geomean from FILTERED data (Common Intersection)
            subset = df_filtered[
                (df_filtered['variant'] == config['variant']) & 
                (df_filtered['d'] == config['d']) & 
                (df_filtered['m'] == config['m'])
            ]
            
            # 2. Calculate Timeouts from FULL data (All runs for this config)
            # We filter for benchmarks in this category + config + status='T/O'
            full_subset = df[
                (df['variant'] == config['variant']) & 
                (df['d'] == config['d']) & 
                (df['m'] == config['m'])
            ]
            
            # --- Per Category ---
            cats = subset.groupby('Category')[col].apply(shifted_geomean).reset_index()
            
            # timeouts per category
            # We need to ensure we count timeouts for the same categories
            # full_subset might have categories not in cats if subset is empty, but generally cats is comprehensive
            
            for _, row in cats.iterrows():
                cat = row['Category']
                # Count T/O for this category in full_subset
                to_count = len(full_subset[ (full_subset['Category'] == cat) & (full_subset['status'] == 'T/O') ])
                
                plot_data.append({
                    'Category': cat, 
                    'Configuration': config['label'], 
                    'Value': row[col],
                    'TimeoutCount': to_count
                })
                
            # --- All (>300 states) ---
            # Use df_filtered_large so the "All" aggregate only includes non-trivial benchmarks
            subset_large = df_filtered_large[
                (df_filtered_large['variant'] == config['variant']) &
                (df_filtered_large['d'] == config['d']) &
                (df_filtered_large['m'] == config['m'])
            ]
            all_val = shifted_geomean(subset_large[col])
            # Timeouts among large benchmarks for this config
            full_large = full_subset[full_subset['benchmarkName'].isin(large_benchmarks)]
            total_to = len(full_large[full_large['status'] == 'T/O'])

            plot_data.append({
                'Category': 'All (>300 states)',
                'Configuration': config['label'],
                'Value': all_val,
                'TimeoutCount': total_to
            })
            
        df_plot = pd.DataFrame(plot_data)
        
        # Draw Bars
        bars = sns.barplot(
            data=df_plot,
            x='Category',
            y='Value',
            hue='Configuration',
            order=cat_order,
            hue_order=config_labels,
            palette='viridis',
            edgecolor='black',
            ax=ax
        )
        
        # Annotate Timeouts
        # Iterate over bars and add text
        # sns.barplot returns axes, we need to iterate patches
        # Warning: Patches order depends on hue/x order. 
        # Safer to iterate explicit bars if we can map them back, but seaborn patches are just rects.
        # Order: First hue (all x), Second hue (all x), etc.
        
        # We need a map from (Category, Config) -> TimeoutCount
        to_map = {}
        for _, row in df_plot.iterrows():
            to_map[(row['Category'], row['Configuration'])] = row['TimeoutCount']
            
        # Iterate patches
        # Seaborn plots bars by Hue group.
        # Hue 0: Cat 0, Cat 1, Cat 2...
        # Hue 1: Cat 0, Cat 1, Cat 2...
        
        for i, patch in enumerate(ax.patches):
            # Calculate indices
            # num_x = len(cat_order)
            # hue_idx = i // num_x
            # cat_idx = i % num_x
            
            # Wait, seaborn might plot NaNs if missing? 
            # Our df_plot is complete (we iterated all configs/categories).
            # But let's verify patch count.
            
            # Config index
            hue_idx = i // len(cat_order)
            if hue_idx >= len(config_labels): break # Safety
            
            config_label = config_labels[hue_idx]
            
            # Cat index
            cat_idx = i % len(cat_order)
            cat_label = cat_order[cat_idx]
            
            # Get count
            count = to_map.get((cat_label, config_label), 0)
            
            if count > 0:
                # Add Annotation
                # Position: Above bar? 
                # If bar is very short, it might overlap usage.
                # Let's put it just above the bar.
                height = patch.get_height()
                x = patch.get_x() + patch.get_width() / 2
                y = height
                
                # Offset slightly
                ax.text(x, y, f"{count}", 
                        ha='center', va='bottom', fontsize=10, color='red', fontweight='bold', rotation=0)

        ax.set_title(title)
        ax.set_ylabel("RIR" if ax == axs[0] else "")
        ax.set_xlabel("")
        ax.set_ylim(0, df_plot['Value'].max() * 1.15) # Increase headroom for annotations
        
        # Grab legend from the first plot before removing
        if ax == axs[0]:
            handles, labels = ax.get_legend_handles_labels()
        
        if ax.get_legend():
            ax.get_legend().remove()

    # Shared Legend
    if handles:
        fig.legend(handles, labels, bbox_to_anchor=(1.02, 0.9), loc='upper left', borderaxespad=0.)

    plt.tight_layout(pad=0.2)
    
    outfile = "benchmarks/new_analysis/plot_categorical_combined.png"
    plt.savefig(outfile, bbox_inches='tight')
    print(f"Saved {outfile}")

if __name__ == "__main__":
    plot_categorical()
