
import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
import numpy as np
from plot_utils import load_results_with_baselines, get_benchmark_category, filter_common_benchmarks

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
        {'variant': 'dmcfar', 'd': 1, 'm': 0, 'label': '1,0-HMCFAR'},
        {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': '1,1-HMCFAR'},
        {'variant': 'dmcfar', 'd': 1, 'm': 2, 'label': '1,2-HMCFAR'},
    ]
    
    config_labels = [c['label'] for c in configs]
    
    # Filter for benchmarks present in ALL these configs
    # (To ensure fair comparison)
    df_filtered = filter_common_benchmarks(df, configs)
    print(f"Common benchmarks: {len(df_filtered['benchmarkName'].unique())}")
    
    # Metrics to plot
    metrics = [
        ('prec_val_rir_strict', 'Value RIR (Shifted Geomean)', 'plot_categorical_val_rir.png'),
        ('prec_cont_rir_strict', 'Continuation RIR (Shifted Geomean)', 'plot_categorical_cont_rir.png')
    ]
    
    for col, title, filename in metrics:
        print(f"Processing {title}...")
        
        plot_data = []
        
        # Iterate over configs
        for config in configs:
            # Get subset for this config
            subset = df_filtered[
                (df_filtered['variant'] == config['variant']) & 
                (df_filtered['d'] == config['d']) & 
                (df_filtered['m'] == config['m'])
            ]
            
            # 1. Per Category
            cats = subset.groupby('Category')[col].apply(shifted_geomean).reset_index()
            for _, row in cats.iterrows():
                plot_data.append({
                    'Category': row['Category'],
                    'Configuration': config['label'],
                    'Value': row[col]
                })
                
            # 2. All Categories (Total)
            all_val = shifted_geomean(subset[col])
            plot_data.append({
                'Category': 'All',
                'Configuration': config['label'],
                'Value': all_val
            })
            
        df_plot = pd.DataFrame(plot_data)
        
        # Define Category Order
        # Put "All" last or first? Usually last.
        # Order: Micro, Koka-Samples, Rosetta, Koka-Gen, All
        cat_order = ['Micro-Suite', 'Koka-Samples', 'Rosetta', 'Koka-Gen', 'All']
        
        # Plot
        plt.figure(figsize=(12, 6))
        sns.set_theme(style="whitegrid")
        
        # Bar chart
        sns.barplot(
            data=df_plot,
            x='Category',
            y='Value',
            hue='Configuration',
            order=cat_order,
            hue_order=config_labels,
            palette='viridis' 
        )
        
        plt.title(title)
        plt.ylabel("Strict RIR (Improvement over 0-CFA)")
        plt.ylim(0, df_plot['Value'].max() * 1.1)
        
        # Annotate
        # (Optional, might be too crowded)
        
        outfile = f"benchmarks/new_analysis/{filename}"
        plt.savefig(outfile)
        print(f"Saved {outfile}")
        plt.close()

if __name__ == "__main__":
    plot_categorical()
