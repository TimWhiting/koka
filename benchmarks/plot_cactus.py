
import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
import numpy as np
import os
from plot_utils import load_results_with_baselines

def plot_cactus():
    print("Loading results...")
    # Load all results
    results = load_results_with_baselines("benchmarks/results-cached")
    df = pd.DataFrame(results)
    
    output_dir = "benchmarks/new_analysis"
    os.makedirs(output_dir, exist_ok=True)
    
    # 1. Scalability: Cactus Plot
    # X-axis: Number of benches solved <= T
    # Y-axis: Time T
    plt.figure(figsize=(7, 3.5))
    sns.set_theme(style="whitegrid", context="paper", font_scale=1.5)
    
    # Select key configurations to plot
    key_configs = [
        {'variant': 'kcfa', 'd': 0, 'm': 1, 'label': 'k-CFA k=1'},
        {'variant': 'kcfa', 'd': 0, 'm': 2, 'label': 'k-CFA k=2'},
        {'variant': 'dmcfar', 'd': 1, 'm': 1, 'label': 'DMCFAR (1,1)'},
        # {'variant': 'dmcfar', 'd': 1, 'm': 2, 'label': 'DMCFAR (1,2)'}, # Removed per user request
        {'variant': 'dmcfar', 'd': 2, 'm': 2, 'label': 'DMCFAR (2,2)'},
        # {'variant': 'dmcfae', 'd': 1, 'm': 1, 'label': 'DMCFAE (1,1)'}, # Removed per user request
    ]
    
    # Flatten config fields for filtering
    df['d'] = pd.to_numeric(df['d'], errors='coerce')
    df['m'] = pd.to_numeric(df['m'], errors='coerce')
    
    for config in key_configs:
        variant = config['variant']
        d_val = config['d']
        m_val = config['m']
        label = config['label']
        
        # Filter data
        if variant == 'kcfa':
            subset = df[(df['variant'] == variant) & (df['m'] == m_val)]
        else:
            subset = df[(df['variant'] == variant) & (df['m'] == m_val) & (df['d'] == d_val)]
            
        if subset.empty:
            print(f"Skipping {label}: No data found.")
            continue
            
        # Get times for solved instances
        # Time column might be 'analysisTime' or 'Time'
        # plot_utils uses 'Time' which comes from 'analysisTime'
        # Check standard key
        
        # Filter timeouts
        # 'isTimeout' might be boolean or string
        # plot_utils standardizes this usually?
        # Let's check safe access
        
        subset_solved = subset[subset['isTimeout'] == False].copy()
        
        # Extract Time
        # The 'Time' column is usually standardized by load_results... or we compute it
        if 'Time' not in subset_solved.columns:
            # Fallback to computing it
            subset_solved['Time'] = subset_solved['analysisTimes'].apply(lambda x: np.mean(x) if isinstance(x, list) else x)
            
        times = sorted([float(t) for t in subset_solved['Time'] if pd.notna(t)])
        
        # X-axis is just 1..N
        x_axis = range(1, len(times) + 1)
        
        if times:
            # Flip axes: X=Time, Y=Count
            plt.plot(times, x_axis, label=f"{label} ({len(times)} solved)", linewidth=2, marker='o', markersize=4, alpha=0.8)
            
    plt.xscale('log')
    plt.xlabel('Analysis Time (s) [Log Scale]')
    plt.ylabel('Number of Benchmarks Solved')
    plt.title('Scalability (Cactus Plot)')
    plt.legend(bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0.)
    plt.grid(True, which="both", ls="-", alpha=0.2)
    plt.tight_layout(pad=0.2)
    
    outfile = os.path.join(output_dir, 'cactus_plot.png')
    plt.savefig(outfile)
    print(f"Saved {outfile}")
    plt.close()

if __name__ == "__main__":
    plot_cactus()
