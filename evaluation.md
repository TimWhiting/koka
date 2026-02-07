
**RQ1: Precision.** How precise is our analysis compared to baselines?

We evaluate precision using a microbenchmark suite targeting different patterns of continuation usage:
- **Zero-shot vs single-shot vs multi-shot**: Operations that are never resumed (e.g., exceptions) vs. resumed once vs. resumed multiple times
- **Tail vs non-tail resumption**: Whether resume appears in tail position
- **Nested operations**: Operations called recursively or from within other operations
- **Handler interaction**: Multiple handlers, operations called in different orders

For each benchmark, we compare three analyses:
- **0-CFA**: Flow-insensitive baseline ($m=h=0$)
- **KCFA**: Threading timestamps through evaluation like a store
- **Our two-component analysis**: Using structured continuation timestamps ($m$) and meta-continuation timestamps ($h$)

All three analyses use a global store where addresses map to sets of values.
We vary parameters $m \in \{0,1,2\}$ and $h \in \{0,1,2\}$ to explore the precision-cost tradeoff.

We measure:
- **Final result precision**: For deterministic benchmarks, whether the analysis computes the exact concrete result
- **Store precision**: Ratio of singleton sets (precise addresses) in the final abstract store
- **Store growth**: Total abstract addresses and configurations explored

**RQ2: Scalability.** Does the analysis scale to larger programs?

We evaluate scalability on two benchmark suites:
- **Koka standard examples** (50-100 LOC): ambient environment, state, iterators, parser combinators, unix simulator, search and nondeterminism for gametrees and knapsack problems.
- **AI-generated libraries** (100-300 LOC): Larger examples showcasing realistic effect handler usage:
  - Incremental build system with dependency tracking
  - Lambda calculus interpreters (handlers for environment / errors)
  - Probabilistic programming
  - $\mu$Kanren relational programming
  - Cooperative schedulers with and without channel communication

For each benchmark, we measure:
- **Analysis time**: Wall-clock time to fixpoint
- **State space size**: Total abstract configurations explored
- **Scalability**: How time and space grow with program size and parameter values
- **Precision-cost tradeoff**: Store precision (singleton ratio) vs. resource usage at each $(m,h)$ setting
