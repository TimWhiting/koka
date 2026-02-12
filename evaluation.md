
# Evaluation {#evaluation}

We evaluate our analysis along two dimensions: precision and scalability.

## Research Questions {#research-questions}

**RQ1: Precision.** How precise is our analysis compared to baselines?

We evaluate precision using a microbenchmark suite targeting different patterns of continuation usage:

* **Zero-shot vs single-shot vs multi-shot**: Operations that use the continuation different numbers of times
* **Tail vs non-tail resumption**: Whether resume appears in tail position in the operation
* **Recursive operation calls**: Operations called recursively
* **Handler interaction**: Multiple handlers with operations called in different orders or within other operations

For each benchmark, we compare three analyses:

* **0-CFA**: Flow-insensitive baseline ($m=h=0$)
* **KCFA**: Threading timestamps through evaluation like a store
* **Our two-component analysis**: Using structured continuation timestamps ($m$) and meta-continuation timestamps ($h$)

All three analyses use a global store where addresses map to sets of values.
We vary parameters $m \in \{0,1,2\}$ and $h \in \{0,1,2\}$ to explore the precision-cost tradeoff.

We measure:

* **Final result precision**: For deterministic benchmarks, whether the analysis computes the exact concrete result
* **Store precision**: Ratio of singleton sets (precise addresses) in the final abstract store
* **Store growth**: Total abstract addresses and configurations explored

**RQ2: Scalability.** Does the analysis scale to larger programs?

We evaluate scalability on two benchmark suites:

**Koka standard examples** (50-100 LOC): ambient environment, state, iterators, parser combinators, unix simulator, search and nondeterminism for gametrees and knapsack problems.

**AI-generated libraries** (100-300 LOC): Larger examples showcasing realistic effect handler usage:

* Incremental build system with dependency tracking
* Lambda calculus interpreters (handlers for environment / errors)
* Probabilistic programming
* $\mu$Kanren relational programming
* Cooperative schedulers with and without channel communication

For each benchmark, we measure:

* **Analysis time**: Wall-clock time to fixpoint
* **State space size**: Total abstract configurations explored
* **Scalability**: How time and space grow with program size and parameter values
* **Precision-cost tradeoff**: Store precision (singleton ratio) vs. resource usage at each $(m,h)$ setting

## Running Example: Precision Gains {#precision-gains}

KCFA versus DMCFAR on samples/handlers/scoped/example5 (parsing)
- k=467
- d=4,m=22

[INCLUDE=tables/handlers/precision-comparison]

Returning to our running example, Figure [#precision-comparison] shows the precision differences across analyses. 
The 0-CFA baseline conflates all resumption paths, losing track of which values flow through which continuations.
Our analysis uses structured timestamps to track both ordinary function call contexts ($m$) and handler delimiter contexts ($h$), distinguishing each execution path and precisely determining which values flow through each resumption.
This demonstrates how the combination of continuation and meta-continuation structure is essential for precise multi-shot handler analysis.

## Evaluation Artifacts {#artifacts}

We are currently exploring different presentations of our evaluation data. Key questions include:
- How to effectively visualize precision differences across many benchmarks and parameter settings
- Whether to show detailed per-address precision or aggregate metrics
- How to present the three-way comparison (0-CFA vs. KCFA-style vs. two-component)


## Discussion {#discussion}

**Why not compare to AAC or CFA2?** Abstracting Abstract Control [@glaze_abstracting_2014] provides a direct analysis for $@shift/reset$, but does not extend to effect handlers (which use labeled delimiters and operations). More critically, AAC has super-exponential complexity even on small programs, making direct comparison infeasible. CFA2 [@vardoulakis_pushdown_2011-1] could analyze handlers after CPS translation, but the translation loses precision and expresses results in CPS terms rather than source constructs, and also require continuations to be allocated in environments and thus limit their allocation strategy. Our big-step approach provides the first practical direct analysis for effect handlers.

**Parameter tuning in practice.** While we evaluate fixed $(m,h)$ pairs, a production implementation could use adaptive strategies for extending timestamps to fit patterns that occur frequently with delimited control. 
Multi-prompt is one such pattern that we handle well, but is not necessary for every implementation of effect handlers.

**Rebinding tradeoff.** Section [#rebinding] presents rebinding as essential for tractability, following Might et al.'s approach for $m$-CFA. 
However, rebinding loses precision when free variables originate from different contexts. 
Future work could explore selective rebinding that preserves key distinctions.

**Integration with Koka compiler.** Our evaluation measures analysis precision and cost in isolation, but the ultimate goal is optimization. 
Section [#introduction] motivated CFA for handlers with examples of code duplication and evidence vector inefficiency. 
Quantifying these optimization opportunities requires:
- Identifying optimization patterns enabled by precise continuation flow
- Measuring code size and runtime improvements after optimization
- Demonstrating that our precision gains translate to performance wins

This represents promising future work beyond the current evaluation's scope.

## Threats to Validity {#threats}

*Implementation-formalization gap.* 
Our implementation is in Haskell on a slightly more complex non-ANF representation, while the formalism uses mathematical notation and ANF.
While the implementation differs on (e.g. number and type of frames), it follows the timestamping approach exactly. We tested a subset of the benchmarks on a second implementation using a simplified ANF language to validate the correctness of the implementation.
The handling of local state and primitive lattice operations are also bespoke, but applied the same across the different analyses we compared.

*AI-generated code bias.* Some of our larger benchmarks are AI-generated, which may not reflect human coding patterns or real-world usage of effects (but does reflect the means by which many programs using these new language features will likely be programmed). 
We partially addressed this by:
- Including hand-written Koka standard library examples
- Explicitly asking for unique and different ways of utilizing effect handlers
- Manually reviewing generated code to ensure it compiled, was logically correct, and had examples that showcased / stressed the library.

*Parameter selection.* Our choice of $m, h \in \{0,1,2\}$ is often sufficient to achieve concrete precision on our smallest examples. 
Programs with deeper nesting or more complex control flow might benefit from different choices of parameters, but we lack a large corpus of such programs.
Future work should evaluate parameter sensitivity on more diverse codebases with deeper nesting structures.

*Precision metrics.* Points-to set size is a common precision metric, but it may not directly correlate with optimization potential. 
A more imprecise analysis might still enable the same optimizations if it preserves key distinctions. 
We focus on set sizes because they are objective and interpretable, but acknowledge that downstream optimization impact is the ultimate measure.

*Baseline fairness.* 
We compare against 0-CFA ($m=h=0$) and KCFA to isolate the contribution of our structured two-component timestamp design.
KCFA threads timestamps through evaluation like a store, providing some context sensitivity, but lacks the structured stacks that enable our continuation and meta-continuation distinction.
This comparison demonstrates that handlers benefit from tracking both types of context with appropriate structure.
However, stronger baselines would provide additional perspective:
- CFA2 [@vardoulakis_pushdown_2011-1] after CPS translation (though results would be in CPS terms and as shown by [@glaze_abstracting_2014] continuation precision would be limited by value address precision)
- AAC [@glaze_abstracting_2014] for $@shift/reset$ (though it lacks handler support and has exponential complexity)
- Our definitional interpreter with alternative allocation strategies

We omit these comparisons due to implementation effort and fundamental incompatibilities (different source languages, tractability concerns), but acknowledge this limitation in our evaluation.
