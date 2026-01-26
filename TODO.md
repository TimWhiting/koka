- [ ] See if the new results show only decreasing in precision for d=0 if so, keep them, and update the formalism (jump-anywhere regressed slightly, but others didn't timeout - is that because the timeout was changed since they were last run?)
- [ ] Figure out why timeout on ukanren/some build on small m
- [ ] Run for longer (timeouts)
- [ ] Use results to determine stack invariants (order of handlers) - would need extra information in the analysis itself - or maybe just graph edges between eval states -- do this post-processing by checking two nested eval states with different h=?
- [ ] Figure out how to best visualize results
- [ ] Redo analysis of LOC visualization
- [ ] Maybe focus the results on DMCFA even though it has overhead
- [ ] Figure out why some benchmarks timeout on (d,m)=0. Really that shouldn't happen, it should just be imprecise?


DONT WORK ON KCFA until we determine it is useful...
- [ ] Figure out why KCFA doesn't work on state handler / nondet-context, nondet-nested, most of nested-nondet, monads-writer, jump-anywhere, nim
