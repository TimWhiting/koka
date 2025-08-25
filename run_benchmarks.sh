stack run koka -- -l analysis/benchmarks/benchmarks.kk --dmcfa --sweep --da=2 --ma=6 2> dmcfar.kk
stack run koka -- -l analysis/benchmarks/benchmarks.kk --analyze --sweep --da=2 --ma=6 2> dmcfa.kk
stack run koka -- -l analysis/benchmarks/benchmarks.kk --kcfa --sweep --da=0 --ma=6 2> kcfa.kk
