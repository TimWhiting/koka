stack run koka -- -l analysis/aac/benchmarks.kk --dmcfa --da=2 --ma=6 2> dmcfar.kk
stack run koka -- -l analysis/aac/benchmarks.kk --analyze --da=2 --ma=6 2> dmcfa.kk
stack run koka -- -l analysis/aac/benchmarks.kk --kcfa --ma=6 2> kcfa.kk
