module analysis/graph-data

// Represents a function or module in the dependency graph
pub struct node
  name : string
  loc : int           // Local Source Lines of Code for this specific function/module
  deps : list<string> // Fully qualified names of dependencies

// A graph is simply a list of nodes
pub alias graph = list<node>

pub val dependency-graph : graph = [
  // basic.kk functions
  Node("basic/analyze-basic-exception", 4, ["std/core/console/trace", "basic/ex1"]),
  Node("basic/analyze-basic-resume", 4, ["std/core/console/trace", "basic/ex1"]),
  Node("basic/analyze-basic-resume-context", 4, ["std/core/console/trace", "basic/ex1"]),
  Node("basic/analyze-basic-resume-op", 4, ["std/core/console/trace", "basic/ex1"]),
  Node("basic/analyze-basic-resume-op-context", 4, ["std/core/console/trace", "basic/ex1"]),
  
  // Effect definition (1 base + 2 per operation)
  Node("basic/ex1", 3, []),
  
  // complex-flow.kk helper functions
  Node("complex-flow/normal-inc", 2, ["std/core/int/(+)"]),
  Node("complex-flow/normal-double", 2, ["std/core/int/(*)"]),
  Node("complex-flow/tail-ask", 2, ["complex-flow/ask"]),
  Node("complex-flow/fib-eff", 3, ["complex-flow/ask", "std/core/int/(<=)", "std/core/int/(-)", "std/core/int/(+)"]),
  Node("complex-flow/apply-cont", 2, []),
  
  // complex-flow.kk analyze functions
  Node("complex-flow/analyze-complex-tail-call", 4, ["std/core/console/trace", "complex-flow/ask", "complex-flow/normal-inc"]),
  Node("complex-flow/analyze-complex-non-tail-call", 6, ["std/core/console/trace", "complex-flow/ask", "complex-flow/normal-inc", "std/core/int/(+)"]),
  Node("complex-flow/analyze-complex-tail-effect", 4, ["std/core/console/trace", "complex-flow/ask", "complex-flow/tail-ask"]),
  Node("complex-flow/analyze-complex-nested-interleave", 9, ["std/core/console/trace", "complex-flow/ask", "complex-flow/tell", "std/core/int/(+)"]),
  Node("complex-flow/analyze-complex-recursive", 4, ["std/core/console/trace", "complex-flow/ask", "complex-flow/fib-eff"]),
  Node("complex-flow/analyze-complex-layers", 19, ["std/core/console/trace", "complex-flow/flip", "complex-flow/fail", "std/core/int/(+)"]),
  Node("complex-flow/analyze-complex-resume-func", 4, ["std/core/console/trace", "complex-flow/ask", "complex-flow/apply-cont", "std/core/int/(+)"]),
  
  // complex-flow.kk effects
  Node("complex-flow/ask", 3, []),
  Node("complex-flow/tell", 3, []),
  Node("complex-flow/flip", 3, []),
  Node("complex-flow/fail", 3, []),
  
  // multi-effect.kk analyze functions
  Node("multi-effect/analyze-multi-simple", 6, ["std/core/console/trace", "multi-effect/ex51", "multi-effect/ex52", "multi-effect/ex53", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("multi-effect/analyze-multi-inner-first", 6, ["std/core/console/trace", "multi-effect/ex51", "multi-effect/ex52", "multi-effect/ex53", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("multi-effect/analyze-multi-two-outer", 6, ["std/core/console/trace", "multi-effect/ex51", "multi-effect/ex52", "multi-effect/ex53", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  
  // multi-effect.kk effects
  Node("multi-effect/ex51", 3, []),
  Node("multi-effect/ex52", 3, []),
  Node("multi-effect/ex53", 3, []),
  
  // nested.kk analyze functions
  Node("nested/analyze-nested-simple", 5, ["std/core/console/trace", "nested/ex31", "nested/ex32"]),
  Node("nested/analyze-nested-simple-two", 5, ["std/core/console/trace", "nested/ex31", "nested/ex32"]),
  Node("nested/analyze-nested-op-after", 5, ["std/core/console/trace", "nested/ex31", "nested/ex33", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nested/analyze-nested-op-before", 5, ["std/core/console/trace", "nested/ex31", "nested/ex33", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nested/analyze-nested-inner-first", 5, ["std/core/console/trace", "nested/ex31", "nested/ex33", "std/core/int/(+)", "std/core/types/fst"]),
  Node("nested/analyze-nested-outer-first", 5, ["std/core/console/trace", "nested/ex31", "nested/ex33", "std/core/int/(+)", "std/core/types/fst"]),
  Node("nested/analyze-nested-tail-simple", 5, ["std/core/console/trace", "nested/ex41", "nested/ex42", "std/core/int/(+)"]),
  Node("nested/analyze-nested-tail-op-after", 5, ["std/core/console/trace", "nested/ex41", "nested/ex43", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nested/analyze-nested-tail-op-before", 5, ["std/core/console/trace", "nested/ex41", "nested/ex43", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nested/analyze-nested-tail-inner-first", 5, ["std/core/console/trace", "nested/ex41", "nested/ex43", "std/core/int/(+)", "std/core/types/fst"]),
  Node("nested/analyze-nested-tail-outer-first", 5, ["std/core/console/trace", "nested/ex41", "nested/ex43", "std/core/int/(+)", "std/core/types/fst"]),
  Node("nested/analyze-nested-three-levels", 6, ["std/core/console/trace", "nested/ex31", "nested/ex32", "nested/ex33", "std/core/int/(+)", "std/core/int/(*)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nested/analyze-nested-absorb", 6, ["std/core/console/trace", "nested/ex31", "nested/ex32", "nested/ex33", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  
  // nested.kk effects
  Node("nested/ex31", 3, []),
  Node("nested/ex32", 3, []),
  Node("nested/ex33", 3, []),
  Node("nested/ex41", 3, []),
  Node("nested/ex42", 3, []),
  Node("nested/ex43", 3, []),
  
  // nondet.kk analyze functions
  Node("nondet/analyze-nondet-simple", 6, ["std/core/console/trace", "nondet/ex2", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nondet/analyze-nondet-context", 6, ["std/core/console/trace", "nondet/ex2", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nondet/analyze-nondet-nested", 6, ["std/core/console/trace", "nondet/ex2", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nondet/analyze-nondet-discard", 8, ["std/core/console/trace", "nondet/ex2", "std/core/types/fst", "std/core/types/snd"]),
  
  // nondet.kk effects
  Node("nondet/ex2", 3, []),
  
  // nested-nondet.kk analyze functions
  Node("nested-nondet/analyze-nondet-nested-simple", 11, ["std/core/console/trace", "nested-nondet/choice1", "nested-nondet/choice2", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nested-nondet/analyze-nondet-nested-tail", 9, ["std/core/console/trace", "nested-nondet/choice1", "nested-nondet/tail1", "std/core/int/(*)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nested-nondet/analyze-nondet-three-levels", 16, ["std/core/console/trace", "nested-nondet/choice1", "nested-nondet/choice2", "nested-nondet/choice3", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nested-nondet/analyze-nondet-alternating", 13, ["std/core/console/trace", "nested-nondet/choice1", "nested-nondet/choice2", "nested-nondet/tail1", "std/core/int/(+)", "std/core/int/(*)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nested-nondet/analyze-nondet-both-contexts", 14, ["std/core/console/trace", "nested-nondet/choice1", "nested-nondet/choice2", "std/core/int/(+)", "std/core/int/(*)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nested-nondet/analyze-nondet-guarded", 10, ["std/core/console/trace", "nested-nondet/choice1", "std/core/int/(>)", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nested-nondet/analyze-nondet-with-failure", 9, ["std/core/console/trace", "nested-nondet/choice1", "nested-nondet/fail", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  Node("nested-nondet/analyze-nondet-variable-branches", 17, ["std/core/console/trace", "nested-nondet/choice1", "std/core/int/(==)", "std/core/int/(+)", "std/core/types/fst", "std/core/types/snd"]),
  
  // nested-nondet.kk effects
  Node("nested-nondet/choice1", 3, []),
  Node("nested-nondet/choice2", 3, []),
  Node("nested-nondet/choice3", 3, []),
  Node("nested-nondet/tail1", 3, []),
  Node("nested-nondet/fail", 3, []),
  
  // recursion.kk helper functions
  Node("recursion/iterxx", 6, ["recursion/it", "std/core/int/(==)", "std/core/int/(-)"]),
  Node("recursion/iterx", 5, ["recursion/it", "std/core/int/(==)", "std/core/int/(-)"]),
  Node("recursion/iter", 5, ["recursion/it", "std/core/int/(==)", "std/core/int/(-)"]),
  
  // recursion.kk analyze functions
  Node("recursion/analyze-iter-sum", 4, ["std/core/console/trace", "recursion/it", "recursion/iter", "std/core/int/(+)"]),
  Node("recursion/analyze-iter-sum-handler", 6, ["std/core/console/trace", "recursion/it", "recursion/iter", "std/core/int/(+)"]),
  Node("recursion/analyze-iter-sum-two", 4, ["std/core/console/trace", "recursion/it", "recursion/iter", "std/core/int/(+)"]),
  Node("recursion/analyze-iter-sum-b", 4, ["std/core/console/trace", "recursion/it", "recursion/iter", "std/core/int/(+)"]),
  Node("recursion/analyze-iter-sum-two-b", 4, ["std/core/console/trace", "recursion/it", "recursion/iter", "std/core/int/(+)"]),
  Node("recursion/analyze-iter-sum-c", 4, ["std/core/console/trace", "recursion/it", "recursion/iterxx", "std/core/int/(+)"]),
  Node("recursion/analyze-iter-sum-two-c", 4, ["std/core/console/trace", "recursion/it", "recursion/iterxx", "std/core/int/(+)"]),
  Node("recursion/analyze-iter-sum-d", 4, ["std/core/console/trace", "recursion/it", "recursion/iterxx", "std/core/int/(+)"]),
  Node("recursion/analyze-iter-sum-two-d", 4, ["std/core/console/trace", "recursion/it", "recursion/iterxx", "std/core/int/(+)"]),
  
  // recursion.kk effects
  Node("recursion/it", 3, []),
  
  // state-handler.kk helper functions
  Node("state-handler/countdown", 5, ["state-handler/get", "state-handler/set", "std/core/int/(==)", "std/core/int/(-)"]),
  
  // state-handler.kk analyze functions
  Node("state-handler/analyze-state-countdown", 8, ["std/core/console/trace", "state-handler/get", "state-handler/set", "state-handler/countdown"]),
  
  // state-handler.kk effects
  Node("state-handler/get", 3, []),
  Node("state-handler/set", 3, []),
  
  // handlers/ambient.kk helper functions
  Node("handlers/ambient/f", 4, ["handlers/ambient/width", "std/core/int/(+)"]),
  
  // handlers/ambient.kk analyze functions
  Node("handlers/ambient/analyze-example0", 3, ["handlers/ambient/width", "handlers/ambient/f"]),
  
  // handlers/ambient.kk effects
  Node("handlers/ambient/width", 1, []),
  
  // interp.kk types
  Node("interp/term", 5, []),
  Node("interp/value", 2, []),
  
  // interp.kk helper functions
  Node("interp/run-env", 8, ["interp/env", "interp/lookup", "interp/snapshot", "std/core/list/find", "std/core/types/fst", "std/core/int/(==)", "std/core/types/maybe", "std/core/exn/throw", "std/core/string/(++)"]),
  Node("interp/run-safe", 5, ["interp/value", "std/core/string/(++)", "interp/show-value"]),
  Node("interp/show-value", 4, ["interp/value", "std/core/int/show"]),
  Node("interp/eval", 20, ["interp/term", "interp/value", "interp/env", "interp/lookup", "interp/snapshot", "std/core/int/(+)", "std/core/exn/throw", "std/core/string/(++)", "std/core/types/list", "interp/run-env"]),
  
  // interp.kk analyze functions
  Node("interp/analyze-interp", 11, ["interp/term", "interp/run-safe", "interp/run-env", "interp/eval"]),
  
  // interp.kk effects
  Node("interp/env", 5, []),
  Node("interp/lookup", 3, []),
  Node("interp/snapshot", 3, []),
  
  // interp2.kk types
  Node("interp2/surface", 6, []),
  Node("interp2/term", 5, []),
  Node("interp2/value", 2, []),
  
  // interp2.kk helper functions
  Node("interp2/desugar", 12, ["interp2/surface", "interp2/term", "std/core/list/map"]),
  Node("interp2/run-env", 8, ["interp2/env", "interp2/lookup", "interp2/snapshot", "std/core/list/find", "std/core/types/fst", "std/core/int/(==)", "std/core/types/maybe", "std/core/exn/throw", "std/core/string/(++)"]),
  Node("interp2/run-safe", 5, ["std/core/exn/throw-exn"]),
  Node("interp2/show", 4, ["interp2/value", "std/core/int/show"]),
  Node("interp2/eval-prim", 14, ["interp2/value", "std/core/int/(+)", "std/core/int/(-)", "std/core/int/(*)", "std/core/list/foldl", "std/core/exn/throw", "std/core/string/(++)"]),
  Node("interp2/eval", 21, ["interp2/term", "interp2/value", "interp2/env", "interp2/lookup", "interp2/snapshot", "std/core/list/map", "interp2/eval-prim", "std/core/list/length", "std/core/int/show", "std/core/string/(++)", "std/core/exn/throw", "std/core/list/zip", "std/core/list/(++)", "interp2/run-env"]),
  Node("interp2/interpret", 5, ["interp2/surface", "interp2/desugar", "interp2/run-env", "interp2/eval", "std/core/string/(++)", "interp2/show"]),
  
  // interp2.kk analyze functions
  Node("interp2/analyze-t1", 5, ["interp2/surface", "interp2/run-safe", "std/core/types/id", "interp2/interpret"]),
  Node("interp2/analyze-t2", 6, ["interp2/surface", "interp2/run-safe", "std/core/types/id", "interp2/interpret"]),
  Node("interp2/analyze-t3", 7, ["interp2/surface", "interp2/run-safe", "std/core/types/id", "interp2/interpret"]),
  Node("interp2/analyze-t4", 3, ["interp2/surface", "interp2/run-safe", "std/core/types/id", "interp2/interpret"]),
  Node("interp2/analyze-err1", 3, ["interp2/surface", "interp2/run-safe", "std/core/types/id", "interp2/interpret"]),
  Node("interp2/analyze-err2", 6, ["interp2/surface", "interp2/run-safe", "std/core/types/id", "interp2/interpret"]),
  Node("interp2/analyze-err3", 6, ["interp2/surface", "interp2/run-safe", "std/core/types/id", "interp2/interpret"]),
  Node("interp2/analyze-err4", 6, ["interp2/surface", "interp2/run-safe", "std/core/types/id", "interp2/interpret"]),
  Node("interp2/analyze-err5", 3, ["interp2/surface", "interp2/run-safe", "std/core/types/id", "interp2/interpret"]),
  
  // interp2.kk effects
  Node("interp2/env", 5, []),
  Node("interp2/lookup", 3, []),
  Node("interp2/snapshot", 3, []),
  
  // build.kk helper functions
  Node("build/make", 23, ["build/build", "std/core/list/any", "std/core/int/(==)", "std/core/exn/throw", "std/core/string/(++)", "std/core/list/find", "std/core/types/fst", "std/core/console/println", "std/core/types/list", "std/core/list/joinsep/join"]),
  Node("build/run-safe", 8, ["std/core/exn/throw-exn", "std/core/types/either", "std/core/console/println", "std/core/string/(++)", "std/core/exn/show"]),
  Node("build/my-makefile", 23, ["build/build", "std/core/string/(++)", "std/core/exn/throw"]),
  Node("build/my-makefile2", 36, ["build/build", "std/core/console/trace", "std/core/int/(==)", "std/core/string/(++)", "std/core/string/starts-with", "std/core/string/trim-left", "std/core/string/parse-int", "std/core/types/maybe", "std/core/exn/throw", "std/core/int/(<=)", "std/core/int/show", "std/core/int/(-)", "std/core/int/(+)", "std/core/int/default"]),
  
  // build.kk analyze functions
  Node("build/analyze-mymakefile-example1", 5, ["build/run-safe", "build/make", "build/my-makefile", "std/core/console/println", "std/core/string/(++)"]),
  Node("build/analyze-mymakefile-example2", 3, ["build/run-safe", "build/make", "build/my-makefile"]),
  Node("build/analyze-mymakefile-example3", 3, ["build/run-safe", "build/make", "build/my-makefile"]),
  Node("build/analyze-mymakefile-example4", 5, ["build/run-safe", "build/make", "build/my-makefile2", "std/core/console/println", "std/core/string/(++)"]),
  Node("build/analyze-mymakefile-example5", 5, ["build/run-safe", "build/make", "build/my-makefile2", "std/core/console/println", "std/core/string/(++)"]),
  
  // build.kk effects
  Node("build/build", 5, []),
  
  // coop-communication.kk types
  Node("coop-communication/task", 2, []),
  Node("coop-communication/chan", 2, []),
  Node("coop-communication/channel-state", 4, []),
  
  // coop-communication.kk helper functions
  Node("coop-communication/channel", 2, []),
  Node("coop-communication/schedule", 79, ["coop-communication/task", "coop-communication/channel-state", "coop-communication/comm", "std/core/list/(++)", "std/core/list/find", "std/core/string/(==)", "std/core/list/filter", "std/core/string/(!=)", "std/core/types/list"]),
  Node("coop-communication/test-yield", 9, ["coop-communication/schedule", "std/core/console/println", "coop-communication/comm"]),
  Node("coop-communication/test-spawn", 12, ["coop-communication/schedule", "std/core/console/println", "coop-communication/comm"]),
  Node("coop-communication/test-send-recv", 15, ["coop-communication/schedule", "std/core/console/println", "coop-communication/chan", "coop-communication/channel", "coop-communication/comm", "std/core/int/show", "std/core/string/(++)"]),
  Node("coop-communication/test-prime-sieve", 7, ["std/core/console/println", "coop-communication/chan", "coop-communication/channel", "coop-communication/schedule", "coop-communication/comm", "coop-communication/filter-actor", "coop-communication/generator"]),
  Node("coop-communication/filter-actor", 14, ["coop-communication/chan", "coop-communication/channel", "std/core/int/(+)", "std/core/int/show", "std/core/string/(++)", "std/core/console/println", "coop-communication/comm", "std/core/int/(%)"]),
  Node("coop-communication/generator", 7, ["coop-communication/chan", "coop-communication/comm", "std/core/console/println"]),
  
  // coop-communication.kk analyze functions
  Node("coop-communication/analyze-yield", 3, ["coop-communication/test-yield"]),
  Node("coop-communication/analyze-spawn", 3, ["coop-communication/test-spawn"]),
  Node("coop-communication/analyze-send-recv", 3, ["coop-communication/test-send-recv"]),
  Node("coop-communication/analyze-prime-sieve", 3, ["coop-communication/test-prime-sieve"]),
  
  // coop-communication.kk effects
  Node("coop-communication/comm", 11, []),
  
  // mini-ppl.kk helper functions
  Node("mini-ppl/uniform", 7, ["mini-ppl/choice", "std/core/int/(<=)", "std/core/int/(==)", "std/core/int/float64", "std/core/float64/(/)", "std/core/int/(+)", "std/core/int/(-)"]),
  Node("mini-ppl/reject", 2, ["std/core/exn/throw"]),
  Node("mini-ppl/exact", 14, ["mini-ppl/choice", "std/core/exn/throw-exn", "std/core/list/map", "std/core/types/fst", "std/core/types/snd", "std/core/list/(++)", "std/core/float64/(*)", "std/core/float64/(-)", "std/core/types/list"]),
  Node("mini-ppl/show-dist", 6, ["std/core/types/snd", "std/core/types/fst", "std/core/list/map", "std/core/list/sum", "std/core/string/(++)", "std/core/float64/show", "std/core/float64/(*)", "std/core/float64/(/)", "std/core/list/joinsep/join"]),
  Node("mini-ppl/sample", 9, ["mini-ppl/choice", "std/core/num/random/random-float64", "std/core/float64/(<)", "std/core/exn/throw-exn", "std/core/types/maybe"]),
  Node("mini-ppl/burglar-model", 13, ["mini-ppl/choice", "mini-ppl/reject", "std/core/bool/(&&)", "std/core/bool/(!)"]),
  Node("mini-ppl/drunk-walk", 5, ["mini-ppl/choice", "std/core/int/(>)", "std/core/int/(+)"]),
  
  // mini-ppl.kk analyze functions
  Node("mini-ppl/analyze-burglar", 3, ["std/core/num/random/pseudo-random", "mini-ppl/exact", "mini-ppl/burglar-model", "mini-ppl/show-dist"]),
  Node("mini-ppl/analyze-drunk", 3, ["std/core/num/random/pseudo-random", "mini-ppl/exact", "mini-ppl/drunk-walk", "std/core/int/show", "mini-ppl/show-dist"]),
  Node("mini-ppl/analyze-burglar-mc", 13, ["std/core/num/random/pseudo-random", "mini-ppl/sample", "mini-ppl/burglar-model", "std/core/int/(+)", "std/core/types/maybe", "std/core/string/(==)", "std/core/int/float64", "std/core/float64/(/)", "std/core/string/(++)", "std/core/int/show", "std/core/float64/show", "std/core/float64/(*)"]),
  
  // mini-ppl.kk effects
  Node("mini-ppl/choice", 3, []),
  
  // Standard library functions
  Node("std/core/console/trace", 3, []),
  Node("std/core/console/println", 2, []),
  Node("std/core/int/(+)", 1, []),
  Node("std/core/int/(-)", 1, []),
  Node("std/core/int/(*)", 1, []),
  Node("std/core/int/(%)", 1, []),
  Node("std/core/int/(<=)", 1, []),
  Node("std/core/int/(>)", 1, []),
  Node("std/core/int/(==)", 1, []),
  Node("std/core/int/show", 1, []),
  Node("std/core/int/float64", 1, []),
  Node("std/core/string/(++)", 1, []),
  Node("std/core/string/(==)", 1, []),
  Node("std/core/string/(!=)", 1, []),
  Node("std/core/bool/(&&)", 1, []),
  Node("std/core/bool/(!)", 1, []),
  Node("std/core/float64/show", 5, ["std/core/float64/abs", "std/core/float64/(>=)", "std/core/float64/(<)", "std/core/num/float64/show-fixed", "std/core/num/float64/show-exp"]),
  Node("std/core/float64/(+)", 1, []),
  Node("std/core/float64/(-)", 1, []),
  Node("std/core/float64/(*)", 1, []),
  Node("std/core/float64/(/)", 1, []),
  Node("std/core/float64/(<)", 1, []),
  Node("std/core/list/find", 3, []),
  Node("std/core/list/map", 3, []),
  Node("std/core/list/foldl", 3, []),
  Node("std/core/list/zip", 6, []),
  Node("std/core/list/length", 6, []),
  Node("std/core/list/(++)", 2, ["std/core/list/append"]),
  Node("std/core/list/append", 3, []),
  Node("std/core/exn/throw", 1, []),
  Node("std/core/exn/throw-exn", 3, []),
  Node("std/core/types/fst", 3, []),
  Node("std/core/types/snd", 3, []),
  Node("std/core/types/id", 2, []),
  Node("std/core/types/maybe", 3, []),
  Node("std/core/types/list", 3, []),
  Node("std/core/types/either", 3, []),
  Node("std/core/list/any", 5, []),
  Node("std/core/list/filter", 4, []),
  Node("std/core/list/joinsep/join", 2, ["std/core/list/joinsep"]),
  Node("std/core/list/joinsep", 6, ["std/core/string/(++)"]),
  Node("std/core/list/sum", 2, ["std/core/list/foldl", "std/core/int/(+)"]),
  Node("std/core/exn/show", 2, []),
  Node("std/core/string/starts-with", 4, []),
  Node("std/core/string/trim-left", 5, ["std/core/string/starts-with"]),
  Node("std/core/string/parse-int", 2, []),
  Node("std/core/int/default", 4, []),
  Node("std/core/num/random/random-float64", 3, ["std/core/num/random/random-int64", "std/core/int/shr", "std/core/int/or", "std/core/num/float64/float64-from-bits", "std/core/float64/(-)", "std/core/int/int64"]),
  Node("std/core/num/random/pseudo-random", 7, ["std/core/num/random/sfc-init", "std/core/num/random/sfc-step"]),
  Node("std/core/num/random/random-int64", 2, ["std/core/num/random/random-int32", "std/core/int/int64"]),
  Node("std/core/num/random/sfc-init", 2, ["std/core/num/random/sfc-init32", "std/core/int/int32", "std/core/int/(/)"]),
  Node("std/core/num/random/sfc-step", 8, ["std/core/int32/(+)", "std/core/int32/(^)", "std/core/int/shr", "std/core/int/shl", "std/core/int/rotl", "std/core/int/int32"]),
  Node("std/core/num/random/sfc-init32", 3, ["std/core/int/int32", "std/core/num/random/fold-int32", "std/core/num/random/sfc-step"]),
  Node("std/core/num/random/random-int32", 1, []),
  Node("std/core/num/random/fold-int32", 1, []),
  Node("std/core/int/int32", 1, []),
  Node("std/core/int/(/)", 1, []),
  Node("std/core/int32/(+)", 1, []),
  Node("std/core/int32/(^)", 1, []),
  Node("std/core/int/shr", 1, []),
  Node("std/core/int/or", 1, []),
  Node("std/core/int/shl", 1, []),
  Node("std/core/int/rotl", 1, []),
  Node("std/core/int/int64", 1, []),
  Node("std/core/float64/abs", 1, []),
  Node("std/core/float64/(>=)", 1, []),
  Node("std/core/num/float64/show-fixed", 1, []),
  Node("std/core/num/float64/show-exp", 1, []),
  Node("std/core/num/float64/float64-from-bits", 1, []),
  
  // music.kk
  Node("music/analyze-search-love", 5, ["music/music-manager", "music/search-service", "music/populate-lib", "music/find-songs", "std/core/list/map", "std/core/list/joinsep/join"]),
  Node("music/analyze-search-come", 5, ["music/music-manager", "music/search-service", "music/populate-lib", "music/find-songs", "std/core/list/map", "std/core/list/joinsep/join"]),
  Node("music/music-manager", 16, ["std/core/int/(+)", "music/artist", "music/album", "music/song"]),
  Node("music/search-service", 7, ["music/get-library", "std/core/list/filter", "std/core/string/to-lower", "std/core/string/contains"]),
  Node("music/populate-lib", 10, ["music/add-artist", "music/add-album", "music/add-song"]),
  Node("music/music-ops", 9, []),
  Node("music/search", 3, []),
  Node("music/add-artist", 1, []),
  Node("music/add-album", 1, []),
  Node("music/add-song", 1, []),
  Node("music/get-library", 1, []),
  Node("music/find-songs", 1, []),
  Node("music/artist", 3, []),
  Node("music/album", 4, []),
  Node("music/song", 5, []),
  Node("std/core/string/to-lower", 4, []),
  Node("std/core/string/contains", 4, []),
  
  // ukanren.kk
  Node("ukanren/analyze-q1", 10, ["ukanren/solve", "ukanren/fresh", "ukanren/to-logic-list", "ukanren/appendo", "std/core/list/map", "std/core/string/(++)", "ukanren/reify", "std/core/types/fst", "std/core/types/snd", "std/core/list/joinsep/join"]),
  Node("ukanren/analyze-q2", 10, ["ukanren/solve", "ukanren/fresh", "ukanren/to-logic-list", "ukanren/appendo", "std/core/list/map", "std/core/string/(++)", "ukanren/reify", "std/core/types/fst", "std/core/types/snd", "std/core/list/joinsep/join"]),
  Node("ukanren/solve", 20, ["ukanren/term", "std/core/int/(+)", "ukanren/unify", "std/core/list/(++)", "std/core/types/Nothing", "std/core/types/Just"]),
  Node("ukanren/logic", 7, []),
  Node("ukanren/walk", 7, ["std/core/list/find", "std/core/types/fst", "std/core/int/(==)", "std/core/types/Just", "std/core/types/Nothing"]),
  Node("ukanren/unify", 12, ["ukanren/walk", "ukanren/eq-term", "std/core/types/Just", "std/core/types/Nothing"]),
  Node("ukanren/eq-term", 6, ["std/core/int/(==)", "std/core/string/(=="]),
  Node("ukanren/(===)", 2, ["ukanren/unify-term"]),
  Node("ukanren/conde", 7, ["ukanren/unify-term", "ukanren/term", "ukanren/flip"]),
  Node("ukanren/to-logic-list", 4, ["ukanren/term", "std/core/int/show"]),
  Node("ukanren/reify", 6, ["ukanren/walk", "std/core/string/(++)", "std/core/int/show"]),
  Node("ukanren/appendo", 15, ["ukanren/conde", "ukanren/(===)", "ukanren/term", "ukanren/fresh"]),
  Node("ukanren/fresh", 1, []),
  Node("ukanren/unify-term", 1, []),
  Node("ukanren/flip", 1, []),
  Node("ukanren/term", 5, []),
  
  // rosetta/a/abcproblem.kk
  Node("abcproblem/analyze-main", 3, ["std/core/list/map", "abcproblem/can-make-word"]),
  Node("abcproblem/can-make-word", 2, ["abcproblem/check-word", "std/core/string/to-upper"]),
  Node("abcproblem/check-word", 8, ["std/core/string/head", "abcproblem/get-remove", "std/core/types/fst", "std/core/types/snd", "std/core/bool/(||)", "std/core/string/(==)", "std/core/types/Nothing", "std/core/types/Just", "std/core/string/tail"]),
  Node("abcproblem/get-remove", 4, ["std/core/bool/(!)", "std/core/types/list", "std/core/list/(++)", "std/core/types/Just", "std/core/types/Nothing"]),
  
  // rosetta/p/playing-cards.kk
  Node("playing-cards/analyze-deck", 5, ["playing-cards/deck", "playing-cards/shuffle", "playing-cards/simple/deal"]),
  Node("playing-cards/deck", 3, ["std/core/list/map", "std/core/list/concat", "playing-cards/Deck"]),
  Node("playing-cards/shuffle", 13, ["std/core/list/length", "std/core/num/random/random-int", "std/core/int/(%)", "std/core/list/split", "std/core/list/(++)", "playing-cards/split", "std/core/int/for", "playing-cards/Deck"]),
  Node("playing-cards/simple/deal", 2, ["std/core/list/split", "std/core/types/map", "playing-cards/Deck"]),
  Node("playing-cards/suit", 4, []),
  Node("playing-cards/rank", 13, []),
  Node("playing-cards/card", 2, []),
  Node("playing-cards/Deck", 1, []),
  Node("playing-cards/split", 1, []),
  
  // rosetta/b/balanced-ternary.kk
  Node("balanced-ternary/analyze-main", 5, ["balanced-ternary/from_string", "balanced-ternary/from_int", "balanced-ternary/btern/(*)", "balanced-ternary/btern/(-)"]),
  Node("balanced-ternary/from_string", 9, ["std/core/string/foreach", "std/core/exn/throw"]),
  Node("balanced-ternary/from_int", 7, ["std/core/int/(==)", "std/core/int/(%)", "std/core/int/(/)", "std/core/core/undiv/pretend-decreasing", "std/core/exn/throw", "balanced-ternary/btdigit"]),
  Node("balanced-ternary/btern/(*)", 7, ["balanced-ternary/btern", "balanced-ternary/btern/(+)", "balanced-ternary/btern/(-)", "balanced-ternary/neg"]),
  Node("balanced-ternary/btern/(+)", 16, ["std/core/list/is-nil", "std/core/exn/throw"]),
  Node("balanced-ternary/btern/(-)", 2, ["balanced-ternary/btern/(+)", "balanced-ternary/neg"]),
  Node("balanced-ternary/neg", 6, ["std/core/list/map"]),
  Node("balanced-ternary/btdigit", 3, []),
  Node("balanced-ternary/btern", 1, []),
  
  // rosetta/c/conjugate-latin-verbs.kk
  Node("conjugate-latin-verbs/analyze-main", 12, ["std/core/list/foreach", "std/core/string/(++)", "std/core/console/println", "conjugate-latin-verbs/conjugate", "std/core/types/list"]),
  Node("conjugate-latin-verbs/conjugate", 17, ["std/core/string/count", "std/core/int/(<)", "std/core/string/(++)", "conjugate-latin-verbs/yield", "std/core/sslice/last", "std/core/sslice/string", "std/core/sslice/before", "std/core/list/foreach"]),
  Node("conjugate-latin-verbs/yield-effect", 1, []),
  Node("conjugate-latin-verbs/yield", 1, []),
  
  // rosetta/m/monads-writer.kk
  Node("monads-writer/analyze-solution1", 2, ["monads-writer/solution1"]),
  Node("monads-writer/solution1", 7, ["monads-writer/write", "monads-writer/root", "monads-writer/add-one", "monads-writer/half", "std/core/list/reverse", "std/core/types/list"]),
  Node("monads-writer/write", 3, ["monads-writer/log", "std/core/string/pad-right", "std/core/string/(++)", "std/core/float64/show"]),
  Node("monads-writer/root", 1, ["monads-writer/write", "std/core/num/float64/sqrt"]),
  Node("monads-writer/add-one", 1, ["monads-writer/write", "std/core/float64/(+)"]),
  Node("monads-writer/half", 1, ["monads-writer/write", "std/core/float64/(/)"]),
  Node("monads-writer/log-effect", 1, []),
  Node("monads-writer/log", 1, []),
  
  // rosetta/j/jump-anywhere.kk
  Node("jump-anywhere/analyze-e1", 2, ["jump-anywhere/find-first"]),
  Node("jump-anywhere/analyze-loop", 7, ["jump-anywhere/loop", "std/core/int/(<)", "std/core/int/(+)"]),
  Node("jump-anywhere/find-first", 6, ["std/core/int/for", "std/core/int/(==)", "jump-anywhere/exit"]),
  Node("jump-anywhere/loop", 8, ["jump-anywhere/lbreak", "jump-anywhere/lcontinue"]),
  Node("jump-anywhere/exit-effect", 1, []),
  Node("jump-anywhere/exit", 1, []),
  Node("jump-anywhere/loop-effect", 3, []),
  Node("jump-anywhere/lbreak", 1, []),
  Node("jump-anywhere/lcontinue", 1, []),
  
  // rosetta/n/nim.kk
  Node("nim/analyze-nim", 2, ["nim/main"]),
  Node("nim/main", 16, ["std/core/int/for", "nim/get-move", "std/core/int/(-)", "std/core/int/(==)", "std/core/console/println", "std/core/int/show", "std/core/string/(++)", "std/core/types/Just", "nim/player/other", "nim/move", "std/core/types/Nothing"]),
  Node("nim/get-move", 17, ["std/core/int/min", "std/core/console/println", "std/core/int/show", "std/core/string/(++)", "std/core/os/readline/readline", "std/core/string/parse-int", "std/core/types/Just", "std/core/int/(>=)", "std/core/int/(<=)", "std/core/bool/(&&)", "std/core/types/Nothing"]),
  Node("nim/player", 2, []),
  Node("nim/player/other", 5, []),
  Node("nim/player/show", 5, []),
  Node("nim/move-effect", 1, []),
  Node("nim/move", 1, []),
  
  // rosetta/0-nums/pr4rings.kk
  Node("pr4rings/analyze-four-squares", 2, ["pr4rings/four_squares"]),
  Node("pr4rings/four_squares", 17, ["std/core/int/for", "pr4rings/is_unique", "pr4rings/is_solution", "std/core/bool/(||)", "std/core/bool/(!)", "std/core/bool/(&&)", "std/core/int/(+)", "std/core/int/show", "std/core/string/(++)"]),
  Node("pr4rings/is_unique", 6, ["std/core/int/(!=)", "std/core/bool/(&&)"]),
  Node("pr4rings/is_solution", 10, ["std/core/int/(+)", "std/core/int/(==)"]),
  
  // Standard library additions
  Node("std/core/string/to-upper", 4, []),
  Node("std/core/string/head", 1, []),
  Node("std/core/string/tail", 1, []),
  Node("std/core/bool/(!)", 1, []),
  Node("std/core/bool/(||)", 1, []),
  Node("std/core/bool/(&&)", 1, []),
  Node("std/core/list/concat", 1, []),
  Node("std/core/list/split", 1, []),
  Node("std/core/list/is-nil", 1, []),
  Node("std/core/list/reverse", 1, []),
  Node("std/core/types/map", 1, []),
  Node("std/core/num/random/random-int", 1, []),
  Node("std/core/string/foreach", 1, []),
  Node("std/core/string/count", 1, []),
  Node("std/core/string/pad-right", 1, []),
  Node("std/core/sslice/last", 1, []),
  Node("std/core/sslice/string", 1, []),
  Node("std/core/sslice/before", 1, []),
  Node("std/core/int/for", 1, []),
  Node("std/core/int/min", 1, []),
  Node("std/core/int/(>=)", 1, []),
  Node("std/core/int/(<=)", 1, []),
  Node("std/core/int/(!=)", 1, []),
  Node("std/core/int/(<)", 1, []),
  Node("std/core/os/readline/readline", 1, []),
  Node("std/core/core/undiv/pretend-decreasing", 1, []),
  Node("std/core/num/float64/sqrt", 1, [])
]
