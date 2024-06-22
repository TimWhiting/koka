// https://github.com/koka-lang/koka/issues/483
// Thanks @hflsmax for the report
rec effect process
  fun fork(p: () -> <process> ()): ()