div effect resched<e>
  final ctl exit(): ()
  ctl yield(): ()
  ctl go(task: () -> <resched<e>,div|e> ()): ()

fun mktask(task)
  fn()
    task()
    exit()

effect ping
  fun ping(): ()

tail fun sched(tasks)
  ping()
  match tasks
    Nil -> ()
    Cons(next, rest) ->
      val new-tasks =
        with handler
          return(_)
            impossible("forgot to exit() somewhere (see mktask)")
          final ctl exit()
            ([], [])
          raw ctl yield()
            ([], [{ rcontext.resume-shallow(()).ignore }])
          raw ctl go(task)
            ([{ rcontext.resume-shallow(()).ignore }], [mktask(task)])
        next()
      sched(new-tasks.fst ++ rest ++ new-tasks.snd)

fun sched/run(main)
  val count = ref(0)
  with fun ping()
    count := !count + 1
    if !count % 100 == 0 then println((!count).show ++ " task switches")
  sched([mktask(main)])

fun loop(n: int)
  repeat(n)
    yield()

fun main()
  sched/run
    go { loop(20000) }
    go { loop(20000) }
    go { loop(20000) }