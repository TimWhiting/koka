Evaluating: error/try((fn(){
  (@open(example-check)());
})) nim:812:t_[top]@[]
Evaluating: error/try nim:813:t_[top]@[]
Evaluating: error/try nim:815:t_[top]@[]
Evaluating: forall<a,e> fn(action){
  handle/try((fn(){
      (Ok((action())));
    }), (fn(exn){
      (Error(exn));
    }));
} exn:1589:t_[top]@[]
Extending store: BI@(1589:t_[top]@[]) with DefNonRec(error/try)
Extending store: T@std/core/exn/#error/try with DefNonRec(error/try)
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:814 0 fn(){
  @open(example-check)();
}], resolvedArgs = [], parent = LamBody [] error/try((fn(){
  (@open(example-check)());
}))}
Evaluating: fn(){
  @open(example-check)();
} nim:814:t_[top]@[]
Extending store: BI@(814:t_[top]@[]) with AppParam(fn(){
  @open(example-check)();
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/exn/#error/try], parent = LamBody [] error/try((fn(){
  (@open(example-check)());
}))}
Extending store: B@(action:t_[a812,top]@[]) with AppParam(fn(){
  @open(example-check)();
})
Evaluating: handle/try((fn(){
    (Ok((action())));
  }), (fn(exn){
    (Error(exn));
  })) exn:1610:t_[a812,top]@[]
Evaluating: handle/try exn:1611:t_[a812,top]@[]
Evaluating: handle/try exn:1614:t_[a812,top]@[]
Evaluating: forall<a,e> fn(action, hndl){
  (fn(@action){
    exn/@handle((@Hnd-exn(0, (forall<b> @open(clause-never1)((fn(exn){
          (hndl(exn));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (action());
  }));
} exn:1587:t_[top]@[]
Extending store: BI@(1587:t_[top]@[]) with DefNonRec(handle/try)
Extending store: T@std/core/exn/#handle/try with DefNonRec(handle/try)
Applying FApp {totalArgs = 2, leftArgs = [AppParam exn:1612 0 fn(){
  Ok((action()));
},AppParam exn:1613 1 fn(exn){
  Error(exn);
}], resolvedArgs = [], parent = LamBody [action] handle/try((fn(){
    (Ok((action())));
  }), (fn(exn){
    (Error(exn));
  }))}
Evaluating: fn(){
  Ok((action()));
} exn:1612:t_[a812,top]@[]
Extending store: BI@(1612:t_[a812,top]@[]) with AppParam(fn(){
  Ok((action()));
})
Applying FApp {totalArgs = 2, leftArgs = [AppParam exn:1613 1 fn(exn){
  Error(exn);
}], resolvedArgs = [T@std/core/exn/#handle/try], parent = LamBody [action] handle/try((fn(){
    (Ok((action())));
  }), (fn(exn){
    (Error(exn));
  }))}
Evaluating: fn(exn){
  Error(exn);
} exn:1613:t_[a812,top]@[]
Extending store: BI@(1613:t_[a812,top]@[]) with AppParam(fn(exn){
  Error(exn);
})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/exn/#handle/try,BI@(1612:t_[a812,top]@[])], parent = LamBody [action] handle/try((fn(){
    (Ok((action())));
  }), (fn(exn){
    (Error(exn));
  }))}
Extending store: B@(action:t_[a1610,a812,top]@[]) with AppParam(fn(){
  Ok((action()));
})
Extending store: B@(hndl:t_[a1610,a812,top]@[]) with AppParam(fn(exn){
  Error(exn);
})
Evaluating: (fn(@action){
  exn/@handle((@Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
        (hndl(exn));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (action());
})) exn:1615:t_[a1610,a812,top]@[]
Evaluating: fn(@action){
  exn/@handle((@Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
        (hndl(exn));
      }))))), (fn(@res){
      @res;
    }), @action);
} exn:1616:t_[a1610,a812,top]@[]
Extending store: BI@(1616:t_[a1610,a812,top]@[]) with AppLambda(fn(@action){
  exn/@handle((@Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
        (hndl(exn));
      }))))), (fn(@res){
      @res;
    }), @action);
})
Applying FApp {totalArgs = 1, leftArgs = [AppParam exn:1617 0 fn(){
  action();
}], resolvedArgs = [], parent = LamBody [action,hndl] (fn(@action){
  exn/@handle((@Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
        (hndl(exn));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (action());
}))}
Evaluating: fn(){
  action();
} exn:1617:t_[a1610,a812,top]@[]
Extending store: BI@(1617:t_[a1610,a812,top]@[]) with AppParam(fn(){
  action();
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(1616:t_[a1610,a812,top]@[])], parent = LamBody [action,hndl] (fn(@action){
  exn/@handle((@Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
        (hndl(exn));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (action());
}))}
Extending store: B@(@action:t_[a1615,a1610,a812,top]@[]) with AppParam(fn(){
  action();
})
Extending store: B@(hndl:t_[a1615,a1610,a812,top]@[]) with AppParam(fn(exn){
  Error(exn);
})
Evaluating: exn/@handle((@Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
      (hndl(exn));
    }))))), (fn(@res){
    @res;
  }), @action) exn:1618:t_[a1615,a1610,a812,top]@[]
Evaluating: exn/@handle exn:1619:t_[a1615,a1610,a812,top]@[]
Evaluating: exn/@handle exn:1623:t_[a1615,a1610,a812,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(exn/@tag, hnd, ret, action);
} exn:1539:t_[top]@[]
Extending store: BI@(1539:t_[top]@[]) with DefNonRec(exn/@handle)
Extending store: T@std/core/exn/#exn/@handle with DefNonRec(exn/@handle)
Applying FApp {totalArgs = 3, leftArgs = [AppParam exn:1620 0 @Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
    (hndl(exn));
  })))),AppParam exn:1621 1 fn(@res){
  @res;
},AppParam exn:1622 2 @action], resolvedArgs = [], parent = LamBody [@action] exn/@handle((@Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
      (hndl(exn));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
    (hndl(exn));
  })))) exn:1620:t_[a1615,a1610,a812,top]@[]
Evaluating: @Hnd-exn exn:1624:t_[a1615,a1610,a812,top]@[]
Evaluating: @Hnd-exn exn:1627:t_[a1615,a1610,a812,top]@[]
Extending store: BI@(1627:t_[a1615,a1610,a812,top]@[]) with @Hnd-exn
Applying FApp {totalArgs = 2, leftArgs = [AppParam exn:1625 0 0,AppParam exn:1626 1 forall<a> @open(clause-never1)((fn(exn){
  (hndl(exn));
}))], resolvedArgs = [], parent = AppParam exn:1620 0 @Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
    (hndl(exn));
  }))))}
Evaluating: 0 exn:1625:t_[a1615,a1610,a812,top]@[]
Extending store: BI@(1625:t_[a1615,a1610,a812,top]@[]) with int -> (exn:1625,0)
Applying FApp {totalArgs = 2, leftArgs = [AppParam exn:1626 1 forall<a> @open(clause-never1)((fn(exn){
  (hndl(exn));
}))], resolvedArgs = [BI@(1627:t_[a1615,a1610,a812,top]@[])], parent = AppParam exn:1620 0 @Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
    (hndl(exn));
  }))))}
Evaluating: forall<a> @open(clause-never1)((fn(exn){
  (hndl(exn));
})) exn:1626:t_[a1615,a1610,a812,top]@[]
Evaluating: clause-never1 exn:1631:t_[a1615,a1610,a812,top]@[]
Evaluating: clause-never1 exn:1632:t_[a1615,a1610,a812,top]@[]
Extending store: BI@(1632:t_[a1615,a1610,a812,top]@[]) with std/core/hnd/clause-never1
Applying FApp {totalArgs = 1, leftArgs = [AppParam exn:1629 0 fn(exn){
  hndl(exn);
}], resolvedArgs = [], parent = AppParam exn:1626 1 forall<a> @open(clause-never1)((fn(exn){
  (hndl(exn));
}))}
Evaluating: fn(exn){
  hndl(exn);
} exn:1629:t_[a1615,a1610,a812,top]@[]
Extending store: BI@(1629:t_[a1615,a1610,a812,top]@[]) with AppParam(fn(exn){
  hndl(exn);
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(1632:t_[a1615,a1610,a812,top]@[])], parent = AppParam exn:1626 1 forall<a> @open(clause-never1)((fn(exn){
  (hndl(exn));
}))}
Extending store: CI@(clause-never11 1626:t_[a1615,a1610,a812,top]@[]) with AppParam(fn(exn){
  hndl(exn);
})
Extending store: BI@(1626:t_[a1615,a1610,a812,top]@[]) with std/core/hnd/clause-never1([(,CI@(clause-never11 1626:t_[a1615,a1610,a812,top]@[]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1627:t_[a1615,a1610,a812,top]@[]),BI@(1625:t_[a1615,a1610,a812,top]@[])], parent = AppParam exn:1620 0 @Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
    (hndl(exn));
  }))))}
Extending store: CI@(@cfc 1620:t_[a1615,a1610,a812,top]@[]) with int -> (exn:1625,0)
Extending store: CI@(@brk-throw-exn 1620:t_[a1615,a1610,a812,top]@[]) with std/core/hnd/clause-never1([(,CI@(clause-never11 1626:t_[a1615,a1610,a812,top]@[]))])
Extending store: BI@(1620:t_[a1615,a1610,a812,top]@[]) with std/core/exn/@Hnd-exn([(@cfc,CI@(@cfc 1620:t_[a1615,a1610,a812,top]@[])),(@brk-throw-exn,CI@(@brk-throw-exn 1620:t_[a1615,a1610,a812,top]@[]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam exn:1621 1 fn(@res){
  @res;
},AppParam exn:1622 2 @action], resolvedArgs = [T@std/core/exn/#exn/@handle], parent = LamBody [@action] exn/@handle((@Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
      (hndl(exn));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} exn:1621:t_[a1615,a1610,a812,top]@[]
Extending store: BI@(1621:t_[a1615,a1610,a812,top]@[]) with AppParam(fn(@res){
  @res;
})
Applying FApp {totalArgs = 3, leftArgs = [AppParam exn:1622 2 @action], resolvedArgs = [T@std/core/exn/#exn/@handle,BI@(1620:t_[a1615,a1610,a812,top]@[])], parent = LamBody [@action] exn/@handle((@Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
      (hndl(exn));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action exn:1622:t_[a1615,a1610,a812,top]@[]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@std/core/exn/#exn/@handle,BI@(1620:t_[a1615,a1610,a812,top]@[]),BI@(1621:t_[a1615,a1610,a812,top]@[])], parent = LamBody [@action] exn/@handle((@Hnd-exn(0, (forall<a> @open(clause-never1)((fn(exn){
      (hndl(exn));
    }))))), (fn(@res){
    @res;
  }), @action)}
Extending store: B@(hnd:t_[a1618,a1615,a1610,a812,top]@[]) with std/core/exn/@Hnd-exn([(@cfc,CI@(@cfc 1620:t_[a1615,a1610,a812,top]@[])),(@brk-throw-exn,CI@(@brk-throw-exn 1620:t_[a1615,a1610,a812,top]@[]))])
Extending store: B@(ret:t_[a1618,a1615,a1610,a812,top]@[]) with AppParam(fn(@res){
  @res;
})
Extending store: B@(action:t_[a1618,a1615,a1610,a812,top]@[]) with AppParam(fn(){
  action();
})
Evaluating: @hhandle(exn/@tag, hnd, ret, action) exn:1633:t_[a1618,a1615,a1610,a812,top]@[]
Evaluating: @hhandle exn:1634:t_[a1618,a1615,a1610,a812,top]@[]
Evaluating: @hhandle exn:1639:t_[a1618,a1615,a1610,a812,top]@[]
Extending store: BI@(1639:t_[a1618,a1615,a1610,a812,top]@[]) with std/core/hnd/@hhandle
Applying FApp {totalArgs = 4, leftArgs = [AppParam exn:1635 0 exn/@tag,AppParam exn:1636 1 hnd,AppParam exn:1637 2 ret,AppParam exn:1638 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(exn/@tag, hnd, ret, action)}
Evaluating: exn/@tag exn:1635:t_[a1618,a1615,a1610,a812,top]@[]
Evaluating: @open(@new-htag)("exn@exn") exn:1537:t_[top]@[]
Evaluating: @new-htag exn:1643:t_[top]@[]
Evaluating: @new-htag exn:1644:t_[top]@[]
Extending store: BI@(1644:t_[top]@[]) with std/core/hnd/@new-htag
Applying FApp {totalArgs = 1, leftArgs = [AppParam exn:1641 0 "exn@exn"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:exn`
pub val exn/@tag : hnd/htag<exn>;}
Evaluating: "exn@exn" exn:1641:t_[top]@[]
Extending store: BI@(1641:t_[top]@[]) with string -> (exn:1641,"exn@exn")
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(1644:t_[top]@[])], parent = DefNonRec // runtime tag for the effect `:exn`
pub val exn/@tag : hnd/htag<exn>;}
Extending store: CI@(@new-htag1 1537:t_[top]@[]) with string -> (exn:1641,"exn@exn")
Extending store: BI@(1537:t_[top]@[]) with std/core/hnd/@new-htag([(,CI@(@new-htag1 1537:t_[top]@[]))])
Extending store: T@std/core/exn/#exn/@tag with std/core/hnd/@new-htag([(,CI@(@new-htag1 1537:t_[top]@[]))])
Applying FApp {totalArgs = 4, leftArgs = [AppParam exn:1636 1 hnd,AppParam exn:1637 2 ret,AppParam exn:1638 3 action], resolvedArgs = [BI@(1639:t_[a1618,a1615,a1610,a812,top]@[])], parent = LamBody [hnd,ret,action] @hhandle(exn/@tag, hnd, ret, action)}
Evaluating: hnd exn:1636:t_[a1618,a1615,a1610,a812,top]@[]
Applying FApp {totalArgs = 4, leftArgs = [AppParam exn:1637 2 ret,AppParam exn:1638 3 action], resolvedArgs = [BI@(1639:t_[a1618,a1615,a1610,a812,top]@[]),T@std/core/exn/#exn/@tag], parent = LamBody [hnd,ret,action] @hhandle(exn/@tag, hnd, ret, action)}
Evaluating: ret exn:1637:t_[a1618,a1615,a1610,a812,top]@[]
Applying FApp {totalArgs = 4, leftArgs = [AppParam exn:1638 3 action], resolvedArgs = [BI@(1639:t_[a1618,a1615,a1610,a812,top]@[]),T@std/core/exn/#exn/@tag,B@(hnd:t_[a1618,a1615,a1610,a812,top]@[])], parent = LamBody [hnd,ret,action] @hhandle(exn/@tag, hnd, ret, action)}
Evaluating: action exn:1638:t_[a1618,a1615,a1610,a812,top]@[]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(1639:t_[a1618,a1615,a1610,a812,top]@[]),T@std/core/exn/#exn/@tag,B@(hnd:t_[a1618,a1615,a1610,a812,top]@[]),B@(ret:t_[a1618,a1615,a1610,a812,top]@[])], parent = LamBody [hnd,ret,action] @hhandle(exn/@tag, hnd, ret, action)}
Extending store: B@(action:d_[delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(){
  Ok((action()));
})
Evaluating: action() exn:1645:d_[delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action exn:1646:d_[delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [] action()}
Extending store: B@(action:d_[a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(){
  @open(example-check)();
})
Evaluating: Ok((action())) exn:1647:d_[a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Ok exn:1648:d_[a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Ok exn:1650:d_[a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1650:d_[a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Ok
Applying FApp {totalArgs = 1, leftArgs = [AppParam exn:1649 0 action()], resolvedArgs = [], parent = LamBody [] Ok((action()))}
Evaluating: action() exn:1649:d_[a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action exn:1651:d_[a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = AppParam exn:1649 0 action()}
Evaluating: @open(example-check)() nim:816:d_[a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: example-check nim:819:d_[a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: fn(){
  perfect((fn(){
    (cheat-report((fn(){
      (check((fn(){
        (@open(game)(7));
      })));
    })));
  }));
} nim:66:t_[top]@[]
Extending store: BI@(66:t_[top]@[]) with DefNonRec(example-check)
Extending store: T@analysis/benchmarks/handlers/nim/example-check with DefNonRec(example-check)
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [] @open(example-check)()}
Evaluating: perfect((fn(){
  (cheat-report((fn(){
    (check((fn(){
      (@open(game)(7));
    })));
  })));
})) nim:792:d_[a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: perfect nim:793:d_[a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: perfect nim:795:d_[a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a,e> fn(@action){
  move/@handle((@Hnd-move(1, (@open(clause-tail2)((fn(_p, n){
        (@open(max)(1, (@open((%))(n, 4))));
      }))))), (fn(@res){
      @res;
    }), @action);
} nim:28:t_[top]@[]
Extending store: BI@(28:t_[top]@[]) with DefNonRec(perfect)
Extending store: T@analysis/benchmarks/handlers/nim/perfect with DefNonRec(perfect)
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:794 0 fn(){
  cheat-report((fn(){
    (check((fn(){
      (@open(game)(7));
    })));
  }));
}], resolvedArgs = [], parent = LamBody [] perfect((fn(){
  (cheat-report((fn(){
    (check((fn(){
      (@open(game)(7));
    })));
  })));
}))}
Evaluating: fn(){
  cheat-report((fn(){
    (check((fn(){
      (@open(game)(7));
    })));
  }));
} nim:794:d_[a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(794:d_[a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(){
  cheat-report((fn(){
    (check((fn(){
      (@open(game)(7));
    })));
  }));
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/perfect], parent = LamBody [] perfect((fn(){
  (cheat-report((fn(){
    (check((fn(){
      (@open(game)(7));
    })));
  })));
}))}
Extending store: B@(@action:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(){
  cheat-report((fn(){
    (check((fn(){
      (@open(game)(7));
    })));
  }));
})
Evaluating: move/@handle((@Hnd-move(1, (@open(clause-tail2)((fn(_p, n){
      (@open(max)(1, (@open((%))(n, 4))));
    }))))), (fn(@res){
    @res;
  }), @action) nim:306:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move/@handle nim:307:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move/@handle nim:311:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(move/@tag, hnd, ret, action);
} nim:17:t_[top]@[]
Extending store: BI@(17:t_[top]@[]) with DefNonRec(move/@handle)
Extending store: T@analysis/benchmarks/handlers/nim/#move/@handle with DefNonRec(move/@handle)
Applying FApp {totalArgs = 3, leftArgs = [AppParam nim:308 0 @Hnd-move(1, (@open(clause-tail2)((fn(_p, n){
    (@open(max)(1, (@open((%))(n, 4))));
  })))),AppParam nim:309 1 fn(@res){
  @res;
},AppParam nim:310 2 @action], resolvedArgs = [], parent = LamBody [@action] move/@handle((@Hnd-move(1, (@open(clause-tail2)((fn(_p, n){
      (@open(max)(1, (@open((%))(n, 4))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @Hnd-move(1, (@open(clause-tail2)((fn(_p, n){
    (@open(max)(1, (@open((%))(n, 4))));
  })))) nim:308:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @Hnd-move nim:312:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @Hnd-move nim:315:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(315:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with @Hnd-move
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:313 0 1,AppParam nim:314 1 @open(clause-tail2)((fn(_p, n){
  (@open(max)(1, (@open((%))(n, 4))));
}))], resolvedArgs = [], parent = AppParam nim:308 0 @Hnd-move(1, (@open(clause-tail2)((fn(_p, n){
    (@open(max)(1, (@open((%))(n, 4))));
  }))))}
Evaluating: 1 nim:313:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(313:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:313,1)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:314 1 @open(clause-tail2)((fn(_p, n){
  (@open(max)(1, (@open((%))(n, 4))));
}))], resolvedArgs = [BI@(315:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:308 0 @Hnd-move(1, (@open(clause-tail2)((fn(_p, n){
    (@open(max)(1, (@open((%))(n, 4))));
  }))))}
Evaluating: @open(clause-tail2)((fn(_p, n){
  (@open(max)(1, (@open((%))(n, 4))));
})) nim:314:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: clause-tail2 nim:320:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: clause-tail2 nim:322:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(322:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/clause-tail2
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:318 0 fn(_p, n){
  @open(max)(1, (@open((%))(n, 4)));
}], resolvedArgs = [], parent = AppParam nim:314 1 @open(clause-tail2)((fn(_p, n){
  (@open(max)(1, (@open((%))(n, 4))));
}))}
Evaluating: fn(_p, n){
  @open(max)(1, (@open((%))(n, 4)));
} nim:318:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(318:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(_p, n){
  @open(max)(1, (@open((%))(n, 4)));
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(322:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:314 1 @open(clause-tail2)((fn(_p, n){
  (@open(max)(1, (@open((%))(n, 4))));
}))}
Extending store: CI@(clause-tail21 314:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(_p, n){
  @open(max)(1, (@open((%))(n, 4)));
})
Extending store: BI@(314:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/clause-tail2([(,CI@(clause-tail21 314:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(315:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(313:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:308 0 @Hnd-move(1, (@open(clause-tail2)((fn(_p, n){
    (@open(max)(1, (@open((%))(n, 4))));
  }))))}
Extending store: CI@(@cfc 308:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:313,1)
Extending store: CI@(@ctl-move 308:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/clause-tail2([(,CI@(clause-tail21 314:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(308:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with analysis/benchmarks/handlers/nim/@Hnd-move([(@cfc,CI@(@cfc 308:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(@ctl-move,CI@(@ctl-move 308:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam nim:309 1 fn(@res){
  @res;
},AppParam nim:310 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/nim/#move/@handle], parent = LamBody [@action] move/@handle((@Hnd-move(1, (@open(clause-tail2)((fn(_p, n){
      (@open(max)(1, (@open((%))(n, 4))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} nim:309:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(309:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(@res){
  @res;
})
Applying FApp {totalArgs = 3, leftArgs = [AppParam nim:310 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/nim/#move/@handle,BI@(308:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [@action] move/@handle((@Hnd-move(1, (@open(clause-tail2)((fn(_p, n){
      (@open(max)(1, (@open((%))(n, 4))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action nim:310:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/#move/@handle,BI@(308:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(309:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [@action] move/@handle((@Hnd-move(1, (@open(clause-tail2)((fn(_p, n){
      (@open(max)(1, (@open((%))(n, 4))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Extending store: B@(hnd:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with analysis/benchmarks/handlers/nim/@Hnd-move([(@cfc,CI@(@cfc 308:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(@ctl-move,CI@(@ctl-move 308:d_[a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(ret:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(@res){
  @res;
})
Extending store: B@(action:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(){
  cheat-report((fn(){
    (check((fn(){
      (@open(game)(7));
    })));
  }));
})
Evaluating: @hhandle(move/@tag, hnd, ret, action) nim:185:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @hhandle nim:186:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @hhandle nim:191:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(191:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@hhandle
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:187 0 move/@tag,AppParam nim:188 1 hnd,AppParam nim:189 2 ret,AppParam nim:190 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(move/@tag, hnd, ret, action)}
Evaluating: move/@tag nim:187:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open(@new-htag)("move@nim") nim:15:t_[top]@[]
Evaluating: @new-htag nim:181:t_[top]@[]
Evaluating: @new-htag nim:183:t_[top]@[]
Extending store: BI@(183:t_[top]@[]) with std/core/hnd/@new-htag
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:179 0 "move@nim"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:move`
val move/@tag : hnd/htag<analysis/benchmarks/handlers/nim/move>;}
Evaluating: "move@nim" nim:179:t_[top]@[]
Extending store: BI@(179:t_[top]@[]) with string -> (nim:179,"move@nim")
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(183:t_[top]@[])], parent = DefNonRec // runtime tag for the effect `:move`
val move/@tag : hnd/htag<analysis/benchmarks/handlers/nim/move>;}
Extending store: CI@(@new-htag1 15:t_[top]@[]) with string -> (nim:179,"move@nim")
Extending store: BI@(15:t_[top]@[]) with std/core/hnd/@new-htag([(,CI@(@new-htag1 15:t_[top]@[]))])
Extending store: T@analysis/benchmarks/handlers/nim/#move/@tag with std/core/hnd/@new-htag([(,CI@(@new-htag1 15:t_[top]@[]))])
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:188 1 hnd,AppParam nim:189 2 ret,AppParam nim:190 3 action], resolvedArgs = [BI@(191:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [hnd,ret,action] @hhandle(move/@tag, hnd, ret, action)}
Evaluating: hnd nim:188:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:189 2 ret,AppParam nim:190 3 action], resolvedArgs = [BI@(191:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@tag], parent = LamBody [hnd,ret,action] @hhandle(move/@tag, hnd, ret, action)}
Evaluating: ret nim:189:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:190 3 action], resolvedArgs = [BI@(191:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@tag,B@(hnd:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [hnd,ret,action] @hhandle(move/@tag, hnd, ret, action)}
Evaluating: action nim:190:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(191:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@tag,B@(hnd:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(ret:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [hnd,ret,action] @hhandle(move/@tag, hnd, ret, action)}
Evaluating: cheat-report((fn(){
  (check((fn(){
    (@open(game)(7));
  })));
})) nim:796:d_[delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: cheat-report nim:797:d_[delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: cheat-report nim:799:d_[delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a,e> fn(@action){
  cheat/@handle((@Hnd-cheat(1, (forall<b> @open(clause-tail1)((fn(p){
        (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
      }))))), (fn(@res){
      @res;
    }), @action);
} nim:62:t_[top]@[]
Extending store: BI@(62:t_[top]@[]) with DefNonRec(cheat-report)
Extending store: T@analysis/benchmarks/handlers/nim/cheat-report with DefNonRec(cheat-report)
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:798 0 fn(){
  check((fn(){
    (@open(game)(7));
  }));
}], resolvedArgs = [], parent = LamBody [] cheat-report((fn(){
  (check((fn(){
    (@open(game)(7));
  })));
}))}
Evaluating: fn(){
  check((fn(){
    (@open(game)(7));
  }));
} nim:798:d_[delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(798:d_[delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(){
  check((fn(){
    (@open(game)(7));
  }));
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/cheat-report], parent = LamBody [] cheat-report((fn(){
  (check((fn(){
    (@open(game)(7));
  })));
}))}
Extending store: B@(@action:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(){
  check((fn(){
    (@open(game)(7));
  }));
})
Evaluating: cheat/@handle((@Hnd-cheat(1, (forall<a> @open(clause-tail1)((fn(p){
      (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
    }))))), (fn(@res){
    @res;
  }), @action) nim:670:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: cheat/@handle nim:671:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: cheat/@handle nim:675:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(cheat/@tag, hnd, ret, action);
} nim:56:t_[top]@[]
Extending store: BI@(56:t_[top]@[]) with DefNonRec(cheat/@handle)
Extending store: T@analysis/benchmarks/handlers/nim/#cheat/@handle with DefNonRec(cheat/@handle)
Applying FApp {totalArgs = 3, leftArgs = [AppParam nim:672 0 @Hnd-cheat(1, (forall<a> @open(clause-tail1)((fn(p){
    (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
  })))),AppParam nim:673 1 fn(@res){
  @res;
},AppParam nim:674 2 @action], resolvedArgs = [], parent = LamBody [@action] cheat/@handle((@Hnd-cheat(1, (forall<a> @open(clause-tail1)((fn(p){
      (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @Hnd-cheat(1, (forall<a> @open(clause-tail1)((fn(p){
    (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
  })))) nim:672:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @Hnd-cheat nim:676:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @Hnd-cheat nim:679:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(679:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with @Hnd-cheat
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:677 0 1,AppParam nim:678 1 forall<a> @open(clause-tail1)((fn(p){
  (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
}))], resolvedArgs = [], parent = AppParam nim:672 0 @Hnd-cheat(1, (forall<a> @open(clause-tail1)((fn(p){
    (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
  }))))}
Evaluating: 1 nim:677:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(677:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:677,1)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:678 1 forall<a> @open(clause-tail1)((fn(p){
  (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
}))], resolvedArgs = [BI@(679:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:672 0 @Hnd-cheat(1, (forall<a> @open(clause-tail1)((fn(p){
    (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
  }))))}
Evaluating: forall<a> @open(clause-tail1)((fn(p){
  (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
})) nim:678:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: clause-tail1 nim:684:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: clause-tail1 nim:686:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(686:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/clause-tail1
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:682 0 fn(p){
  @open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None);
}], resolvedArgs = [], parent = AppParam nim:678 1 forall<a> @open(clause-tail1)((fn(p){
  (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
}))}
Evaluating: fn(p){
  @open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None);
} nim:682:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(682:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(p){
  @open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None);
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(686:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:678 1 forall<a> @open(clause-tail1)((fn(p){
  (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
}))}
Extending store: CI@(clause-tail11 678:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(p){
  @open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None);
})
Extending store: BI@(678:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/clause-tail1([(,CI@(clause-tail11 678:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(679:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(677:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:672 0 @Hnd-cheat(1, (forall<a> @open(clause-tail1)((fn(p){
    (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
  }))))}
Extending store: CI@(@cfc 672:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:677,1)
Extending store: CI@(@fun-cheat 672:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/clause-tail1([(,CI@(clause-tail11 678:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(672:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with analysis/benchmarks/handlers/nim/@Hnd-cheat([(@cfc,CI@(@cfc 672:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(@fun-cheat,CI@(@fun-cheat 672:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam nim:673 1 fn(@res){
  @res;
},AppParam nim:674 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/nim/#cheat/@handle], parent = LamBody [@action] cheat/@handle((@Hnd-cheat(1, (forall<a> @open(clause-tail1)((fn(p){
      (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} nim:673:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(673:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(@res){
  @res;
})
Applying FApp {totalArgs = 3, leftArgs = [AppParam nim:674 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/nim/#cheat/@handle,BI@(672:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [@action] cheat/@handle((@Hnd-cheat(1, (forall<a> @open(clause-tail1)((fn(p){
      (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action nim:674:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/#cheat/@handle,BI@(672:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(673:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [@action] cheat/@handle((@Hnd-cheat(1, (forall<a> @open(clause-tail1)((fn(p){
      (@open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None));
    }))))), (fn(@res){
    @res;
  }), @action)}
Extending store: B@(hnd:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with analysis/benchmarks/handlers/nim/@Hnd-cheat([(@cfc,CI@(@cfc 672:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(@fun-cheat,CI@(@fun-cheat 672:d_[a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(ret:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(@res){
  @res;
})
Extending store: B@(action:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(){
  check((fn(){
    (@open(game)(7));
  }));
})
Evaluating: @hhandle(cheat/@tag, hnd, ret, action) nim:633:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @hhandle nim:634:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @hhandle nim:639:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(639:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@hhandle
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:635 0 cheat/@tag,AppParam nim:636 1 hnd,AppParam nim:637 2 ret,AppParam nim:638 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(cheat/@tag, hnd, ret, action)}
Evaluating: cheat/@tag nim:635:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open(@new-htag)("cheat@nim") nim:54:t_[top]@[]
Evaluating: @new-htag nim:629:t_[top]@[]
Evaluating: @new-htag nim:631:t_[top]@[]
Extending store: BI@(631:t_[top]@[]) with std/core/hnd/@new-htag
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:627 0 "cheat@nim"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:cheat`
val cheat/@tag : hnd/htag<analysis/benchmarks/handlers/nim/cheat>;}
Evaluating: "cheat@nim" nim:627:t_[top]@[]
Extending store: BI@(627:t_[top]@[]) with string -> (nim:627,"cheat@nim")
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(631:t_[top]@[])], parent = DefNonRec // runtime tag for the effect `:cheat`
val cheat/@tag : hnd/htag<analysis/benchmarks/handlers/nim/cheat>;}
Extending store: CI@(@new-htag1 54:t_[top]@[]) with string -> (nim:627,"cheat@nim")
Extending store: BI@(54:t_[top]@[]) with std/core/hnd/@new-htag([(,CI@(@new-htag1 54:t_[top]@[]))])
Extending store: T@analysis/benchmarks/handlers/nim/#cheat/@tag with std/core/hnd/@new-htag([(,CI@(@new-htag1 54:t_[top]@[]))])
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:636 1 hnd,AppParam nim:637 2 ret,AppParam nim:638 3 action], resolvedArgs = [BI@(639:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [hnd,ret,action] @hhandle(cheat/@tag, hnd, ret, action)}
Evaluating: hnd nim:636:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:637 2 ret,AppParam nim:638 3 action], resolvedArgs = [BI@(639:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#cheat/@tag], parent = LamBody [hnd,ret,action] @hhandle(cheat/@tag, hnd, ret, action)}
Evaluating: ret nim:637:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:638 3 action], resolvedArgs = [BI@(639:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#cheat/@tag,B@(hnd:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [hnd,ret,action] @hhandle(cheat/@tag, hnd, ret, action)}
Evaluating: action nim:638:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(639:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#cheat/@tag,B@(hnd:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(ret:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [hnd,ret,action] @hhandle(cheat/@tag, hnd, ret, action)}
Evaluating: check((fn(){
  (@open(game)(7));
})) nim:800:d_[delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: check nim:801:d_[delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: check nim:803:d_[delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a,e> fn(@action){
  move/@handle((@Hnd-move(3, (@open(clause-control2)((fn(p, n, resume){
        val m : int
              = (@open(move)(p, n));
        val z : bool
              = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
                  (@open((==))(i, m));
                })))));
        (match (z) {
          (True() : bool )
             -> resume(m);
          (@skip False() : bool )
             -> @open(cheat)(p);
        });
      }))))), (fn(@res){
      @res;
    }), @action);
} nim:64:t_[top]@[]
Extending store: BI@(64:t_[top]@[]) with DefNonRec(check)
Extending store: T@analysis/benchmarks/handlers/nim/check with DefNonRec(check)
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:802 0 fn(){
  @open(game)(7);
}], resolvedArgs = [], parent = LamBody [] check((fn(){
  (@open(game)(7));
}))}
Evaluating: fn(){
  @open(game)(7);
} nim:802:d_[delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(802:d_[delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(){
  @open(game)(7);
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/check], parent = LamBody [] check((fn(){
  (@open(game)(7));
}))}
Extending store: B@(@action:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(){
  @open(game)(7);
})
Evaluating: move/@handle((@Hnd-move(3, (@open(clause-control2)((fn(p, n, resume){
      val m : int
            = (@open(move)(p, n));
      val z : bool
            = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
                (@open((==))(i, m));
              })))));
      (match (z) {
        (True() : bool )
           -> resume(m);
        (@skip False() : bool )
           -> @open(cheat)(p);
      });
    }))))), (fn(@res){
    @res;
  }), @action) nim:714:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move/@handle nim:715:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move/@handle nim:719:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam nim:716 0 @Hnd-move(3, (@open(clause-control2)((fn(p, n, resume){
    val m : int
          = (@open(move)(p, n));
    val z : bool
          = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
              (@open((==))(i, m));
            })))));
    (match (z) {
      (True() : bool )
         -> resume(m);
      (@skip False() : bool )
         -> @open(cheat)(p);
    });
  })))),AppParam nim:717 1 fn(@res){
  @res;
},AppParam nim:718 2 @action], resolvedArgs = [], parent = LamBody [@action] move/@handle((@Hnd-move(3, (@open(clause-control2)((fn(p, n, resume){
      val m : int
            = (@open(move)(p, n));
      val z : bool
            = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
                (@open((==))(i, m));
              })))));
      (match (z) {
        (True() : bool )
           -> resume(m);
        (@skip False() : bool )
           -> @open(cheat)(p);
      });
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @Hnd-move(3, (@open(clause-control2)((fn(p, n, resume){
    val m : int
          = (@open(move)(p, n));
    val z : bool
          = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
              (@open((==))(i, m));
            })))));
    (match (z) {
      (True() : bool )
         -> resume(m);
      (@skip False() : bool )
         -> @open(cheat)(p);
    });
  })))) nim:716:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @Hnd-move nim:720:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @Hnd-move nim:723:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(723:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with @Hnd-move
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:721 0 3,AppParam nim:722 1 @open(clause-control2)((fn(p, n, resume){
  val m : int
        = (@open(move)(p, n));
  val z : bool
        = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
            (@open((==))(i, m));
          })))));
  (match (z) {
    (True() : bool )
       -> resume(m);
    (@skip False() : bool )
       -> @open(cheat)(p);
  });
}))], resolvedArgs = [], parent = AppParam nim:716 0 @Hnd-move(3, (@open(clause-control2)((fn(p, n, resume){
    val m : int
          = (@open(move)(p, n));
    val z : bool
          = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
              (@open((==))(i, m));
            })))));
    (match (z) {
      (True() : bool )
         -> resume(m);
      (@skip False() : bool )
         -> @open(cheat)(p);
    });
  }))))}
Evaluating: 3 nim:721:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(721:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:721,3)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:722 1 @open(clause-control2)((fn(p, n, resume){
  val m : int
        = (@open(move)(p, n));
  val z : bool
        = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
            (@open((==))(i, m));
          })))));
  (match (z) {
    (True() : bool )
       -> resume(m);
    (@skip False() : bool )
       -> @open(cheat)(p);
  });
}))], resolvedArgs = [BI@(723:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:716 0 @Hnd-move(3, (@open(clause-control2)((fn(p, n, resume){
    val m : int
          = (@open(move)(p, n));
    val z : bool
          = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
              (@open((==))(i, m));
            })))));
    (match (z) {
      (True() : bool )
         -> resume(m);
      (@skip False() : bool )
         -> @open(cheat)(p);
    });
  }))))}
Evaluating: @open(clause-control2)((fn(p, n, resume){
  val m : int
        = (@open(move)(p, n));
  val z : bool
        = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
            (@open((==))(i, m));
          })))));
  (match (z) {
    (True() : bool )
       -> resume(m);
    (@skip False() : bool )
       -> @open(cheat)(p);
  });
})) nim:722:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: clause-control2 nim:728:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: clause-control2 nim:730:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(730:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/clause-control2
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:726 0 fn(p, n, resume){
  val m : int
        = @open(move)(p, n);
  val z : bool
        = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
            (@open((==))(i, m));
          }))));
  match (z) {
    (True() : bool )
       -> resume(m);
    (@skip False() : bool )
       -> @open(cheat)(p);
  };
}], resolvedArgs = [], parent = AppParam nim:722 1 @open(clause-control2)((fn(p, n, resume){
  val m : int
        = (@open(move)(p, n));
  val z : bool
        = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
            (@open((==))(i, m));
          })))));
  (match (z) {
    (True() : bool )
       -> resume(m);
    (@skip False() : bool )
       -> @open(cheat)(p);
  });
}))}
Evaluating: fn(p, n, resume){
  val m : int
        = @open(move)(p, n);
  val z : bool
        = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
            (@open((==))(i, m));
          }))));
  match (z) {
    (True() : bool )
       -> resume(m);
    (@skip False() : bool )
       -> @open(cheat)(p);
  };
} nim:726:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(726:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(p, n, resume){
  val m : int
        = @open(move)(p, n);
  val z : bool
        = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
            (@open((==))(i, m));
          }))));
  match (z) {
    (True() : bool )
       -> resume(m);
    (@skip False() : bool )
       -> @open(cheat)(p);
  };
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(730:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:722 1 @open(clause-control2)((fn(p, n, resume){
  val m : int
        = (@open(move)(p, n));
  val z : bool
        = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
            (@open((==))(i, m));
          })))));
  (match (z) {
    (True() : bool )
       -> resume(m);
    (@skip False() : bool )
       -> @open(cheat)(p);
  });
}))}
Extending store: CI@(clause-control21 722:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(p, n, resume){
  val m : int
        = @open(move)(p, n);
  val z : bool
        = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
            (@open((==))(i, m));
          }))));
  match (z) {
    (True() : bool )
       -> resume(m);
    (@skip False() : bool )
       -> @open(cheat)(p);
  };
})
Extending store: BI@(722:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/clause-control2([(,CI@(clause-control21 722:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(723:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(721:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:716 0 @Hnd-move(3, (@open(clause-control2)((fn(p, n, resume){
    val m : int
          = (@open(move)(p, n));
    val z : bool
          = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
              (@open((==))(i, m));
            })))));
    (match (z) {
      (True() : bool )
         -> resume(m);
      (@skip False() : bool )
         -> @open(cheat)(p);
    });
  }))))}
Extending store: CI@(@cfc 716:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:721,3)
Extending store: CI@(@ctl-move 716:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/clause-control2([(,CI@(clause-control21 722:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(716:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with analysis/benchmarks/handlers/nim/@Hnd-move([(@cfc,CI@(@cfc 716:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(@ctl-move,CI@(@ctl-move 716:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam nim:717 1 fn(@res){
  @res;
},AppParam nim:718 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/nim/#move/@handle], parent = LamBody [@action] move/@handle((@Hnd-move(3, (@open(clause-control2)((fn(p, n, resume){
      val m : int
            = (@open(move)(p, n));
      val z : bool
            = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
                (@open((==))(i, m));
              })))));
      (match (z) {
        (True() : bool )
           -> resume(m);
        (@skip False() : bool )
           -> @open(cheat)(p);
      });
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} nim:717:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(717:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(@res){
  @res;
})
Applying FApp {totalArgs = 3, leftArgs = [AppParam nim:718 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/nim/#move/@handle,BI@(716:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [@action] move/@handle((@Hnd-move(3, (@open(clause-control2)((fn(p, n, resume){
      val m : int
            = (@open(move)(p, n));
      val z : bool
            = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
                (@open((==))(i, m));
              })))));
      (match (z) {
        (True() : bool )
           -> resume(m);
        (@skip False() : bool )
           -> @open(cheat)(p);
      });
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action nim:718:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/#move/@handle,BI@(716:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(717:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [@action] move/@handle((@Hnd-move(3, (@open(clause-control2)((fn(p, n, resume){
      val m : int
            = (@open(move)(p, n));
      val z : bool
            = (@open(bool)((find((@open(valid-moves)(n)), (fn(i){
                (@open((==))(i, m));
              })))));
      (match (z) {
        (True() : bool )
           -> resume(m);
        (@skip False() : bool )
           -> @open(cheat)(p);
      });
    }))))), (fn(@res){
    @res;
  }), @action)}
Extending store: B@(hnd:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with analysis/benchmarks/handlers/nim/@Hnd-move([(@cfc,CI@(@cfc 716:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(@ctl-move,CI@(@ctl-move 716:d_[a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(ret:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(@res){
  @res;
})
Extending store: B@(action:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(){
  @open(game)(7);
})
Evaluating: @hhandle(move/@tag, hnd, ret, action) nim:185:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @hhandle nim:186:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @hhandle nim:191:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(191:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@hhandle
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:187 0 move/@tag,AppParam nim:188 1 hnd,AppParam nim:189 2 ret,AppParam nim:190 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(move/@tag, hnd, ret, action)}
Evaluating: move/@tag nim:187:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:188 1 hnd,AppParam nim:189 2 ret,AppParam nim:190 3 action], resolvedArgs = [BI@(191:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [hnd,ret,action] @hhandle(move/@tag, hnd, ret, action)}
Evaluating: hnd nim:188:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:189 2 ret,AppParam nim:190 3 action], resolvedArgs = [BI@(191:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@tag], parent = LamBody [hnd,ret,action] @hhandle(move/@tag, hnd, ret, action)}
Evaluating: ret nim:189:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:190 3 action], resolvedArgs = [BI@(191:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@tag,B@(hnd:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [hnd,ret,action] @hhandle(move/@tag, hnd, ret, action)}
Evaluating: action nim:190:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(191:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@tag,B@(hnd:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(ret:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [hnd,ret,action] @hhandle(move/@tag, hnd, ret, action)}
Evaluating: @open(game)(7) nim:804:d_[delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: game nim:808:d_[delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: fn(n){
  @open(alice-turn)(n);
} nim:26:t_[top]@[]
Extending store: BI@(26:t_[top]@[]) with DefNonRec(game)
Extending store: T@analysis/benchmarks/handlers/nim/game with DefNonRec(game)
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:806 0 7], resolvedArgs = [], parent = LamBody [] @open(game)(7)}
Evaluating: 7 nim:806:d_[delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(806:d_[delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/game], parent = LamBody [] @open(game)(7)}
Extending store: B@(n:d_[a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Evaluating: @open(alice-turn)(n) nim:298:d_[a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: alice-turn nim:302:d_[a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: fn(n){
  match ((@open((<=))(n, 0))) {
    (True() : bool )
       -> Bob;
    (@skip False() : bool )
       -> @open(bob-turn)((@open((-))(n, (@open(move)(Alice, n)))));
  };
} nim:23:t_[top]@[]
Extending store: BI@(23:t_[top]@[]) with DefRec(alice-turn)
Extending store: T@analysis/benchmarks/handlers/nim/alice-turn with DefRec(alice-turn)
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:300 0 n], resolvedArgs = [], parent = LamBody [n] @open(alice-turn)(n)}
Evaluating: n nim:300:d_[a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/alice-turn], parent = LamBody [n] @open(alice-turn)(n)}
Extending store: B@(n:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Evaluating: match ((@open((<=))(n, 0))) {
  (True() : bool )
     -> Bob;
  (@skip False() : bool )
     -> @open(bob-turn)((@open((-))(n, (@open(move)(Alice, n)))));
} nim:224:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open((<=))(n, 0) nim:225:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (<=) nim:232:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(232:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(<=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:229 0 n,AppParam nim:230 1 0], resolvedArgs = [], parent = CaseMatch @open((<=))(n, 0)}
Evaluating: n nim:229:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:230 1 0], resolvedArgs = [BI@(232:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch @open((<=))(n, 0)}
Evaluating: 0 nim:230:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(230:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:230,0)
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(232:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(n:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch @open((<=))(n, 0)}
Extending store: BI@(225:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with False
Applying FScrut {parent = LamBody [n] match ((@open((<=))(n, 0))) {
  (True() : bool )
     -> Bob;
  (@skip False() : bool )
     -> @open(bob-turn)((@open((-))(n, (@open(move)(Alice, n)))));
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> analysis/benchmarks/handlers/nim/Bob;,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/bob-turn)((std/core/types/@open(std/core/int/(-))(n, (std/core/types/@open(analysis/benchmarks/handlers/nim/move)(analysis/benchmarks/handlers/nim/Alice, n)))));]}
Evaluating: @open(bob-turn)((@open((-))(n, (@open(move)(Alice, n))))) nim:227:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: bob-turn nim:241:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: fn(n){
  match ((@open((<=))(n, 0))) {
    (True() : bool )
       -> Alice;
    (@skip False() : bool )
       -> @open(alice-turn)((@open((-))(n, (@open(move)(Bob, n)))));
  };
} nim:24:t_[top]@[]
Extending store: BI@(24:t_[top]@[]) with DefRec(bob-turn)
Extending store: T@analysis/benchmarks/handlers/nim/bob-turn with DefRec(bob-turn)
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:239 0 @open((-))(n, (@open(move)(Alice, n)))], resolvedArgs = [], parent = CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/bob-turn)((std/core/types/@open(std/core/int/(-))(n, (std/core/types/@open(analysis/benchmarks/handlers/nim/move)(analysis/benchmarks/handlers/nim/Alice, n)))));}
Evaluating: @open((-))(n, (@open(move)(Alice, n))) nim:239:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (-) nim:248:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: fn(x, y){
  @open(int-sub)(x, y);
} int:1662:t_[top]@[]
Extending store: BI@(1662:t_[top]@[]) with DefNonRec((-))
Extending store: T@std/core/int/(-) with DefNonRec((-))
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:245 0 n,AppParam nim:246 1 @open(move)(Alice, n)], resolvedArgs = [], parent = AppParam nim:239 0 @open((-))(n, (@open(move)(Alice, n)))}
Evaluating: n nim:245:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:246 1 @open(move)(Alice, n)], resolvedArgs = [T@std/core/int/(-)], parent = AppParam nim:239 0 @open((-))(n, (@open(move)(Alice, n)))}
Evaluating: @open(move)(Alice, n) nim:246:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move nim:256:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: fn(player, sticks){
  @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks);
} nim:21:t_[top]@[]
Extending store: BI@(21:t_[top]@[]) with DefNonRec(move)
Extending store: T@analysis/benchmarks/handlers/nim/move with DefNonRec(move)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:253 0 Alice,AppParam nim:254 1 n], resolvedArgs = [], parent = AppParam nim:246 1 @open(move)(Alice, n)}
Evaluating: Alice nim:253:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(253:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:254 1 n], resolvedArgs = [T@analysis/benchmarks/handlers/nim/move], parent = AppParam nim:246 1 @open(move)(Alice, n)}
Evaluating: n nim:254:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/move,BI@(253:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:246 1 @open(move)(Alice, n)}
Extending store: B@(player:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Extending store: B@(sticks:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Evaluating: @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks) nim:201:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform2 nim:202:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform2 nim:207:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(207:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@perform2
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam nim:204 1 forall<e,a> move/@select,AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) nim:203:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:211:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:213:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(213:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:209 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) nim:209:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @make-ssize_t nim:217:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(217:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:215 0 0], resolvedArgs = [], parent = AppParam nim:209 0 @open(@make-ssize_t)(0)}
Evaluating: 0 nim:215:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(215:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(217:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:209 0 @open(@make-ssize_t)(0)}
Extending store: BI@(209:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(213:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Extending store: CI@(@evv-at1 203:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Extending store: BI@(203:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at([(,CI@(@evv-at1 203:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:204 1 forall<e,a> move/@select,AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: forall<e,a> move/@select nim:204:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move/@select nim:221:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-move(_, (@ctl-move)) : analysis/benchmarks/handlers/nim/move<e,a> )
       -> @ctl-move;
  });
} nim:19:t_[top]@[]
Extending store: BI@(19:t_[top]@[]) with DefNonRec(move/@select)
Extending store: T@analysis/benchmarks/handlers/nim/#move/@select with DefNonRec(move/@select)
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: player nim:205:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@select], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: sticks nim:206:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(207:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@select,B@(player:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Extending store: B@(p:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Extending store: B@(n:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Extending store: B@(resume:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Kont(analysis/benchmarks/handlers/nim/move,AI@(201:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])],Handler {ops = B@(hnd:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), ret = Just AppParam nim:717 1 fn(@res){
  @res;
}})
Evaluating: val m : int
      = @open(move)(p, n);
val z : bool
      = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
          (@open((==))(i, m));
        }))));
match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
} nim:731:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open(move)(p, n) nim:733:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move nim:784:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:781 0 p,AppParam nim:782 1 n], resolvedArgs = [], parent = LetDef val m : int;}
Evaluating: p nim:781:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:782 1 n], resolvedArgs = [T@analysis/benchmarks/handlers/nim/move], parent = LetDef val m : int;}
Evaluating: n nim:782:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/move,B@(p:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LetDef val m : int;}
Extending store: B@(player:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Extending store: B@(sticks:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Evaluating: @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks) nim:201:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform2 nim:202:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform2 nim:207:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(207:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@perform2
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam nim:204 1 forall<e,a> move/@select,AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) nim:203:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:211:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:213:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(213:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:209 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) nim:209:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @make-ssize_t nim:217:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(217:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:215 0 0], resolvedArgs = [], parent = AppParam nim:209 0 @open(@make-ssize_t)(0)}
Evaluating: 0 nim:215:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(215:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(217:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:209 0 @open(@make-ssize_t)(0)}
Extending store: BI@(209:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(213:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Extending store: CI@(@evv-at1 203:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Extending store: BI@(203:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at([(,CI@(@evv-at1 203:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:204 1 forall<e,a> move/@select,AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: forall<e,a> move/@select nim:204:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move/@select nim:221:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: player nim:205:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@select], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: sticks nim:206:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(207:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@select,B@(player:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Extending store: B@(_p:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Extending store: B@(n:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Evaluating: @open(max)(1, (@open((%))(n, 4))) nim:323:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: max nim:328:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: fn(i, j){
  match ((@open((>=))(i, j))) {
    (True() : bool )
       -> i;
    (@skip False() : bool )
       -> j;
  };
} int:1702:t_[top]@[]
Extending store: BI@(1702:t_[top]@[]) with DefNonRec(max)
Extending store: T@std/core/int/max with DefNonRec(max)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:325 0 1,AppParam nim:326 1 @open((%))(n, 4)], resolvedArgs = [], parent = LamBody [_p,n] @open(max)(1, (@open((%))(n, 4)))}
Evaluating: 1 nim:325:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(325:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,1)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:326 1 @open((%))(n, 4)], resolvedArgs = [T@std/core/int/max], parent = LamBody [_p,n] @open(max)(1, (@open((%))(n, 4)))}
Evaluating: @open((%))(n, 4) nim:326:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (%) nim:336:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(336:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(%)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:333 0 n,AppParam nim:334 1 4], resolvedArgs = [], parent = AppParam nim:326 1 @open((%))(n, 4)}
Evaluating: n nim:333:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:334 1 4], resolvedArgs = [BI@(336:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:326 1 @open((%))(n, 4)}
Evaluating: 4 nim:334:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(334:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(336:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(n:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:326 1 @open((%))(n, 4)}
Extending store: BI@(326:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,3)
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/max,BI@(325:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [_p,n] @open(max)(1, (@open((%))(n, 4)))}
Extending store: B@(i:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,1)
Extending store: B@(j:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,3)
Evaluating: match ((@open((>=))(i, j))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> j;
} int:1725:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open((>=))(i, j) int:1726:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (>=) int:1733:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1733:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(>=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:1730 0 i,AppParam int:1731 1 j], resolvedArgs = [], parent = CaseMatch @open((>=))(i, j)}
Evaluating: i int:1730:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:1731 1 j], resolvedArgs = [BI@(1733:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch @open((>=))(i, j)}
Evaluating: j int:1731:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1733:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(i:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch @open((>=))(i, j)}
Extending store: BI@(1726:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with False
Applying FScrut {parent = LamBody [i,j] match ((@open((>=))(i, j))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> j;
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> i;,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> j;]}
Evaluating: j int:1728:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FResume {label = analysis/benchmarks/handlers/nim/move, vaddr = IL@(201:move:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), rHnd = Handler {ops = B@(hnd:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]), ret = Just AppParam nim:309 1 fn(@res){
  @res;
}}, rCtx = nim:323}
Applying FHLink {linkEff = analysis/benchmarks/handlers/nim/cheat, doCtx = nim:201, hCtx = nim:633, linkKnext = AI@(201:d_[a733,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), linkHnd = Handler {ops = B@(hnd:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), ret = Just AppParam nim:673 1 fn(@res){
  @res;
}}}
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = m, resolved = [], parent = LamBody [p,n,resume] val m : int
      = @open(move)(p, n);
val z : bool
      = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
          (@open((==))(i, m));
        }))));
match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
}}
Extending store: B@(m:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,3)
Extending store: B@(n:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Extending store: B@(p:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Extending store: B@(resume:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Kont(analysis/benchmarks/handlers/nim/move,AI@(201:d_[a246,a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])],Handler {ops = B@(hnd:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), ret = Just AppParam nim:717 1 fn(@res){
  @res;
}})
Evaluating: val z : bool
      = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
          (@open((==))(i, m));
        }))));
match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
} nim:734:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open(bool)((find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  })))) nim:736:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: bool nim:756:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: bool nim:758:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a> fn(mb){
  (match (mb) {
    (Just(_) : maybe<a> )
       -> True;
    (@skip Nothing() : (maybe<a>) )
       -> False;
  });
} maybe:1756:t_[top]@[]
Extending store: BI@(1756:t_[top]@[]) with DefNonRec(bool)
Extending store: T@std/core/maybe/bool with DefNonRec(bool)
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:754 0 find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  }))], resolvedArgs = [], parent = LetDef val z : bool;}
Evaluating: find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  })) nim:754:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: find nim:759:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: find nim:762:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a,e> fn(xs, pred){
  foreach-while(xs, (fn(x){
      (match ((pred(x))) {
        (True() : bool )
           -> Just(x);
        (@skip False() : bool )
           -> Nothing;
      });
    }));
} list:1807:t_[top]@[]
Extending store: BI@(1807:t_[top]@[]) with DefNonRec(find)
Extending store: T@std/core/list/find with DefNonRec(find)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:760 0 @open(valid-moves)(n),AppParam nim:761 1 fn(i){
  @open((==))(i, m);
}], resolvedArgs = [], parent = AppParam nim:754 0 find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  }))}
Evaluating: @open(valid-moves)(n) nim:760:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: valid-moves nim:766:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: fn(n){
  filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
      (@open((<=))(m, n));
    }));
} nim:40:t_[top]@[]
Extending store: BI@(40:t_[top]@[]) with DefNonRec(valid-moves)
Extending store: T@analysis/benchmarks/handlers/nim/valid-moves with DefNonRec(valid-moves)
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:764 0 n], resolvedArgs = [], parent = AppParam nim:760 0 @open(valid-moves)(n)}
Evaluating: n nim:764:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/valid-moves], parent = AppParam nim:760 0 @open(valid-moves)(n)}
Extending store: B@(n:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Evaluating: filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
    (@open((<=))(m, n));
  })) nim:389:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter nim:390:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter nim:393:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a,e> fn(xs, pred){
  (match (xs) {
    (Cons((x), (xx)) : list<a> )
       -> (match ((pred(x))) {
        (True() : bool )
           -> Cons(x, (filter(xx, pred)));
        (@skip False() : bool )
           -> filter(xx, pred);
      });
    (@skip Nil() : (list<a>) )
       -> Nil;
  });
} list:1801:t_[top]@[]
Extending store: BI@(1801:t_[top]@[]) with DefRec(filter)
Extending store: T@std/core/list/filter with DefRec(filter)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:391 0 Cons(1, (Cons(2, (Cons(3, Nil))))),AppParam nim:392 1 fn(m){
  @open((<=))(m, n);
}], resolvedArgs = [], parent = LamBody [n] filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
    (@open((<=))(m, n));
  }))}
Evaluating: Cons(1, (Cons(2, (Cons(3, Nil))))) nim:391:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:394:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:397:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(397:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:395 0 1,AppParam nim:396 1 Cons(2, (Cons(3, Nil)))], resolvedArgs = [], parent = AppParam nim:391 0 Cons(1, (Cons(2, (Cons(3, Nil)))))}
Evaluating: 1 nim:395:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(395:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:396 1 Cons(2, (Cons(3, Nil)))], resolvedArgs = [BI@(397:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:391 0 Cons(1, (Cons(2, (Cons(3, Nil)))))}
Evaluating: Cons(2, (Cons(3, Nil))) nim:396:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:399:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:402:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(402:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:400 0 2,AppParam nim:401 1 Cons(3, Nil)], resolvedArgs = [], parent = AppParam nim:396 1 Cons(2, (Cons(3, Nil)))}
Evaluating: 2 nim:400:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(400:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:401 1 Cons(3, Nil)], resolvedArgs = [BI@(402:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:396 1 Cons(2, (Cons(3, Nil)))}
Evaluating: Cons(3, Nil) nim:401:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:404:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:407:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(407:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:405 0 3,AppParam nim:406 1 Nil], resolvedArgs = [], parent = AppParam nim:401 1 Cons(3, Nil)}
Evaluating: 3 nim:405:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(405:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:406 1 Nil], resolvedArgs = [BI@(407:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:401 1 Cons(3, Nil)}
Evaluating: Nil nim:406:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Nil nim:409:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(409:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(407:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(405:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:401 1 Cons(3, Nil)}
Extending store: CI@(head 401:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: CI@(tail 401:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Extending store: BI@(401:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 401:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 401:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(402:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(400:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:396 1 Cons(2, (Cons(3, Nil)))}
Extending store: CI@(head 396:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: CI@(tail 396:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 401:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 401:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(396:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 396:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 396:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(397:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(395:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:391 0 Cons(1, (Cons(2, (Cons(3, Nil)))))}
Extending store: CI@(head 391:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: CI@(tail 391:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 396:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 396:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(391:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 391:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 391:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:392 1 fn(m){
  @open((<=))(m, n);
}], resolvedArgs = [T@std/core/list/filter], parent = LamBody [n] filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
    (@open((<=))(m, n));
  }))}
Evaluating: fn(m){
  @open((<=))(m, n);
} nim:392:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(392:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/filter,BI@(391:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [n] filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
    (@open((<=))(m, n));
  }))}
Extending store: B@(xs:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 391:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 391:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(pred:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
} list:1916:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1917:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,pred] match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
}, branches = [CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });,CaseBranch 1 (@skip std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nil;]}
Extending store: B@(x:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(xx:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 396:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 396:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Cons(x, (filter(xx, pred)));
  (@skip False() : bool )
     -> filter(xx, pred);
} list:1918:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1920:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1923:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1924 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1924:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(m:d_[a1920,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(n:d_[a1920,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Evaluating: @open((<=))(m, n) nim:410:d_[a1920,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (<=) nim:415:d_[a1920,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(415:d_[a1920,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(<=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:412 0 m,AppParam nim:413 1 n], resolvedArgs = [], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: m nim:412:d_[a1920,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:413 1 n], resolvedArgs = [BI@(415:d_[a1920,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: n nim:413:d_[a1920,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(415:d_[a1920,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(m:d_[a1920,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Extending store: BI@(410:d_[a1920,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FScrut {parent = CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/list/filter(xx, pred);]}
Evaluating: Cons(x, (filter(xx, pred))) list:1921:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1925:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1928:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1928:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1926 0 x,AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: x list:1926:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [BI@(1928:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: filter(xx, pred) list:1927:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1929:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1932:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1930 0 xx,AppParam list:1931 1 pred], resolvedArgs = [], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: xx list:1930:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1931 1 pred], resolvedArgs = [T@std/core/list/filter], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: pred list:1931:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/filter,B@(xx:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam list:1927 1 filter(xx, pred)}
Extending store: B@(xs:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 396:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 396:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(pred:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
} list:1916:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1917:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,pred] match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
}, branches = [CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });,CaseBranch 1 (@skip std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nil;]}
Extending store: B@(x:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: B@(xx:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 401:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 401:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Cons(x, (filter(xx, pred)));
  (@skip False() : bool )
     -> filter(xx, pred);
} list:1918:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1920:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1923:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1924 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1924:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(m:d_[a1920,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: B@(n:d_[a1920,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Evaluating: @open((<=))(m, n) nim:410:d_[a1920,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (<=) nim:415:d_[a1920,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(415:d_[a1920,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(<=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:412 0 m,AppParam nim:413 1 n], resolvedArgs = [], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: m nim:412:d_[a1920,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:413 1 n], resolvedArgs = [BI@(415:d_[a1920,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: n nim:413:d_[a1920,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(415:d_[a1920,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(m:d_[a1920,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Extending store: BI@(410:d_[a1920,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FScrut {parent = CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/list/filter(xx, pred);]}
Evaluating: Cons(x, (filter(xx, pred))) list:1921:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1925:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1928:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1928:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1926 0 x,AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: x list:1926:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [BI@(1928:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: filter(xx, pred) list:1927:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1929:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1932:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1930 0 xx,AppParam list:1931 1 pred], resolvedArgs = [], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: xx list:1930:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1931 1 pred], resolvedArgs = [T@std/core/list/filter], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: pred list:1931:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/filter,B@(xx:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam list:1927 1 filter(xx, pred)}
Extending store: B@(xs:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 401:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 401:d_[a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(pred:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
} list:1916:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1917:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,pred] match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
}, branches = [CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });,CaseBranch 1 (@skip std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nil;]}
Extending store: B@(x:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: B@(xx:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Cons(x, (filter(xx, pred)));
  (@skip False() : bool )
     -> filter(xx, pred);
} list:1918:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1920:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1923:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1924 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1924:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(m:d_[a1920,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: B@(n:d_[a1920,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Evaluating: @open((<=))(m, n) nim:410:d_[a1920,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (<=) nim:415:d_[a1920,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(415:d_[a1920,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(<=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:412 0 m,AppParam nim:413 1 n], resolvedArgs = [], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: m nim:412:d_[a1920,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:413 1 n], resolvedArgs = [BI@(415:d_[a1920,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: n nim:413:d_[a1920,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(415:d_[a1920,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(m:d_[a1920,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Extending store: BI@(410:d_[a1920,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FScrut {parent = CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/list/filter(xx, pred);]}
Evaluating: Cons(x, (filter(xx, pred))) list:1921:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1925:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1928:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1928:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1926 0 x,AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: x list:1926:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [BI@(1928:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: filter(xx, pred) list:1927:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1929:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1932:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1930 0 xx,AppParam list:1931 1 pred], resolvedArgs = [], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: xx list:1930:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1931 1 pred], resolvedArgs = [T@std/core/list/filter], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: pred list:1931:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/filter,B@(xx:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam list:1927 1 filter(xx, pred)}
Extending store: B@(xs:d_[a1927,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Extending store: B@(pred:d_[a1927,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
} list:1916:d_[a1927,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1917:d_[a1927,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,pred] match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
}, branches = [CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });,CaseBranch 1 (@skip std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nil;]}
Evaluating: Nil list:1919:d_[a1927,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Nil list:1933:d_[a1927,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1933:d_[a1927,a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1928:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(x:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Extending store: CI@(head 1921:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: CI@(tail 1921:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Extending store: BI@(1921:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1928:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(x:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Extending store: CI@(head 1921:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: CI@(tail 1921:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(1921:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1928:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(x:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Extending store: CI@(head 1921:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: CI@(tail 1921:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(1921:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:761 1 fn(i){
  @open((==))(i, m);
}], resolvedArgs = [T@std/core/list/find], parent = AppParam nim:754 0 find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  }))}
Evaluating: fn(i){
  @open((==))(i, m);
} nim:761:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(761:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(i){
  @open((==))(i, m);
})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/find,BI@(1921:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:754 0 find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  }))}
Extending store: B@(xs:d_[a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(pred:d_[a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(i){
  @open((==))(i, m);
})
Evaluating: foreach-while(xs, (fn(x){
    (match ((pred(x))) {
      (True() : bool )
         -> Just(x);
      (@skip False() : bool )
         -> Nothing;
    });
  })) list:1934:d_[a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1935:d_[a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1938:d_[a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a,b,e> fn(xs, action){
  (match (xs) {
    (Nil() : (list<a>) )
       -> Nothing;
    (@skip Cons((x), (xx)) : list<a> )
       -> (match ((action(x))) {
        (Nothing() : (maybe<b>) )
           -> foreach-while(xx, action);
        (just)
           -> just;
      });
  });
} list:1805:t_[top]@[]
Extending store: BI@(1805:t_[top]@[]) with DefRec(foreach-while)
Extending store: T@std/core/list/foreach-while with DefRec(foreach-while)
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1936 0 xs,AppParam list:1937 1 fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
}], resolvedArgs = [], parent = LamBody [xs,pred] foreach-while(xs, (fn(x){
    (match ((pred(x))) {
      (True() : bool )
         -> Just(x);
      (@skip False() : bool )
         -> Nothing;
    });
  }))}
Evaluating: xs list:1936:d_[a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1937 1 fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
}], resolvedArgs = [T@std/core/list/foreach-while], parent = LamBody [xs,pred] foreach-while(xs, (fn(x){
    (match ((pred(x))) {
      (True() : bool )
         -> Just(x);
      (@skip False() : bool )
         -> Nothing;
    });
  }))}
Evaluating: fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
} list:1937:d_[a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1937:d_[a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/foreach-while,B@(xs:d_[a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [xs,pred] foreach-while(xs, (fn(x){
    (match ((pred(x))) {
      (True() : bool )
         -> Just(x);
      (@skip False() : bool )
         -> Nothing;
    });
  }))}
Extending store: B@(xs:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(action:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
})
Evaluating: match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
} list:1939:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1940:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,action] match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
}, branches = [CaseBranch 0 (std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nothing;,CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });]}
Extending store: B@(x:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(xx:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: match ((action(x))) {
  (Nothing() : (maybe<a>) )
     -> foreach-while(xx, action);
  (just)
     -> just;
} list:1942:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action(x) list:1943:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action list:1946:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1947 0 x], resolvedArgs = [], parent = CaseMatch action(x)}
Evaluating: x list:1947:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(action:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch action(x)}
Extending store: B@(x:d_[a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(pred:d_[a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(i){
  @open((==))(i, m);
})
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Just(x);
  (@skip False() : bool )
     -> Nothing;
} list:1948:d_[a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1949:d_[a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1952:d_[a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1953 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1953:d_[a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(i:d_[a1949,a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(m:d_[a1949,a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,3)
Evaluating: @open((==))(i, m) nim:770:d_[a1949,a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (==) nim:775:d_[a1949,a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(775:d_[a1949,a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(==)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:772 0 i,AppParam nim:773 1 m], resolvedArgs = [], parent = LamBody [i] @open((==))(i, m)}
Evaluating: i nim:772:d_[a1949,a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:773 1 m], resolvedArgs = [BI@(775:d_[a1949,a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [i] @open((==))(i, m)}
Evaluating: m nim:773:d_[a1949,a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(775:d_[a1949,a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(i:d_[a1949,a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [i] @open((==))(i, m)}
Extending store: BI@(770:d_[a1949,a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with False
Applying FScrut {parent = LamBody [x] match ((pred(x))) {
  (True() : bool )
     -> Just(x);
  (@skip False() : bool )
     -> Nothing;
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Just(x);,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/Nothing;]}
Evaluating: Nothing list:1951:d_[a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Nothing list:1954:d_[a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1954:d_[a1943,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nothing
Applying FScrut {parent = CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });, branches = [CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);,CaseBranch 1 (just)
   -> just;]}
Evaluating: foreach-while(xx, action) list:1944:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1955:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1958:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1956 0 xx,AppParam list:1957 1 action], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);}
Evaluating: xx list:1956:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1957 1 action], resolvedArgs = [T@std/core/list/foreach-while], parent = CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);}
Evaluating: action list:1957:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/foreach-while,B@(xx:d_[a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);}
Extending store: B@(xs:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(action:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
})
Evaluating: match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
} list:1939:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1940:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,action] match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
}, branches = [CaseBranch 0 (std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nothing;,CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });]}
Extending store: B@(x:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: B@(xx:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: match ((action(x))) {
  (Nothing() : (maybe<a>) )
     -> foreach-while(xx, action);
  (just)
     -> just;
} list:1942:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action(x) list:1943:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action list:1946:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1947 0 x], resolvedArgs = [], parent = CaseMatch action(x)}
Evaluating: x list:1947:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(action:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch action(x)}
Extending store: B@(x:d_[a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: B@(pred:d_[a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(i){
  @open((==))(i, m);
})
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Just(x);
  (@skip False() : bool )
     -> Nothing;
} list:1948:d_[a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1949:d_[a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1952:d_[a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1953 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1953:d_[a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(i:d_[a1949,a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: B@(m:d_[a1949,a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,3)
Evaluating: @open((==))(i, m) nim:770:d_[a1949,a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (==) nim:775:d_[a1949,a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(775:d_[a1949,a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(==)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:772 0 i,AppParam nim:773 1 m], resolvedArgs = [], parent = LamBody [i] @open((==))(i, m)}
Evaluating: i nim:772:d_[a1949,a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:773 1 m], resolvedArgs = [BI@(775:d_[a1949,a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [i] @open((==))(i, m)}
Evaluating: m nim:773:d_[a1949,a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(775:d_[a1949,a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(i:d_[a1949,a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [i] @open((==))(i, m)}
Extending store: BI@(770:d_[a1949,a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with False
Applying FScrut {parent = LamBody [x] match ((pred(x))) {
  (True() : bool )
     -> Just(x);
  (@skip False() : bool )
     -> Nothing;
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Just(x);,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/Nothing;]}
Evaluating: Nothing list:1951:d_[a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Nothing list:1954:d_[a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1954:d_[a1943,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nothing
Applying FScrut {parent = CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });, branches = [CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);,CaseBranch 1 (just)
   -> just;]}
Evaluating: foreach-while(xx, action) list:1944:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1955:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1958:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1956 0 xx,AppParam list:1957 1 action], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);}
Evaluating: xx list:1956:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1957 1 action], resolvedArgs = [T@std/core/list/foreach-while], parent = CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);}
Evaluating: action list:1957:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/foreach-while,B@(xx:d_[a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);}
Extending store: B@(xs:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a1927,a389,a760,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(action:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
})
Evaluating: match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
} list:1939:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1940:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,action] match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
}, branches = [CaseBranch 0 (std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nothing;,CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });]}
Extending store: B@(x:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: B@(xx:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Evaluating: match ((action(x))) {
  (Nothing() : (maybe<a>) )
     -> foreach-while(xx, action);
  (just)
     -> just;
} list:1942:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action(x) list:1943:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action list:1946:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1947 0 x], resolvedArgs = [], parent = CaseMatch action(x)}
Evaluating: x list:1947:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(action:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch action(x)}
Extending store: B@(x:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: B@(pred:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(i){
  @open((==))(i, m);
})
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Just(x);
  (@skip False() : bool )
     -> Nothing;
} list:1948:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1949:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1952:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1953 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1953:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(i:d_[a1949,a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: B@(m:d_[a1949,a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,3)
Evaluating: @open((==))(i, m) nim:770:d_[a1949,a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (==) nim:775:d_[a1949,a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(775:d_[a1949,a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(==)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:772 0 i,AppParam nim:773 1 m], resolvedArgs = [], parent = LamBody [i] @open((==))(i, m)}
Evaluating: i nim:772:d_[a1949,a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:773 1 m], resolvedArgs = [BI@(775:d_[a1949,a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [i] @open((==))(i, m)}
Evaluating: m nim:773:d_[a1949,a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(775:d_[a1949,a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(i:d_[a1949,a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [i] @open((==))(i, m)}
Extending store: BI@(770:d_[a1949,a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FScrut {parent = LamBody [x] match ((pred(x))) {
  (True() : bool )
     -> Just(x);
  (@skip False() : bool )
     -> Nothing;
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Just(x);,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/Nothing;]}
Evaluating: Just(x) list:1950:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Just list:1959:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Just list:1961:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1961:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Just
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1960 0 x], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Just(x);}
Evaluating: x list:1960:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(1961:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Just(x);}
Extending store: CI@(value 1950:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: BI@(1950:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Just([(value,CI@(value 1950:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FScrut {parent = CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });, branches = [CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);,CaseBranch 1 (just)
   -> just;]}
Extending store: B@(just:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Just([(value,CI@(value 1950:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: just list:1945:d_[a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/maybe/bool], parent = LetDef val z : bool;}
Extending store: B@(mb:d_[a736,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Just([(value,CI@(value 1950:d_[a1943,a1944,a1944,a1934,a754,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: match (mb) {
  (Just(_) : maybe<a> )
     -> True;
  (@skip Nothing() : (maybe<a>) )
     -> False;
} maybe:1962:d_[a736,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: mb maybe:1963:d_[a736,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [mb] match (mb) {
  (Just(_) : maybe<a> )
     -> True;
  (@skip Nothing() : (maybe<a>) )
     -> False;
}, branches = [CaseBranch 0 (std/core/types/Just(_) : maybe<a> )
   -> std/core/types/True;,CaseBranch 1 (@skip std/core/types/Nothing() : (maybe<a>) )
   -> std/core/types/False;]}
Evaluating: True maybe:1964:d_[a736,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1964:d_[a736,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = z, resolved = [], parent = LetBody val z : bool
      = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
          (@open((==))(i, m));
        }))));
match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
}}
Extending store: B@(z:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Evaluating: match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
} nim:737:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: z nim:738:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LetBody match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> resume(m);,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/cheat)(p);]}
Evaluating: resume(m) nim:739:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: resume nim:742:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:743 0 m], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> resume(m);}
Evaluating: m nim:743:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> resume(m);}
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/(-),B@(n:d_[a298,a804,delim]@[(nim:185,d_[a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:239 0 @open((-))(n, (@open(move)(Alice, n)))}
Extending store: B@(x:d_[a239,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:806,7)
Extending store: B@(y:d_[a239,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,3)
Evaluating: @open(int-sub)(x, y) int:1966:d_[a239,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: int-sub int:1971:d_[a239,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1971:d_[a239,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/int-sub
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:1968 0 x,AppParam int:1969 1 y], resolvedArgs = [], parent = LamBody [x,y] @open(int-sub)(x, y)}
Evaluating: x int:1968:d_[a239,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:1969 1 y], resolvedArgs = [BI@(1971:d_[a239,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [x,y] @open(int-sub)(x, y)}
Evaluating: y int:1969:d_[a239,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1971:d_[a239,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(x:d_[a239,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [x,y] @open(int-sub)(x, y)}
Extending store: BI@(1966:d_[a239,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/bob-turn], parent = CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/bob-turn)((std/core/types/@open(std/core/int/(-))(n, (std/core/types/@open(analysis/benchmarks/handlers/nim/move)(analysis/benchmarks/handlers/nim/Alice, n)))));}
Extending store: B@(n:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Evaluating: match ((@open((<=))(n, 0))) {
  (True() : bool )
     -> Alice;
  (@skip False() : bool )
     -> @open(alice-turn)((@open((-))(n, (@open(move)(Bob, n)))));
} nim:261:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open((<=))(n, 0) nim:262:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (<=) nim:269:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(269:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(<=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:266 0 n,AppParam nim:267 1 0], resolvedArgs = [], parent = CaseMatch @open((<=))(n, 0)}
Evaluating: n nim:266:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:267 1 0], resolvedArgs = [BI@(269:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch @open((<=))(n, 0)}
Evaluating: 0 nim:267:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(267:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:267,0)
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(269:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(n:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch @open((<=))(n, 0)}
Extending store: BI@(262:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with False
Applying FScrut {parent = LamBody [n] match ((@open((<=))(n, 0))) {
  (True() : bool )
     -> Alice;
  (@skip False() : bool )
     -> @open(alice-turn)((@open((-))(n, (@open(move)(Bob, n)))));
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> analysis/benchmarks/handlers/nim/Alice;,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/alice-turn)((std/core/types/@open(std/core/int/(-))(n, (std/core/types/@open(analysis/benchmarks/handlers/nim/move)(analysis/benchmarks/handlers/nim/Bob, n)))));]}
Evaluating: @open(alice-turn)((@open((-))(n, (@open(move)(Bob, n))))) nim:264:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: alice-turn nim:278:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:276 0 @open((-))(n, (@open(move)(Bob, n)))], resolvedArgs = [], parent = CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/alice-turn)((std/core/types/@open(std/core/int/(-))(n, (std/core/types/@open(analysis/benchmarks/handlers/nim/move)(analysis/benchmarks/handlers/nim/Bob, n)))));}
Evaluating: @open((-))(n, (@open(move)(Bob, n))) nim:276:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (-) nim:285:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:282 0 n,AppParam nim:283 1 @open(move)(Bob, n)], resolvedArgs = [], parent = AppParam nim:276 0 @open((-))(n, (@open(move)(Bob, n)))}
Evaluating: n nim:282:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:283 1 @open(move)(Bob, n)], resolvedArgs = [T@std/core/int/(-)], parent = AppParam nim:276 0 @open((-))(n, (@open(move)(Bob, n)))}
Evaluating: @open(move)(Bob, n) nim:283:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move nim:293:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:290 0 Bob,AppParam nim:291 1 n], resolvedArgs = [], parent = AppParam nim:283 1 @open(move)(Bob, n)}
Evaluating: Bob nim:290:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(290:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Bob
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:291 1 n], resolvedArgs = [T@analysis/benchmarks/handlers/nim/move], parent = AppParam nim:283 1 @open(move)(Bob, n)}
Evaluating: n nim:291:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/move,BI@(290:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:283 1 @open(move)(Bob, n)}
Extending store: B@(player:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Bob
Extending store: B@(sticks:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Evaluating: @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks) nim:201:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform2 nim:202:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform2 nim:207:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(207:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@perform2
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam nim:204 1 forall<e,a> move/@select,AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) nim:203:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:211:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:213:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(213:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:209 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) nim:209:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @make-ssize_t nim:217:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(217:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:215 0 0], resolvedArgs = [], parent = AppParam nim:209 0 @open(@make-ssize_t)(0)}
Evaluating: 0 nim:215:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(215:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(217:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:209 0 @open(@make-ssize_t)(0)}
Extending store: BI@(209:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(213:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Extending store: CI@(@evv-at1 203:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Extending store: BI@(203:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at([(,CI@(@evv-at1 203:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:204 1 forall<e,a> move/@select,AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: forall<e,a> move/@select nim:204:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move/@select nim:221:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: player nim:205:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@select], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: sticks nim:206:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(207:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@select,B@(player:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Extending store: B@(p:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Bob
Extending store: B@(n:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Extending store: B@(resume:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Kont(analysis/benchmarks/handlers/nim/move,AI@(201:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])],Handler {ops = B@(hnd:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), ret = Just AppParam nim:717 1 fn(@res){
  @res;
}})
Evaluating: val m : int
      = @open(move)(p, n);
val z : bool
      = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
          (@open((==))(i, m));
        }))));
match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
} nim:731:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open(move)(p, n) nim:733:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move nim:784:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:781 0 p,AppParam nim:782 1 n], resolvedArgs = [], parent = LetDef val m : int;}
Evaluating: p nim:781:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:782 1 n], resolvedArgs = [T@analysis/benchmarks/handlers/nim/move], parent = LetDef val m : int;}
Evaluating: n nim:782:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/move,B@(p:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LetDef val m : int;}
Extending store: B@(player:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Bob
Extending store: B@(sticks:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Evaluating: @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks) nim:201:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform2 nim:202:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform2 nim:207:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(207:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@perform2
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam nim:204 1 forall<e,a> move/@select,AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) nim:203:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:211:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:213:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(213:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:209 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) nim:209:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @make-ssize_t nim:217:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(217:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:215 0 0], resolvedArgs = [], parent = AppParam nim:209 0 @open(@make-ssize_t)(0)}
Evaluating: 0 nim:215:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(215:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(217:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:209 0 @open(@make-ssize_t)(0)}
Extending store: BI@(209:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(213:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Extending store: CI@(@evv-at1 203:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Extending store: BI@(203:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at([(,CI@(@evv-at1 203:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:204 1 forall<e,a> move/@select,AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: forall<e,a> move/@select nim:204:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move/@select nim:221:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: player nim:205:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@select], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: sticks nim:206:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(207:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@select,B@(player:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Extending store: B@(_p:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Bob
Extending store: B@(n:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Evaluating: @open(max)(1, (@open((%))(n, 4))) nim:323:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: max nim:328:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:325 0 1,AppParam nim:326 1 @open((%))(n, 4)], resolvedArgs = [], parent = LamBody [_p,n] @open(max)(1, (@open((%))(n, 4)))}
Evaluating: 1 nim:325:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(325:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,1)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:326 1 @open((%))(n, 4)], resolvedArgs = [T@std/core/int/max], parent = LamBody [_p,n] @open(max)(1, (@open((%))(n, 4)))}
Evaluating: @open((%))(n, 4) nim:326:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (%) nim:336:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(336:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(%)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:333 0 n,AppParam nim:334 1 4], resolvedArgs = [], parent = AppParam nim:326 1 @open((%))(n, 4)}
Evaluating: n nim:333:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:334 1 4], resolvedArgs = [BI@(336:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:326 1 @open((%))(n, 4)}
Evaluating: 4 nim:334:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(334:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(336:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(n:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:326 1 @open((%))(n, 4)}
Extending store: BI@(326:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,0)
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/max,BI@(325:d_[a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [_p,n] @open(max)(1, (@open((%))(n, 4)))}
Extending store: B@(i:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,1)
Extending store: B@(j:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,0)
Evaluating: match ((@open((>=))(i, j))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> j;
} int:1725:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open((>=))(i, j) int:1726:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (>=) int:1733:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1733:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(>=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:1730 0 i,AppParam int:1731 1 j], resolvedArgs = [], parent = CaseMatch @open((>=))(i, j)}
Evaluating: i int:1730:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:1731 1 j], resolvedArgs = [BI@(1733:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch @open((>=))(i, j)}
Evaluating: j int:1731:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1733:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(i:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch @open((>=))(i, j)}
Extending store: BI@(1726:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FScrut {parent = LamBody [i,j] match ((@open((>=))(i, j))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> j;
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> i;,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> j;]}
Evaluating: i int:1727:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FResume {label = analysis/benchmarks/handlers/nim/move, vaddr = IL@(201:move:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), rHnd = Handler {ops = B@(hnd:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]), ret = Just AppParam nim:309 1 fn(@res){
  @res;
}}, rCtx = nim:323}
Applying FHLink {linkEff = analysis/benchmarks/handlers/nim/cheat, doCtx = nim:201, hCtx = nim:633, linkKnext = AI@(201:d_[a733,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), linkHnd = Handler {ops = B@(hnd:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), ret = Just AppParam nim:673 1 fn(@res){
  @res;
}}}
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = m, resolved = [], parent = LamBody [p,n,resume] val m : int
      = @open(move)(p, n);
val z : bool
      = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
          (@open((==))(i, m));
        }))));
match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
}}
Extending store: B@(m:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,1)
Extending store: B@(n:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Extending store: B@(p:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Bob
Extending store: B@(resume:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Kont(analysis/benchmarks/handlers/nim/move,AI@(201:d_[a283,a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])],Handler {ops = B@(hnd:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), ret = Just AppParam nim:717 1 fn(@res){
  @res;
}})
Evaluating: val z : bool
      = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
          (@open((==))(i, m));
        }))));
match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
} nim:734:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open(bool)((find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  })))) nim:736:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: bool nim:756:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: bool nim:758:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:754 0 find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  }))], resolvedArgs = [], parent = LetDef val z : bool;}
Evaluating: find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  })) nim:754:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: find nim:759:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: find nim:762:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:760 0 @open(valid-moves)(n),AppParam nim:761 1 fn(i){
  @open((==))(i, m);
}], resolvedArgs = [], parent = AppParam nim:754 0 find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  }))}
Evaluating: @open(valid-moves)(n) nim:760:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: valid-moves nim:766:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:764 0 n], resolvedArgs = [], parent = AppParam nim:760 0 @open(valid-moves)(n)}
Evaluating: n nim:764:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/valid-moves], parent = AppParam nim:760 0 @open(valid-moves)(n)}
Extending store: B@(n:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Evaluating: filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
    (@open((<=))(m, n));
  })) nim:389:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter nim:390:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter nim:393:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:391 0 Cons(1, (Cons(2, (Cons(3, Nil))))),AppParam nim:392 1 fn(m){
  @open((<=))(m, n);
}], resolvedArgs = [], parent = LamBody [n] filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
    (@open((<=))(m, n));
  }))}
Evaluating: Cons(1, (Cons(2, (Cons(3, Nil))))) nim:391:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:394:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:397:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(397:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:395 0 1,AppParam nim:396 1 Cons(2, (Cons(3, Nil)))], resolvedArgs = [], parent = AppParam nim:391 0 Cons(1, (Cons(2, (Cons(3, Nil)))))}
Evaluating: 1 nim:395:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(395:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:396 1 Cons(2, (Cons(3, Nil)))], resolvedArgs = [BI@(397:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:391 0 Cons(1, (Cons(2, (Cons(3, Nil)))))}
Evaluating: Cons(2, (Cons(3, Nil))) nim:396:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:399:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:402:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(402:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:400 0 2,AppParam nim:401 1 Cons(3, Nil)], resolvedArgs = [], parent = AppParam nim:396 1 Cons(2, (Cons(3, Nil)))}
Evaluating: 2 nim:400:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(400:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:401 1 Cons(3, Nil)], resolvedArgs = [BI@(402:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:396 1 Cons(2, (Cons(3, Nil)))}
Evaluating: Cons(3, Nil) nim:401:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:404:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:407:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(407:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:405 0 3,AppParam nim:406 1 Nil], resolvedArgs = [], parent = AppParam nim:401 1 Cons(3, Nil)}
Evaluating: 3 nim:405:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(405:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:406 1 Nil], resolvedArgs = [BI@(407:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:401 1 Cons(3, Nil)}
Evaluating: Nil nim:406:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Nil nim:409:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(409:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(407:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(405:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:401 1 Cons(3, Nil)}
Extending store: CI@(head 401:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: CI@(tail 401:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Extending store: BI@(401:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 401:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 401:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(402:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(400:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:396 1 Cons(2, (Cons(3, Nil)))}
Extending store: CI@(head 396:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: CI@(tail 396:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 401:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 401:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(396:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 396:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 396:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(397:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(395:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:391 0 Cons(1, (Cons(2, (Cons(3, Nil)))))}
Extending store: CI@(head 391:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: CI@(tail 391:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 396:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 396:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(391:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 391:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 391:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:392 1 fn(m){
  @open((<=))(m, n);
}], resolvedArgs = [T@std/core/list/filter], parent = LamBody [n] filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
    (@open((<=))(m, n));
  }))}
Evaluating: fn(m){
  @open((<=))(m, n);
} nim:392:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(392:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/filter,BI@(391:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [n] filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
    (@open((<=))(m, n));
  }))}
Extending store: B@(xs:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 391:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 391:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(pred:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
} list:1916:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1917:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,pred] match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
}, branches = [CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });,CaseBranch 1 (@skip std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nil;]}
Extending store: B@(x:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(xx:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 396:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 396:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Cons(x, (filter(xx, pred)));
  (@skip False() : bool )
     -> filter(xx, pred);
} list:1918:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1920:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1923:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1924 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1924:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(m:d_[a1920,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(n:d_[a1920,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Evaluating: @open((<=))(m, n) nim:410:d_[a1920,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (<=) nim:415:d_[a1920,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(415:d_[a1920,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(<=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:412 0 m,AppParam nim:413 1 n], resolvedArgs = [], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: m nim:412:d_[a1920,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:413 1 n], resolvedArgs = [BI@(415:d_[a1920,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: n nim:413:d_[a1920,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(415:d_[a1920,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(m:d_[a1920,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Extending store: BI@(410:d_[a1920,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FScrut {parent = CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/list/filter(xx, pred);]}
Evaluating: Cons(x, (filter(xx, pred))) list:1921:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1925:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1928:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1928:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1926 0 x,AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: x list:1926:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [BI@(1928:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: filter(xx, pred) list:1927:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1929:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1932:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1930 0 xx,AppParam list:1931 1 pred], resolvedArgs = [], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: xx list:1930:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1931 1 pred], resolvedArgs = [T@std/core/list/filter], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: pred list:1931:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/filter,B@(xx:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam list:1927 1 filter(xx, pred)}
Extending store: B@(xs:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 396:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 396:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(pred:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
} list:1916:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1917:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,pred] match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
}, branches = [CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });,CaseBranch 1 (@skip std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nil;]}
Extending store: B@(x:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: B@(xx:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 401:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 401:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Cons(x, (filter(xx, pred)));
  (@skip False() : bool )
     -> filter(xx, pred);
} list:1918:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1920:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1923:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1924 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1924:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(m:d_[a1920,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: B@(n:d_[a1920,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Evaluating: @open((<=))(m, n) nim:410:d_[a1920,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (<=) nim:415:d_[a1920,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(415:d_[a1920,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(<=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:412 0 m,AppParam nim:413 1 n], resolvedArgs = [], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: m nim:412:d_[a1920,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:413 1 n], resolvedArgs = [BI@(415:d_[a1920,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: n nim:413:d_[a1920,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(415:d_[a1920,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(m:d_[a1920,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Extending store: BI@(410:d_[a1920,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FScrut {parent = CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/list/filter(xx, pred);]}
Evaluating: Cons(x, (filter(xx, pred))) list:1921:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1925:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1928:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1928:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1926 0 x,AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: x list:1926:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [BI@(1928:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: filter(xx, pred) list:1927:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1929:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1932:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1930 0 xx,AppParam list:1931 1 pred], resolvedArgs = [], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: xx list:1930:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1931 1 pred], resolvedArgs = [T@std/core/list/filter], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: pred list:1931:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/filter,B@(xx:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam list:1927 1 filter(xx, pred)}
Extending store: B@(xs:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 401:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 401:d_[a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(pred:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
} list:1916:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1917:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,pred] match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
}, branches = [CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });,CaseBranch 1 (@skip std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nil;]}
Extending store: B@(x:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: B@(xx:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Cons(x, (filter(xx, pred)));
  (@skip False() : bool )
     -> filter(xx, pred);
} list:1918:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1920:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1923:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1924 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1924:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(m:d_[a1920,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: B@(n:d_[a1920,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Evaluating: @open((<=))(m, n) nim:410:d_[a1920,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (<=) nim:415:d_[a1920,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(415:d_[a1920,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(<=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:412 0 m,AppParam nim:413 1 n], resolvedArgs = [], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: m nim:412:d_[a1920,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:413 1 n], resolvedArgs = [BI@(415:d_[a1920,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: n nim:413:d_[a1920,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(415:d_[a1920,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(m:d_[a1920,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Extending store: BI@(410:d_[a1920,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FScrut {parent = CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/list/filter(xx, pred);]}
Evaluating: Cons(x, (filter(xx, pred))) list:1921:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1925:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1928:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1928:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1926 0 x,AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: x list:1926:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [BI@(1928:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: filter(xx, pred) list:1927:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1929:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1932:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1930 0 xx,AppParam list:1931 1 pred], resolvedArgs = [], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: xx list:1930:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1931 1 pred], resolvedArgs = [T@std/core/list/filter], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: pred list:1931:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/filter,B@(xx:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam list:1927 1 filter(xx, pred)}
Extending store: B@(xs:d_[a1927,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Extending store: B@(pred:d_[a1927,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
} list:1916:d_[a1927,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1917:d_[a1927,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,pred] match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
}, branches = [CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });,CaseBranch 1 (@skip std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nil;]}
Evaluating: Nil list:1919:d_[a1927,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Nil list:1933:d_[a1927,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1933:d_[a1927,a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1928:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(x:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Extending store: CI@(head 1921:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: CI@(tail 1921:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Extending store: BI@(1921:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1928:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(x:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Extending store: CI@(head 1921:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: CI@(tail 1921:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(1921:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1928:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(x:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Extending store: CI@(head 1921:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: CI@(tail 1921:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(1921:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:761 1 fn(i){
  @open((==))(i, m);
}], resolvedArgs = [T@std/core/list/find], parent = AppParam nim:754 0 find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  }))}
Evaluating: fn(i){
  @open((==))(i, m);
} nim:761:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(761:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(i){
  @open((==))(i, m);
})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/find,BI@(1921:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:754 0 find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  }))}
Extending store: B@(xs:d_[a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(pred:d_[a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(i){
  @open((==))(i, m);
})
Evaluating: foreach-while(xs, (fn(x){
    (match ((pred(x))) {
      (True() : bool )
         -> Just(x);
      (@skip False() : bool )
         -> Nothing;
    });
  })) list:1934:d_[a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1935:d_[a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1938:d_[a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1936 0 xs,AppParam list:1937 1 fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
}], resolvedArgs = [], parent = LamBody [xs,pred] foreach-while(xs, (fn(x){
    (match ((pred(x))) {
      (True() : bool )
         -> Just(x);
      (@skip False() : bool )
         -> Nothing;
    });
  }))}
Evaluating: xs list:1936:d_[a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1937 1 fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
}], resolvedArgs = [T@std/core/list/foreach-while], parent = LamBody [xs,pred] foreach-while(xs, (fn(x){
    (match ((pred(x))) {
      (True() : bool )
         -> Just(x);
      (@skip False() : bool )
         -> Nothing;
    });
  }))}
Evaluating: fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
} list:1937:d_[a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1937:d_[a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/foreach-while,B@(xs:d_[a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [xs,pred] foreach-while(xs, (fn(x){
    (match ((pred(x))) {
      (True() : bool )
         -> Just(x);
      (@skip False() : bool )
         -> Nothing;
    });
  }))}
Extending store: B@(xs:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(action:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
})
Evaluating: match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
} list:1939:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1940:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,action] match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
}, branches = [CaseBranch 0 (std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nothing;,CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });]}
Extending store: B@(x:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(xx:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a389,a760,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: match ((action(x))) {
  (Nothing() : (maybe<a>) )
     -> foreach-while(xx, action);
  (just)
     -> just;
} list:1942:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action(x) list:1943:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action list:1946:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1947 0 x], resolvedArgs = [], parent = CaseMatch action(x)}
Evaluating: x list:1947:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(action:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch action(x)}
Extending store: B@(x:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(pred:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(i){
  @open((==))(i, m);
})
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Just(x);
  (@skip False() : bool )
     -> Nothing;
} list:1948:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1949:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1952:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1953 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1953:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(i:d_[a1949,a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(m:d_[a1949,a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,1)
Evaluating: @open((==))(i, m) nim:770:d_[a1949,a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (==) nim:775:d_[a1949,a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(775:d_[a1949,a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(==)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:772 0 i,AppParam nim:773 1 m], resolvedArgs = [], parent = LamBody [i] @open((==))(i, m)}
Evaluating: i nim:772:d_[a1949,a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:773 1 m], resolvedArgs = [BI@(775:d_[a1949,a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [i] @open((==))(i, m)}
Evaluating: m nim:773:d_[a1949,a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(775:d_[a1949,a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(i:d_[a1949,a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [i] @open((==))(i, m)}
Extending store: BI@(770:d_[a1949,a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FScrut {parent = LamBody [x] match ((pred(x))) {
  (True() : bool )
     -> Just(x);
  (@skip False() : bool )
     -> Nothing;
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Just(x);,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/Nothing;]}
Evaluating: Just(x) list:1950:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Just list:1959:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Just list:1961:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1961:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Just
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1960 0 x], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Just(x);}
Evaluating: x list:1960:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(1961:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Just(x);}
Extending store: CI@(value 1950:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: BI@(1950:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Just([(value,CI@(value 1950:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FScrut {parent = CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });, branches = [CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);,CaseBranch 1 (just)
   -> just;]}
Extending store: B@(just:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Just([(value,CI@(value 1950:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: just list:1945:d_[a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/maybe/bool], parent = LetDef val z : bool;}
Extending store: B@(mb:d_[a736,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Just([(value,CI@(value 1950:d_[a1943,a1934,a754,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: match (mb) {
  (Just(_) : maybe<a> )
     -> True;
  (@skip Nothing() : (maybe<a>) )
     -> False;
} maybe:1962:d_[a736,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: mb maybe:1963:d_[a736,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [mb] match (mb) {
  (Just(_) : maybe<a> )
     -> True;
  (@skip Nothing() : (maybe<a>) )
     -> False;
}, branches = [CaseBranch 0 (std/core/types/Just(_) : maybe<a> )
   -> std/core/types/True;,CaseBranch 1 (@skip std/core/types/Nothing() : (maybe<a>) )
   -> std/core/types/False;]}
Evaluating: True maybe:1964:d_[a736,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1964:d_[a736,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = z, resolved = [], parent = LetBody val z : bool
      = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
          (@open((==))(i, m));
        }))));
match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
}}
Extending store: B@(z:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Evaluating: match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
} nim:737:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: z nim:738:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LetBody match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> resume(m);,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/cheat)(p);]}
Evaluating: resume(m) nim:739:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: resume nim:742:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:743 0 m], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> resume(m);}
Evaluating: m nim:743:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:d_[a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> resume(m);}
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/(-),B@(n:d_[a227,a298,a804,delim]@[(nim:739,d_[a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:276 0 @open((-))(n, (@open(move)(Bob, n)))}
Extending store: B@(x:d_[a276,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Extending store: B@(y:d_[a276,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,1)
Evaluating: @open(int-sub)(x, y) int:1966:d_[a276,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: int-sub int:1971:d_[a276,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1971:d_[a276,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/int-sub
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:1968 0 x,AppParam int:1969 1 y], resolvedArgs = [], parent = LamBody [x,y] @open(int-sub)(x, y)}
Evaluating: x int:1968:d_[a276,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:1969 1 y], resolvedArgs = [BI@(1971:d_[a276,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [x,y] @open(int-sub)(x, y)}
Evaluating: y int:1969:d_[a276,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1971:d_[a276,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(x:d_[a276,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [x,y] @open(int-sub)(x, y)}
Extending store: BI@(1966:d_[a276,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,3)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/alice-turn], parent = CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/alice-turn)((std/core/types/@open(std/core/int/(-))(n, (std/core/types/@open(analysis/benchmarks/handlers/nim/move)(analysis/benchmarks/handlers/nim/Bob, n)))));}
Extending store: B@(n:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,3)
Evaluating: match ((@open((<=))(n, 0))) {
  (True() : bool )
     -> Bob;
  (@skip False() : bool )
     -> @open(bob-turn)((@open((-))(n, (@open(move)(Alice, n)))));
} nim:224:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open((<=))(n, 0) nim:225:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (<=) nim:232:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(232:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(<=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:229 0 n,AppParam nim:230 1 0], resolvedArgs = [], parent = CaseMatch @open((<=))(n, 0)}
Evaluating: n nim:229:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:230 1 0], resolvedArgs = [BI@(232:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch @open((<=))(n, 0)}
Evaluating: 0 nim:230:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(230:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:230,0)
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(232:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(n:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch @open((<=))(n, 0)}
Extending store: BI@(225:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with False
Applying FScrut {parent = LamBody [n] match ((@open((<=))(n, 0))) {
  (True() : bool )
     -> Bob;
  (@skip False() : bool )
     -> @open(bob-turn)((@open((-))(n, (@open(move)(Alice, n)))));
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> analysis/benchmarks/handlers/nim/Bob;,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/bob-turn)((std/core/types/@open(std/core/int/(-))(n, (std/core/types/@open(analysis/benchmarks/handlers/nim/move)(analysis/benchmarks/handlers/nim/Alice, n)))));]}
Evaluating: @open(bob-turn)((@open((-))(n, (@open(move)(Alice, n))))) nim:227:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: bob-turn nim:241:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:239 0 @open((-))(n, (@open(move)(Alice, n)))], resolvedArgs = [], parent = CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/bob-turn)((std/core/types/@open(std/core/int/(-))(n, (std/core/types/@open(analysis/benchmarks/handlers/nim/move)(analysis/benchmarks/handlers/nim/Alice, n)))));}
Evaluating: @open((-))(n, (@open(move)(Alice, n))) nim:239:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (-) nim:248:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:245 0 n,AppParam nim:246 1 @open(move)(Alice, n)], resolvedArgs = [], parent = AppParam nim:239 0 @open((-))(n, (@open(move)(Alice, n)))}
Evaluating: n nim:245:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:246 1 @open(move)(Alice, n)], resolvedArgs = [T@std/core/int/(-)], parent = AppParam nim:239 0 @open((-))(n, (@open(move)(Alice, n)))}
Evaluating: @open(move)(Alice, n) nim:246:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move nim:256:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:253 0 Alice,AppParam nim:254 1 n], resolvedArgs = [], parent = AppParam nim:246 1 @open(move)(Alice, n)}
Evaluating: Alice nim:253:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(253:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:254 1 n], resolvedArgs = [T@analysis/benchmarks/handlers/nim/move], parent = AppParam nim:246 1 @open(move)(Alice, n)}
Evaluating: n nim:254:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/move,BI@(253:d_[a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:246 1 @open(move)(Alice, n)}
Extending store: B@(player:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Extending store: B@(sticks:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,3)
Evaluating: @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks) nim:201:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform2 nim:202:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform2 nim:207:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(207:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@perform2
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam nim:204 1 forall<e,a> move/@select,AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) nim:203:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:211:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:213:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(213:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:209 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) nim:209:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @make-ssize_t nim:217:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(217:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:215 0 0], resolvedArgs = [], parent = AppParam nim:209 0 @open(@make-ssize_t)(0)}
Evaluating: 0 nim:215:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(215:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(217:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:209 0 @open(@make-ssize_t)(0)}
Extending store: BI@(209:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(213:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Extending store: CI@(@evv-at1 203:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Extending store: BI@(203:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at([(,CI@(@evv-at1 203:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:204 1 forall<e,a> move/@select,AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: forall<e,a> move/@select nim:204:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move/@select nim:221:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: player nim:205:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@select], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: sticks nim:206:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(207:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@select,B@(player:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Extending store: B@(p:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Extending store: B@(n:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,3)
Extending store: B@(resume:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Kont(analysis/benchmarks/handlers/nim/move,AI@(201:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])],Handler {ops = B@(hnd:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), ret = Just AppParam nim:717 1 fn(@res){
  @res;
}})
Evaluating: val m : int
      = @open(move)(p, n);
val z : bool
      = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
          (@open((==))(i, m));
        }))));
match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
} nim:731:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open(move)(p, n) nim:733:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move nim:784:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:781 0 p,AppParam nim:782 1 n], resolvedArgs = [], parent = LetDef val m : int;}
Evaluating: p nim:781:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:782 1 n], resolvedArgs = [T@analysis/benchmarks/handlers/nim/move], parent = LetDef val m : int;}
Evaluating: n nim:782:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/move,B@(p:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LetDef val m : int;}
Extending store: B@(player:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Extending store: B@(sticks:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,3)
Evaluating: @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks) nim:201:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform2 nim:202:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform2 nim:207:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(207:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@perform2
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam nim:204 1 forall<e,a> move/@select,AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) nim:203:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:211:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:213:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(213:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:209 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) nim:209:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @make-ssize_t nim:217:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(217:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:215 0 0], resolvedArgs = [], parent = AppParam nim:209 0 @open(@make-ssize_t)(0)}
Evaluating: 0 nim:215:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(215:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(217:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:209 0 @open(@make-ssize_t)(0)}
Extending store: BI@(209:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(213:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:203 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Extending store: CI@(@evv-at1 203:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:215,0)
Extending store: BI@(203:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at([(,CI@(@evv-at1 203:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:204 1 forall<e,a> move/@select,AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: forall<e,a> move/@select nim:204:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: move/@select nim:221:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:205 2 player,AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: player nim:205:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam nim:206 3 sticks], resolvedArgs = [BI@(207:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@select], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Evaluating: sticks nim:206:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(207:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(203:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#move/@select,B@(player:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player,sticks] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> move/@select), player, sticks)}
Extending store: B@(_p:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Extending store: B@(n:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,3)
Evaluating: @open(max)(1, (@open((%))(n, 4))) nim:323:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: max nim:328:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:325 0 1,AppParam nim:326 1 @open((%))(n, 4)], resolvedArgs = [], parent = LamBody [_p,n] @open(max)(1, (@open((%))(n, 4)))}
Evaluating: 1 nim:325:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(325:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,1)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:326 1 @open((%))(n, 4)], resolvedArgs = [T@std/core/int/max], parent = LamBody [_p,n] @open(max)(1, (@open((%))(n, 4)))}
Evaluating: @open((%))(n, 4) nim:326:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (%) nim:336:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(336:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(%)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:333 0 n,AppParam nim:334 1 4], resolvedArgs = [], parent = AppParam nim:326 1 @open((%))(n, 4)}
Evaluating: n nim:333:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:334 1 4], resolvedArgs = [BI@(336:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:326 1 @open((%))(n, 4)}
Evaluating: 4 nim:334:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(334:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,4)
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(336:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(n:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:326 1 @open((%))(n, 4)}
Extending store: BI@(326:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,3)
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/max,BI@(325:d_[a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [_p,n] @open(max)(1, (@open((%))(n, 4)))}
Extending store: B@(i:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,1)
Extending store: B@(j:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,3)
Evaluating: match ((@open((>=))(i, j))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> j;
} int:1725:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open((>=))(i, j) int:1726:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (>=) int:1733:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1733:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(>=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:1730 0 i,AppParam int:1731 1 j], resolvedArgs = [], parent = CaseMatch @open((>=))(i, j)}
Evaluating: i int:1730:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:1731 1 j], resolvedArgs = [BI@(1733:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch @open((>=))(i, j)}
Evaluating: j int:1731:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1733:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(i:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch @open((>=))(i, j)}
Extending store: BI@(1726:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with False
Applying FScrut {parent = LamBody [i,j] match ((@open((>=))(i, j))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> j;
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> i;,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> j;]}
Evaluating: j int:1728:d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FResume {label = analysis/benchmarks/handlers/nim/move, vaddr = IL@(201:move:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), rHnd = Handler {ops = B@(hnd:d_[a306,a792,a816,a1649,a1645,delim]@[(exn:1633,t_[a1618,a1615,a1610,a812,top])]), ret = Just AppParam nim:309 1 fn(@res){
  @res;
}}, rCtx = nim:323}
Applying FHLink {linkEff = analysis/benchmarks/handlers/nim/cheat, doCtx = nim:201, hCtx = nim:633, linkKnext = AI@(201:d_[a733,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), linkHnd = Handler {ops = B@(hnd:d_[a670,a796,delim]@[(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), ret = Just AppParam nim:673 1 fn(@res){
  @res;
}}}
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = m, resolved = [], parent = LamBody [p,n,resume] val m : int
      = @open(move)(p, n);
val z : bool
      = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
          (@open((==))(i, m));
        }))));
match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
}}
Extending store: B@(m:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,3)
Extending store: B@(n:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,3)
Extending store: B@(p:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Extending store: B@(resume:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Kont(analysis/benchmarks/handlers/nim/move,AI@(201:d_[a246,a264,a227,a298,a804,delim]@[(nim:739,d_[a739,a739,a714,a800,delim]),(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])],Handler {ops = B@(hnd:d_[a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:185,d_[a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), ret = Just AppParam nim:717 1 fn(@res){
  @res;
}})
Evaluating: val z : bool
      = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
          (@open((==))(i, m));
        }))));
match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
} nim:734:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @open(bool)((find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  })))) nim:736:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: bool nim:756:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: bool nim:758:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:754 0 find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  }))], resolvedArgs = [], parent = LetDef val z : bool;}
Evaluating: find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  })) nim:754:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: find nim:759:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: find nim:762:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:760 0 @open(valid-moves)(n),AppParam nim:761 1 fn(i){
  @open((==))(i, m);
}], resolvedArgs = [], parent = AppParam nim:754 0 find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  }))}
Evaluating: @open(valid-moves)(n) nim:760:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: valid-moves nim:766:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:764 0 n], resolvedArgs = [], parent = AppParam nim:760 0 @open(valid-moves)(n)}
Evaluating: n nim:764:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/valid-moves], parent = AppParam nim:760 0 @open(valid-moves)(n)}
Extending store: B@(n:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,3)
Evaluating: filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
    (@open((<=))(m, n));
  })) nim:389:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter nim:390:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter nim:393:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:391 0 Cons(1, (Cons(2, (Cons(3, Nil))))),AppParam nim:392 1 fn(m){
  @open((<=))(m, n);
}], resolvedArgs = [], parent = LamBody [n] filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
    (@open((<=))(m, n));
  }))}
Evaluating: Cons(1, (Cons(2, (Cons(3, Nil))))) nim:391:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:394:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:397:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(397:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:395 0 1,AppParam nim:396 1 Cons(2, (Cons(3, Nil)))], resolvedArgs = [], parent = AppParam nim:391 0 Cons(1, (Cons(2, (Cons(3, Nil)))))}
Evaluating: 1 nim:395:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(395:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:396 1 Cons(2, (Cons(3, Nil)))], resolvedArgs = [BI@(397:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:391 0 Cons(1, (Cons(2, (Cons(3, Nil)))))}
Evaluating: Cons(2, (Cons(3, Nil))) nim:396:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:399:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:402:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(402:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:400 0 2,AppParam nim:401 1 Cons(3, Nil)], resolvedArgs = [], parent = AppParam nim:396 1 Cons(2, (Cons(3, Nil)))}
Evaluating: 2 nim:400:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(400:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:401 1 Cons(3, Nil)], resolvedArgs = [BI@(402:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:396 1 Cons(2, (Cons(3, Nil)))}
Evaluating: Cons(3, Nil) nim:401:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:404:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons nim:407:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(407:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:405 0 3,AppParam nim:406 1 Nil], resolvedArgs = [], parent = AppParam nim:401 1 Cons(3, Nil)}
Evaluating: 3 nim:405:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(405:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:406 1 Nil], resolvedArgs = [BI@(407:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:401 1 Cons(3, Nil)}
Evaluating: Nil nim:406:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Nil nim:409:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(409:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(407:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(405:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:401 1 Cons(3, Nil)}
Extending store: CI@(head 401:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: CI@(tail 401:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Extending store: BI@(401:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 401:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 401:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(402:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(400:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:396 1 Cons(2, (Cons(3, Nil)))}
Extending store: CI@(head 396:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: CI@(tail 396:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 401:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 401:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(396:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 396:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 396:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(397:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(395:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:391 0 Cons(1, (Cons(2, (Cons(3, Nil)))))}
Extending store: CI@(head 391:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: CI@(tail 391:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 396:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 396:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(391:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 391:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 391:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:392 1 fn(m){
  @open((<=))(m, n);
}], resolvedArgs = [T@std/core/list/filter], parent = LamBody [n] filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
    (@open((<=))(m, n));
  }))}
Evaluating: fn(m){
  @open((<=))(m, n);
} nim:392:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(392:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/filter,BI@(391:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [n] filter((Cons(1, (Cons(2, (Cons(3, Nil)))))), (fn(m){
    (@open((<=))(m, n));
  }))}
Extending store: B@(xs:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 391:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 391:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(pred:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
} list:1916:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1917:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,pred] match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
}, branches = [CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });,CaseBranch 1 (@skip std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nil;]}
Extending store: B@(x:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(xx:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 396:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 396:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Cons(x, (filter(xx, pred)));
  (@skip False() : bool )
     -> filter(xx, pred);
} list:1918:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1920:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1923:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1924 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1924:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(m:d_[a1920,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(n:d_[a1920,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,3)
Evaluating: @open((<=))(m, n) nim:410:d_[a1920,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (<=) nim:415:d_[a1920,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(415:d_[a1920,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(<=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:412 0 m,AppParam nim:413 1 n], resolvedArgs = [], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: m nim:412:d_[a1920,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:413 1 n], resolvedArgs = [BI@(415:d_[a1920,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: n nim:413:d_[a1920,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(415:d_[a1920,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(m:d_[a1920,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Extending store: BI@(410:d_[a1920,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FScrut {parent = CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/list/filter(xx, pred);]}
Evaluating: Cons(x, (filter(xx, pred))) list:1921:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1925:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1928:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1928:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1926 0 x,AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: x list:1926:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [BI@(1928:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: filter(xx, pred) list:1927:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1929:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1932:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1930 0 xx,AppParam list:1931 1 pred], resolvedArgs = [], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: xx list:1930:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1931 1 pred], resolvedArgs = [T@std/core/list/filter], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: pred list:1931:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/filter,B@(xx:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam list:1927 1 filter(xx, pred)}
Extending store: B@(xs:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 396:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 396:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(pred:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
} list:1916:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1917:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,pred] match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
}, branches = [CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });,CaseBranch 1 (@skip std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nil;]}
Extending store: B@(x:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: B@(xx:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 401:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 401:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Cons(x, (filter(xx, pred)));
  (@skip False() : bool )
     -> filter(xx, pred);
} list:1918:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1920:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1923:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1924 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1924:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(m:d_[a1920,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: B@(n:d_[a1920,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,3)
Evaluating: @open((<=))(m, n) nim:410:d_[a1920,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (<=) nim:415:d_[a1920,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(415:d_[a1920,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(<=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:412 0 m,AppParam nim:413 1 n], resolvedArgs = [], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: m nim:412:d_[a1920,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:413 1 n], resolvedArgs = [BI@(415:d_[a1920,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: n nim:413:d_[a1920,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(415:d_[a1920,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(m:d_[a1920,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Extending store: BI@(410:d_[a1920,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with True
Applying FScrut {parent = CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/list/filter(xx, pred);]}
Evaluating: Cons(x, (filter(xx, pred))) list:1921:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1925:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Cons list:1928:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1928:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Cons
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1926 0 x,AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: x list:1926:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1927 1 filter(xx, pred)], resolvedArgs = [BI@(1928:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Evaluating: filter(xx, pred) list:1927:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1929:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1932:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1930 0 xx,AppParam list:1931 1 pred], resolvedArgs = [], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: xx list:1930:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1931 1 pred], resolvedArgs = [T@std/core/list/filter], parent = AppParam list:1927 1 filter(xx, pred)}
Evaluating: pred list:1931:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/filter,B@(xx:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam list:1927 1 filter(xx, pred)}
Extending store: B@(xs:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 401:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 401:d_[a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(pred:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
} list:1916:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1917:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,pred] match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
}, branches = [CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });,CaseBranch 1 (@skip std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nil;]}
Extending store: B@(x:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: B@(xx:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Cons(x, (filter(xx, pred)));
  (@skip False() : bool )
     -> filter(xx, pred);
} list:1918:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1920:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1923:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1924 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1924:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(m:d_[a1920,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:405,3)
Extending store: B@(n:d_[a1920,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:325,3)
Evaluating: @open((<=))(m, n) nim:410:d_[a1920,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (<=) nim:415:d_[a1920,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(415:d_[a1920,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(<=)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:412 0 m,AppParam nim:413 1 n], resolvedArgs = [], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: m nim:412:d_[a1920,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:413 1 n], resolvedArgs = [BI@(415:d_[a1920,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Evaluating: n nim:413:d_[a1920,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(415:d_[a1920,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(m:d_[a1920,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [m] @open((<=))(m, n)}
Extending store: BI@(410:d_[a1920,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with False
Applying FScrut {parent = CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/list/filter(xx, pred);]}
Evaluating: filter(xx, pred) list:1922:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1972:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: filter list:1975:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1973 0 xx,AppParam list:1974 1 pred], resolvedArgs = [], parent = CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/list/filter(xx, pred);}
Evaluating: xx list:1973:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1974 1 pred], resolvedArgs = [T@std/core/list/filter], parent = CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/list/filter(xx, pred);}
Evaluating: pred list:1974:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/filter,B@(xx:d_[a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/list/filter(xx, pred);}
Extending store: B@(xs:d_[a1922,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Extending store: B@(pred:d_[a1922,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(m){
  @open((<=))(m, n);
})
Evaluating: match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
} list:1916:d_[a1922,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1917:d_[a1922,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,pred] match (xs) {
  (Cons((x), (xx)) : list<a> )
     -> (match ((pred(x))) {
      (True() : bool )
         -> Cons(x, (filter(xx, pred)));
      (@skip False() : bool )
         -> filter(xx, pred);
    });
  (@skip Nil() : (list<a>) )
     -> Nil;
}, branches = [CaseBranch 0 (std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((pred(x))) {
    (std/core/types/True() : bool )
       -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));
    (@skip std/core/types/False() : bool )
       -> std/core/list/filter(xx, pred);
  });,CaseBranch 1 (@skip std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nil;]}
Evaluating: Nil list:1919:d_[a1922,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Nil list:1933:d_[a1922,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1933:d_[a1922,a1927,a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1928:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(x:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Extending store: CI@(head 1921:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: CI@(tail 1921:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Extending store: BI@(1921:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1928:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(x:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Cons(x, (std/core/list/filter(xx, pred)));}
Extending store: CI@(head 1921:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: CI@(tail 1921:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(1921:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:761 1 fn(i){
  @open((==))(i, m);
}], resolvedArgs = [T@std/core/list/find], parent = AppParam nim:754 0 find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  }))}
Evaluating: fn(i){
  @open((==))(i, m);
} nim:761:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(761:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(i){
  @open((==))(i, m);
})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/find,BI@(1921:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:754 0 find((@open(valid-moves)(n)), (fn(i){
    (@open((==))(i, m));
  }))}
Extending store: B@(xs:d_[a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(pred:d_[a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(i){
  @open((==))(i, m);
})
Evaluating: foreach-while(xs, (fn(x){
    (match ((pred(x))) {
      (True() : bool )
         -> Just(x);
      (@skip False() : bool )
         -> Nothing;
    });
  })) list:1934:d_[a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1935:d_[a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1938:d_[a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1936 0 xs,AppParam list:1937 1 fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
}], resolvedArgs = [], parent = LamBody [xs,pred] foreach-while(xs, (fn(x){
    (match ((pred(x))) {
      (True() : bool )
         -> Just(x);
      (@skip False() : bool )
         -> Nothing;
    });
  }))}
Evaluating: xs list:1936:d_[a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1937 1 fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
}], resolvedArgs = [T@std/core/list/foreach-while], parent = LamBody [xs,pred] foreach-while(xs, (fn(x){
    (match ((pred(x))) {
      (True() : bool )
         -> Just(x);
      (@skip False() : bool )
         -> Nothing;
    });
  }))}
Evaluating: fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
} list:1937:d_[a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1937:d_[a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/foreach-while,B@(xs:d_[a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [xs,pred] foreach-while(xs, (fn(x){
    (match ((pred(x))) {
      (True() : bool )
         -> Just(x);
      (@skip False() : bool )
         -> Nothing;
    });
  }))}
Extending store: B@(xs:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(action:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
})
Evaluating: match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
} list:1939:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1940:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,action] match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
}, branches = [CaseBranch 0 (std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nothing;,CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });]}
Extending store: B@(x:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(xx:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: match ((action(x))) {
  (Nothing() : (maybe<a>) )
     -> foreach-while(xx, action);
  (just)
     -> just;
} list:1942:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action(x) list:1943:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action list:1946:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1947 0 x], resolvedArgs = [], parent = CaseMatch action(x)}
Evaluating: x list:1947:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(action:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch action(x)}
Extending store: B@(x:d_[a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(pred:d_[a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(i){
  @open((==))(i, m);
})
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Just(x);
  (@skip False() : bool )
     -> Nothing;
} list:1948:d_[a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1949:d_[a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1952:d_[a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1953 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1953:d_[a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(i:d_[a1949,a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:395,1)
Extending store: B@(m:d_[a1949,a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,3)
Evaluating: @open((==))(i, m) nim:770:d_[a1949,a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (==) nim:775:d_[a1949,a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(775:d_[a1949,a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(==)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:772 0 i,AppParam nim:773 1 m], resolvedArgs = [], parent = LamBody [i] @open((==))(i, m)}
Evaluating: i nim:772:d_[a1949,a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:773 1 m], resolvedArgs = [BI@(775:d_[a1949,a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [i] @open((==))(i, m)}
Evaluating: m nim:773:d_[a1949,a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(775:d_[a1949,a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(i:d_[a1949,a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [i] @open((==))(i, m)}
Extending store: BI@(770:d_[a1949,a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with False
Applying FScrut {parent = LamBody [x] match ((pred(x))) {
  (True() : bool )
     -> Just(x);
  (@skip False() : bool )
     -> Nothing;
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Just(x);,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/Nothing;]}
Evaluating: Nothing list:1951:d_[a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Nothing list:1954:d_[a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1954:d_[a1943,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nothing
Applying FScrut {parent = CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });, branches = [CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);,CaseBranch 1 (just)
   -> just;]}
Evaluating: foreach-while(xx, action) list:1944:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1955:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1958:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1956 0 xx,AppParam list:1957 1 action], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);}
Evaluating: xx list:1956:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1957 1 action], resolvedArgs = [T@std/core/list/foreach-while], parent = CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);}
Evaluating: action list:1957:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/foreach-while,B@(xx:d_[a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);}
Extending store: B@(xs:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/Cons([(head,CI@(head 1921:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(tail,CI@(tail 1921:d_[a1927,a389,a760,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: B@(action:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
})
Evaluating: match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
} list:1939:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1940:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,action] match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
}, branches = [CaseBranch 0 (std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nothing;,CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });]}
Extending store: B@(x:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: B@(xx:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Evaluating: match ((action(x))) {
  (Nothing() : (maybe<a>) )
     -> foreach-while(xx, action);
  (just)
     -> just;
} list:1942:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action(x) list:1943:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: action list:1946:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1947 0 x], resolvedArgs = [], parent = CaseMatch action(x)}
Evaluating: x list:1947:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(action:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch action(x)}
Extending store: B@(x:d_[a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: B@(pred:d_[a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(i){
  @open((==))(i, m);
})
Evaluating: match ((pred(x))) {
  (True() : bool )
     -> Just(x);
  (@skip False() : bool )
     -> Nothing;
} list:1948:d_[a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred(x) list:1949:d_[a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: pred list:1952:d_[a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam list:1953 0 x], resolvedArgs = [], parent = CaseMatch pred(x)}
Evaluating: x list:1953:d_[a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(pred:d_[a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseMatch pred(x)}
Extending store: B@(i:d_[a1949,a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:400,2)
Extending store: B@(m:d_[a1949,a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:334,3)
Evaluating: @open((==))(i, m) nim:770:d_[a1949,a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (==) nim:775:d_[a1949,a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(775:d_[a1949,a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/int/(==)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:772 0 i,AppParam nim:773 1 m], resolvedArgs = [], parent = LamBody [i] @open((==))(i, m)}
Evaluating: i nim:772:d_[a1949,a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:773 1 m], resolvedArgs = [BI@(775:d_[a1949,a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [i] @open((==))(i, m)}
Evaluating: m nim:773:d_[a1949,a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(775:d_[a1949,a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(i:d_[a1949,a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [i] @open((==))(i, m)}
Extending store: BI@(770:d_[a1949,a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with False
Applying FScrut {parent = LamBody [x] match ((pred(x))) {
  (True() : bool )
     -> Just(x);
  (@skip False() : bool )
     -> Nothing;
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> std/core/types/Just(x);,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/Nothing;]}
Evaluating: Nothing list:1951:d_[a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Nothing list:1954:d_[a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1954:d_[a1943,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nothing
Applying FScrut {parent = CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });, branches = [CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);,CaseBranch 1 (just)
   -> just;]}
Evaluating: foreach-while(xx, action) list:1944:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1955:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: foreach-while list:1958:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1956 0 xx,AppParam list:1957 1 action], resolvedArgs = [], parent = CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);}
Evaluating: xx list:1956:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam list:1957 1 action], resolvedArgs = [T@std/core/list/foreach-while], parent = CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);}
Evaluating: action list:1957:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/list/foreach-while,B@(xx:d_[a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = CaseBranch 0 (std/core/types/Nothing() : (maybe<a>) )
   -> std/core/list/foreach-while(xx, action);}
Extending store: B@(xs:d_[a1944,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nil
Extending store: B@(action:d_[a1944,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with AppParam(fn(x){
  match ((pred(x))) {
    (True() : bool )
       -> Just(x);
    (@skip False() : bool )
       -> Nothing;
  };
})
Evaluating: match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
} list:1939:d_[a1944,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: xs list:1940:d_[a1944,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [xs,action] match (xs) {
  (Nil() : (list<a>) )
     -> Nothing;
  (@skip Cons((x), (xx)) : list<a> )
     -> (match ((action(x))) {
      (Nothing() : (maybe<a>) )
         -> foreach-while(xx, action);
      (just)
         -> just;
    });
}, branches = [CaseBranch 0 (std/core/types/Nil() : (list<a>) )
   -> std/core/types/Nothing;,CaseBranch 1 (@skip std/core/types/Cons((x), (xx)) : list<a> )
   -> (match ((action(x))) {
    (std/core/types/Nothing() : (maybe<a>) )
       -> std/core/list/foreach-while(xx, action);
    (just)
       -> just;
  });]}
Evaluating: Nothing list:1941:d_[a1944,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Nothing list:1976:d_[a1944,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1976:d_[a1944,a1944,a1934,a754,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nothing
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/maybe/bool], parent = LetDef val z : bool;}
Extending store: B@(mb:d_[a736,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Nothing
Evaluating: match (mb) {
  (Just(_) : maybe<a> )
     -> True;
  (@skip Nothing() : (maybe<a>) )
     -> False;
} maybe:1962:d_[a736,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: mb maybe:1963:d_[a736,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [mb] match (mb) {
  (Just(_) : maybe<a> )
     -> True;
  (@skip Nothing() : (maybe<a>) )
     -> False;
}, branches = [CaseBranch 0 (std/core/types/Just(_) : maybe<a> )
   -> std/core/types/True;,CaseBranch 1 (@skip std/core/types/Nothing() : (maybe<a>) )
   -> std/core/types/False;]}
Evaluating: False maybe:1965:d_[a736,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(1965:d_[a736,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with False
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = z, resolved = [], parent = LetBody val z : bool
      = @open(bool)((find((@open(valid-moves)(n)), (fn(i){
          (@open((==))(i, m));
        }))));
match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
}}
Extending store: B@(z:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with False
Evaluating: match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
} nim:737:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: z nim:738:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LetBody match (z) {
  (True() : bool )
     -> resume(m);
  (@skip False() : bool )
     -> @open(cheat)(p);
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> resume(m);,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/cheat)(p);]}
Evaluating: @open(cheat)(p) nim:740:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: cheat nim:749:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: cheat nim:751:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a> fn(player){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,b> cheat/@select), player);
} nim:60:t_[top]@[]
Extending store: BI@(60:t_[top]@[]) with DefNonRec(cheat)
Extending store: T@analysis/benchmarks/handlers/nim/cheat with DefNonRec(cheat)
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:747 0 p], resolvedArgs = [], parent = CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/cheat)(p);}
Evaluating: p nim:747:d_[a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/cheat], parent = CaseBranch 1 (@skip std/core/types/False() : bool )
   -> std/core/types/@open(analysis/benchmarks/handlers/nim/cheat)(p);}
Extending store: B@(player:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> cheat/@select), player) nim:649:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform1 nim:650:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform1 nim:654:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(654:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@perform1
Applying FApp {totalArgs = 3, leftArgs = [AppParam nim:651 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam nim:652 1 forall<e,a> cheat/@select,AppParam nim:653 2 player], resolvedArgs = [], parent = LamBody [player] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> cheat/@select), player)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) nim:651:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:658:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at nim:660:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(660:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:656 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam nim:651 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) nim:656:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @make-ssize_t nim:664:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(664:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:662 0 0], resolvedArgs = [], parent = AppParam nim:656 0 @open(@make-ssize_t)(0)}
Evaluating: 0 nim:662:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(662:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:662,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(664:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:656 0 @open(@make-ssize_t)(0)}
Extending store: BI@(656:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:662,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(660:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:651 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Extending store: CI@(@evv-at1 651:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (nim:662,0)
Extending store: BI@(651:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at([(,CI@(@evv-at1 651:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam nim:652 1 forall<e,a> cheat/@select,AppParam nim:653 2 player], resolvedArgs = [BI@(654:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> cheat/@select), player)}
Evaluating: forall<e,a> cheat/@select nim:652:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: cheat/@select nim:668:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a,e,b> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-cheat(_, (@fun-cheat)) : analysis/benchmarks/handlers/nim/cheat<e,b> )
       -> @fun-cheat;
  });
} nim:58:t_[top]@[]
Extending store: BI@(58:t_[top]@[]) with DefNonRec(cheat/@select)
Extending store: T@analysis/benchmarks/handlers/nim/#cheat/@select with DefNonRec(cheat/@select)
Applying FApp {totalArgs = 3, leftArgs = [AppParam nim:653 2 player], resolvedArgs = [BI@(654:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(651:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [player] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> cheat/@select), player)}
Evaluating: player nim:653:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [BI@(654:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(651:d_[a740,a739,a739,a714,a800,delim]@[(nim:633,d_[a670,a796,delim]),(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@analysis/benchmarks/handlers/nim/#cheat/@select], parent = LamBody [player] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> cheat/@select), player)}
Extending store: B@(p:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Evaluating: @open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None) nim:687:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: throw nim:692:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: throw nim:694:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a> fn(message, info){
  val @uniq-info@398 : exception-info
        = (match (info) {
          (@Optional((@uniq-info@399)) : ? exception-info )
             -> @uniq-info@399;
          (@skip @None() : ? exception-info )
             -> ExnError;
        });
  @open(throw-exn)((Exception(message, @uniq-info@398)));
} exn:1567:t_[top]@[]
Extending store: BI@(1567:t_[top]@[]) with DefNonRec(throw)
Extending store: T@std/core/exn/throw with DefNonRec(throw)
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:689 0 @open((++))((@open(player/show)(p)), " cheated!"),AppParam nim:690 1 @None], resolvedArgs = [], parent = LamBody [p] @open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None)}
Evaluating: @open((++))((@open(player/show)(p)), " cheated!") nim:689:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (++) nim:699:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: fn(x, y){
  @open((@extern-x++))(x, y);
} types:2071:t_[top]@[]
Extending store: BI@(2071:t_[top]@[]) with DefNonRec((++))
Extending store: T@std/core/types/(++) with DefNonRec((++))
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:696 0 @open(player/show)(p),AppParam nim:697 1 " cheated!"], resolvedArgs = [], parent = AppParam nim:689 0 @open((++))((@open(player/show)(p)), " cheated!")}
Evaluating: @open(player/show)(p) nim:696:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: player/show nim:705:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: fn(p){
  match (p) {
    (Bob() : analysis/benchmarks/handlers/nim/player )
       -> "bob";
    (@skip Alice() : analysis/benchmarks/handlers/nim/player )
       -> "alice";
  };
} nim:9:t_[top]@[]
Extending store: BI@(9:t_[top]@[]) with DefNonRec(player/show)
Extending store: T@analysis/benchmarks/handlers/nim/#player/show with DefNonRec(player/show)
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:703 0 p], resolvedArgs = [], parent = AppParam nim:696 0 @open(player/show)(p)}
Evaluating: p nim:703:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/nim/#player/show], parent = AppParam nim:696 0 @open(player/show)(p)}
Extending store: B@(p:d_[a696,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Alice
Evaluating: match (p) {
  (Bob() : analysis/benchmarks/handlers/nim/player )
     -> "bob";
  (@skip Alice() : analysis/benchmarks/handlers/nim/player )
     -> "alice";
} nim:161:d_[a696,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: p nim:162:d_[a696,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LamBody [p] match (p) {
  (Bob() : analysis/benchmarks/handlers/nim/player )
     -> "bob";
  (@skip Alice() : analysis/benchmarks/handlers/nim/player )
     -> "alice";
}, branches = [CaseBranch 0 (analysis/benchmarks/handlers/nim/Bob() : analysis/benchmarks/handlers/nim/player )
   -> "bob";,CaseBranch 1 (@skip analysis/benchmarks/handlers/nim/Alice() : analysis/benchmarks/handlers/nim/player )
   -> "alice";]}
Evaluating: "alice" nim:164:d_[a696,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(164:d_[a696,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with string -> (nim:164,"alice")
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:697 1 " cheated!"], resolvedArgs = [T@std/core/types/(++)], parent = AppParam nim:689 0 @open((++))((@open(player/show)(p)), " cheated!")}
Evaluating: " cheated!" nim:697:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(697:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with string -> (nim:697," cheated!")
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/types/(++),BI@(164:d_[a696,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam nim:689 0 @open((++))((@open(player/show)(p)), " cheated!")}
Extending store: B@(x:d_[a689,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with string -> (nim:164,"alice")
Extending store: B@(y:d_[a689,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with string -> (nim:697," cheated!")
Evaluating: @open((@extern-x++))(x, y) types:2084:d_[a689,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: (@extern-x++) types:2089:d_[a689,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(2089:d_[a689,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/(@extern-x++)
Applying FApp {totalArgs = 2, leftArgs = [AppParam types:2086 0 x,AppParam types:2087 1 y], resolvedArgs = [], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Evaluating: x types:2086:d_[a689,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam types:2087 1 y], resolvedArgs = [BI@(2089:d_[a689,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Evaluating: y types:2087:d_[a689,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(2089:d_[a689,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(x:d_[a689,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Extending store: BI@(2084:d_[a689,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with string -> (nim:697,"alice cheated!")
Applying FApp {totalArgs = 2, leftArgs = [AppParam nim:690 1 @None], resolvedArgs = [T@std/core/exn/throw], parent = LamBody [p] @open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None)}
Evaluating: @None nim:690:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @None nim:710:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(710:d_[a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with @None
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/exn/throw,BI@(2084:d_[a689,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [p] @open(throw)((@open((++))((@open(player/show)(p)), " cheated!")), @None)}
Extending store: B@(message:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with string -> (nim:697,"alice cheated!")
Extending store: B@(info:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with @None
Evaluating: val @uniq-info@398 : exception-info
      = match (info) {
        (@Optional((@uniq-info@399)) : ? exception-info )
           -> @uniq-info@399;
        (@skip @None() : ? exception-info )
           -> ExnError;
      };
@open(throw-exn)((Exception(message, @uniq-info@398))) exn:2090:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: match (info) {
  (@Optional((@uniq-info@399)) : ? exception-info )
     -> @uniq-info@399;
  (@skip @None() : ? exception-info )
     -> ExnError;
} exn:2092:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: info exn:2094:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FScrut {parent = LetDef val @uniq-info@398 : exception-info;, branches = [CaseBranch 0 (std/core/types/@Optional((@uniq-info@399)) : ? exception-info )
   -> @uniq-info@399;,CaseBranch 1 (@skip std/core/types/@None() : ? exception-info )
   -> std/core/exn/ExnError;]}
Evaluating: ExnError exn:2096:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(2096:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with ExnError
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = @uniq-info@398, resolved = [], parent = LamBody [message,info] val @uniq-info@398 : exception-info
      = match (info) {
        (@Optional((@uniq-info@399)) : ? exception-info )
           -> @uniq-info@399;
        (@skip @None() : ? exception-info )
           -> ExnError;
      };
@open(throw-exn)((Exception(message, @uniq-info@398)))}
Extending store: B@(@uniq-info@398:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with ExnError
Evaluating: @open(throw-exn)((Exception(message, @uniq-info@398))) exn:2093:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: throw-exn exn:2100:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: throw-exn exn:2101:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a> fn(exn){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,b> throw-exn/@select), exn);
} exn:1545:t_[top]@[]
Extending store: BI@(1545:t_[top]@[]) with DefNonRec(throw-exn)
Extending store: T@std/core/exn/throw-exn with DefNonRec(throw-exn)
Applying FApp {totalArgs = 1, leftArgs = [AppParam exn:2098 0 Exception(message, @uniq-info@398)], resolvedArgs = [], parent = LetBody @open(throw-exn)((Exception(message, @uniq-info@398)))}
Evaluating: Exception(message, @uniq-info@398) exn:2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: Exception exn:2102:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(2102:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with Exception
Applying FApp {totalArgs = 2, leftArgs = [AppParam exn:2103 0 message,AppParam exn:2104 1 @uniq-info@398], resolvedArgs = [], parent = AppParam exn:2098 0 Exception(message, @uniq-info@398)}
Evaluating: message exn:2103:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam exn:2104 1 @uniq-info@398], resolvedArgs = [BI@(2102:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam exn:2098 0 Exception(message, @uniq-info@398)}
Evaluating: @uniq-info@398 exn:2104:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(2102:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),B@(message:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam exn:2098 0 Exception(message, @uniq-info@398)}
Extending store: CI@(message 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with string -> (nim:697,"alice cheated!")
Extending store: CI@(info 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with ExnError
Extending store: BI@(2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/exn/Exception([(message,CI@(message 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(info,CI@(info 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/exn/throw-exn], parent = LetBody @open(throw-exn)((Exception(message, @uniq-info@398)))}
Extending store: B@(exn:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/exn/Exception([(message,CI@(message 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(info,CI@(info 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> throw-exn/@select), exn) exn:2105:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform1 exn:2106:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @perform1 exn:2110:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(2110:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@perform1
Applying FApp {totalArgs = 3, leftArgs = [AppParam exn:2107 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam exn:2108 1 forall<e,a> throw-exn/@select,AppParam exn:2109 2 exn], resolvedArgs = [], parent = LamBody [exn] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> throw-exn/@select), exn)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) exn:2107:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at exn:2114:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @evv-at exn:2115:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(2115:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam exn:2112 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam exn:2107 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) exn:2112:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: @make-ssize_t exn:2119:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(2119:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam exn:2117 0 0], resolvedArgs = [], parent = AppParam exn:2112 0 @open(@make-ssize_t)(0)}
Evaluating: 0 exn:2117:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Extending store: BI@(2117:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (exn:2117,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(2119:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam exn:2112 0 @open(@make-ssize_t)(0)}
Extending store: BI@(2112:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (exn:2117,0)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(2115:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = AppParam exn:2107 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Extending store: CI@(@evv-at1 2107:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with int -> (exn:2117,0)
Extending store: BI@(2107:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]) with std/core/hnd/@evv-at([(,CI@(@evv-at1 2107:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam exn:2108 1 forall<e,a> throw-exn/@select,AppParam exn:2109 2 exn], resolvedArgs = [BI@(2110:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [exn] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> throw-exn/@select), exn)}
Evaluating: forall<e,a> throw-exn/@select exn:2108:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: throw-exn/@select exn:2120:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Evaluating: forall<a,e,b> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-exn(_, (@brk-throw-exn)) : exn<e,b> )
       -> @brk-throw-exn;
  });
} exn:1543:t_[top]@[]
Extending store: BI@(1543:t_[top]@[]) with DefNonRec(throw-exn/@select)
Extending store: T@std/core/exn/#throw-exn/@select with DefNonRec(throw-exn/@select)
Applying FApp {totalArgs = 3, leftArgs = [AppParam exn:2109 2 exn], resolvedArgs = [BI@(2110:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(2107:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])], parent = LamBody [exn] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> throw-exn/@select), exn)}
Evaluating: exn exn:2109:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [BI@(2110:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),BI@(2107:d_[a2093,a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]),T@std/core/exn/#throw-exn/@select], parent = LamBody [exn] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> throw-exn/@select), exn)}
Extending store: B@(hndl:t_[a1618,a1615,a1610,a812,top]@[]) with AppParam(fn(exn){
  Error(exn);
})
Extending store: B@(exn:t_[a1618,a1615,a1610,a812,top]@[]) with std/core/exn/Exception([(message,CI@(message 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(info,CI@(info 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: hndl(exn) exn:2121:t_[a1618,a1615,a1610,a812,top]@[]
Evaluating: hndl exn:2122:t_[a1618,a1615,a1610,a812,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam exn:2123 0 exn], resolvedArgs = [], parent = LamBody [exn] hndl(exn)}
Evaluating: exn exn:2123:t_[a1618,a1615,a1610,a812,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(hndl:t_[a1618,a1615,a1610,a812,top]@[])], parent = LamBody [exn] hndl(exn)}
Extending store: B@(exn:t_[a2121,a1618,a1615,a1610,a812,top]@[]) with std/core/exn/Exception([(message,CI@(message 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(info,CI@(info 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Evaluating: Error(exn) exn:2124:t_[a2121,a1618,a1615,a1610,a812,top]@[]
Evaluating: Error exn:2125:t_[a2121,a1618,a1615,a1610,a812,top]@[]
Evaluating: Error exn:2127:t_[a2121,a1618,a1615,a1610,a812,top]@[]
Extending store: BI@(2127:t_[a2121,a1618,a1615,a1610,a812,top]@[]) with Error
Applying FApp {totalArgs = 1, leftArgs = [AppParam exn:2126 0 exn], resolvedArgs = [], parent = LamBody [exn] Error(exn)}
Evaluating: exn exn:2126:t_[a2121,a1618,a1615,a1610,a812,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(2127:t_[a2121,a1618,a1615,a1610,a812,top]@[])], parent = LamBody [exn] Error(exn)}
Extending store: CI@(exception 2124:t_[a2121,a1618,a1615,a1610,a812,top]@[]) with std/core/exn/Exception([(message,CI@(message 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(info,CI@(info 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])
Extending store: BI@(2124:t_[a2121,a1618,a1615,a1610,a812,top]@[]) with std/core/exn/Error([(exception,CI@(exception 2124:t_[a2121,a1618,a1615,a1610,a812,top]@[]))])
Extending store: EndVAddr with std/core/exn/Error([(exception,CI@(exception 2124:t_[a2121,a1618,a1615,a1610,a812,top]@[]))])
result': ( objs: ["(ExprBasic Error,std/core/exn/Error,[(exception,CI@(exception 2124:t_[a2121,a1618,a1615,a1610,a812,top]@[]))])"] lit: ⊥,⊥,⊥,⊥,fromList [(CI@(exception 2124:t_[a2121,a1618,a1615,a1610,a812,top]@[]), objs: ["(AppLambda Exception,std/core/exn/Exception,[(message,CI@(message 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])])),(info,CI@(info 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]))])"] lit: ⊥,⊥,⊥,⊥),(CI@(info 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), constrs: (CaseBranch 1 (@skip std/core/types/@None() : ? exception-info )
   -> std/core/exn/ExnError;,[]) lit: ⊥,⊥,⊥,⊥),(CI@(message 2098:d_[a687,a670,a796,delim]@[(nim:323,d_[a323,a323,a323,a306,a792,a816,a1649,a1645,delim]),(exn:1633,t_[a1618,a1615,a1610,a812,top])]), lit: ⊥,⊥,⊥,(nim:697,"alice cheated!"))])
Evaluating: Ok(Alice) nim:822:t_[top]@[]
Evaluating: Ok nim:823:t_[top]@[]
Evaluating: Ok nim:825:t_[top]@[]
Extending store: BI@(825:t_[top]@[]) with Ok
Applying FApp {totalArgs = 1, leftArgs = [AppParam nim:824 0 Alice], resolvedArgs = [], parent = LamBody [] Ok(Alice)}
Evaluating: Alice nim:824:t_[top]@[]
Extending store: BI@(824:t_[top]@[]) with Alice
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(825:t_[top]@[])], parent = LamBody [] Ok(Alice)}
Extending store: CI@(result 822:t_[top]@[]) with Alice
Extending store: BI@(822:t_[top]@[]) with std/core/exn/Ok([(result,CI@(result 822:t_[top]@[]))])
Extending store: EndVAddr with std/core/exn/Ok([(result,CI@(result 822:t_[top]@[]))])
expected': ( objs: ["(ExprBasic Ok,std/core/exn/Ok,[(result,CI@(result 822:t_[top]@[]))])"] lit: ⊥,⊥,⊥,⊥,fromList [(CI@(result 822:t_[top]@[]), constrs: (AppParam nim:824 0 Alice,[]) lit: ⊥,⊥,⊥,⊥)])
passed: False
 objs: ["(ExprBasic Error,std/core/exn/Error,[(exception,CI@(exception 2124:t_[a2121,a1618,a1615,a1610,a812,top]@[]))])"] lit: ⊥,⊥,⊥,⊥
 objs: ["(ExprBasic Ok,std/core/exn/Ok,[(result,CI@(result 822:t_[top]@[]))])"] lit: ⊥,⊥,⊥,⊥
d=5,m=20
Result 0 / 1
Result 0.0%, time: 0.157665s
