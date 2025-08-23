Evaluating: val _ : ()
      = @open(trace)("Example 1 - exceptions");
(fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        a;
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open(ex1)(1));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 1 - exceptions") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 1 - exceptions" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        a;
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open(ex1)(1));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        a;
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  @open(ex1)(1);
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
      a;
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex1/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
    a;
  })))) in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: @open(clause-control1)((fn(a, resume){
  a;
})) in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: fn(a, resume){
  a;
} in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a371,top]@[]
Evaluating: @hhandle(ex1/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a374,a371,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a374,a371,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a374,a371,top]@[]
Evaluating: ex1/@tag in BEnv (fromList [action,hnd,ret]):[a374,a371,top]@[]
Evaluating: @open(@new-htag)("ex1@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex1@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a374,a371,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a374,a371,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a374,a371,top]@[]
OPS analysis/aac/benchmarks/ex1 fvs: BEnv (fromList []):[a374,a371,top]@[]
Evaluating: @open(ex1)(1) in BEnv (fromList []):[delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: ex1 in BEnv (fromList []):[delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i) in BEnv (fromList [i]):[a396,delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a396,delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a396,delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a396,delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a396,delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a396,delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a396,delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a396,delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: 0 in BEnv (fromList [i]):[a396,delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: forall<e,a> ex1/@select in BEnv (fromList [i]):[a396,delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: ex1/@select in BEnv (fromList [i]):[a396,delim]@[(benchmarks:326,[a374,a371,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex1(_, (@ctl-ex1)) : analysis/aac/benchmarks/ex1<e,a> )
       -> @ctl-ex1;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a396,delim]@[(benchmarks:326,[a374,a371,top])]
Matched [a374,a371,top]@[]
Evaluating: a in BEnv (fromList [a]):[a374,a371,top]@[]
Evaluating: 1 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 10 - simple");
(fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open((+))(a, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open(ex1)(0));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 10 - simple") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 10 - simple" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open((+))(a, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open(ex1)(0));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open((+))(a, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  @open(ex1)(0);
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
      (resume((@open((+))(a, 1))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex1/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
    (resume((@open((+))(a, 1))));
  })))) in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: @open(clause-control1)((fn(a, resume){
  (resume((@open((+))(a, 1))));
})) in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: fn(a, resume){
  resume((@open((+))(a, 1)));
} in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a416,top]@[]
Evaluating: @hhandle(ex1/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a419,a416,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a419,a416,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a419,a416,top]@[]
Evaluating: ex1/@tag in BEnv (fromList [action,hnd,ret]):[a419,a416,top]@[]
Evaluating: @open(@new-htag)("ex1@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex1@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a419,a416,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a419,a416,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a419,a416,top]@[]
OPS analysis/aac/benchmarks/ex1 fvs: BEnv (fromList []):[a419,a416,top]@[]
Evaluating: @open(ex1)(0) in BEnv (fromList []):[delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: ex1 in BEnv (fromList []):[delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i);
} in BEnv (fromList []):[top]@[]
Evaluating: 0 in BEnv (fromList []):[delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i) in BEnv (fromList [i]):[a452,delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a452,delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a452,delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a452,delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a452,delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a452,delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a452,delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a452,delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: 0 in BEnv (fromList [i]):[a452,delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: forall<e,a> ex1/@select in BEnv (fromList [i]):[a452,delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: ex1/@select in BEnv (fromList [i]):[a452,delim]@[(benchmarks:326,[a419,a416,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex1(_, (@ctl-ex1)) : analysis/aac/benchmarks/ex1<e,a> )
       -> @ctl-ex1;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a452,delim]@[(benchmarks:326,[a419,a416,top])]
Matched [a419,a416,top]@[]
Evaluating: resume((@open((+))(a, 1))) in BEnv (fromList [a,resume]):[a419,a416,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a419,a416,top]@[]
Evaluating: @open((+))(a, 1) in BEnv (fromList [a,resume]):[a419,a416,top]@[]
Evaluating: (+) in BEnv (fromList [a,resume]):[a419,a416,top]@[]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a419,a416,top]@[]
Evaluating: 1 in BEnv (fromList [a,resume]):[a419,a416,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a438,a419,a416,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a438,a419,a416,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a438,a419,a416,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a438,a419,a416,top]@[]
Applying continuation benchmarks:436 rebinding BEnv (fromList [])
Evaluating: 1 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 121 - simple cont");
(fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open((+))(a, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open(ex1)(0)), 1));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 121 - simple cont") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 121 - simple cont" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open((+))(a, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open(ex1)(0)), 1));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open((+))(a, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  @open((+))((@open(ex1)(0)), 1);
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
      (resume((@open((+))(a, 1))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex1/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
    (resume((@open((+))(a, 1))));
  })))) in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: @open(clause-control1)((fn(a, resume){
  (resume((@open((+))(a, 1))));
})) in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: fn(a, resume){
  resume((@open((+))(a, 1)));
} in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a472,top]@[]
Evaluating: @hhandle(ex1/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a475,a472,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a475,a472,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a475,a472,top]@[]
Evaluating: ex1/@tag in BEnv (fromList [action,hnd,ret]):[a475,a472,top]@[]
Evaluating: @open(@new-htag)("ex1@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex1@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a475,a472,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a475,a472,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a475,a472,top]@[]
OPS analysis/aac/benchmarks/ex1 fvs: BEnv (fromList []):[a475,a472,top]@[]
Evaluating: @open((+))((@open(ex1)(0)), 1) in BEnv (fromList []):[delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(ex1)(0) in BEnv (fromList []):[delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: ex1 in BEnv (fromList []):[delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i);
} in BEnv (fromList []):[top]@[]
Evaluating: 0 in BEnv (fromList []):[delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i) in BEnv (fromList [i]):[a510,delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a510,delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a510,delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a510,delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a510,delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a510,delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a510,delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a510,delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: 0 in BEnv (fromList [i]):[a510,delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: forall<e,a> ex1/@select in BEnv (fromList [i]):[a510,delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: ex1/@select in BEnv (fromList [i]):[a510,delim]@[(benchmarks:326,[a475,a472,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex1(_, (@ctl-ex1)) : analysis/aac/benchmarks/ex1<e,a> )
       -> @ctl-ex1;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a510,delim]@[(benchmarks:326,[a475,a472,top])]
Matched [a475,a472,top]@[]
Evaluating: resume((@open((+))(a, 1))) in BEnv (fromList [a,resume]):[a475,a472,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a475,a472,top]@[]
Evaluating: @open((+))(a, 1) in BEnv (fromList [a,resume]):[a475,a472,top]@[]
Evaluating: (+) in BEnv (fromList [a,resume]):[a475,a472,top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a475,a472,top]@[]
Evaluating: 1 in BEnv (fromList [a,resume]):[a475,a472,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a494,a475,a472,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a494,a475,a472,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a494,a475,a472,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a494,a475,a472,top]@[]
Applying continuation benchmarks:492 rebinding BEnv (fromList [])
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:492,[a492,a475,a472,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a508,delim]@[(benchmarks:492,[a492,a475,a472,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a508,delim]@[(benchmarks:492,[a492,a475,a472,top])]
Evaluating: x in BEnv (fromList [x,y]):[a508,delim]@[(benchmarks:492,[a492,a475,a472,top])]
Evaluating: y in BEnv (fromList [x,y]):[a508,delim]@[(benchmarks:492,[a492,a475,a472,top])]
Evaluating: 2 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 122 - simple cont");
(fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open((+))(a, 1)))), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open(ex1)(0));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 122 - simple cont") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 122 - simple cont" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open((+))(a, 1)))), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open(ex1)(0));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open((+))(a, 1)))), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  @open(ex1)(0);
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open((+))(a, 1)))), 1));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex1/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open((+))(a, 1)))), 1));
  })))) in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open((+))(a, 1)))), 1));
})) in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: fn(a, resume){
  @open((+))((resume((@open((+))(a, 1)))), 1);
} in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a536,top]@[]
Evaluating: @hhandle(ex1/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a539,a536,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a539,a536,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a539,a536,top]@[]
Evaluating: ex1/@tag in BEnv (fromList [action,hnd,ret]):[a539,a536,top]@[]
Evaluating: @open(@new-htag)("ex1@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex1@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a539,a536,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a539,a536,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a539,a536,top]@[]
OPS analysis/aac/benchmarks/ex1 fvs: BEnv (fromList []):[a539,a536,top]@[]
Evaluating: @open(ex1)(0) in BEnv (fromList []):[delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: ex1 in BEnv (fromList []):[delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i);
} in BEnv (fromList []):[top]@[]
Evaluating: 0 in BEnv (fromList []):[delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i) in BEnv (fromList [i]):[a580,delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a580,delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a580,delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a580,delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a580,delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a580,delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a580,delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a580,delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: 0 in BEnv (fromList [i]):[a580,delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: forall<e,a> ex1/@select in BEnv (fromList [i]):[a580,delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: ex1/@select in BEnv (fromList [i]):[a580,delim]@[(benchmarks:326,[a539,a536,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex1(_, (@ctl-ex1)) : analysis/aac/benchmarks/ex1<e,a> )
       -> @ctl-ex1;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a580,delim]@[(benchmarks:326,[a539,a536,top])]
Matched [a539,a536,top]@[]
Evaluating: @open((+))((resume((@open((+))(a, 1)))), 1) in BEnv (fromList [a,resume]):[a539,a536,top]@[]
Evaluating: (+) in BEnv (fromList [a,resume]):[a539,a536,top]@[]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: resume((@open((+))(a, 1))) in BEnv (fromList [a,resume]):[a539,a536,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a539,a536,top]@[]
Evaluating: @open((+))(a, 1) in BEnv (fromList [a,resume]):[a539,a536,top]@[]
Evaluating: (+) in BEnv (fromList [a,resume]):[a539,a536,top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a539,a536,top]@[]
Evaluating: 1 in BEnv (fromList [a,resume]):[a539,a536,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a565,a539,a536,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a565,a539,a536,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a565,a539,a536,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a565,a539,a536,top]@[]
Applying continuation benchmarks:558 rebinding BEnv (fromList [])
Evaluating: 1 in BEnv (fromList [a,resume]):[a539,a536,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a556,a539,a536,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a556,a539,a536,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a556,a539,a536,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a556,a539,a536,top]@[]
Evaluating: 2 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 123 - simple cont2");
(fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open((+))(a, 1)))), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open(ex1)(0)), 1));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 123 - simple cont2") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 123 - simple cont2" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open((+))(a, 1)))), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open(ex1)(0)), 1));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open((+))(a, 1)))), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  @open((+))((@open(ex1)(0)), 1);
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open((+))(a, 1)))), 1));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex1/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open((+))(a, 1)))), 1));
  })))) in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open((+))(a, 1)))), 1));
})) in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: fn(a, resume){
  @open((+))((resume((@open((+))(a, 1)))), 1);
} in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a600,top]@[]
Evaluating: @hhandle(ex1/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a603,a600,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a603,a600,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a603,a600,top]@[]
Evaluating: ex1/@tag in BEnv (fromList [action,hnd,ret]):[a603,a600,top]@[]
Evaluating: @open(@new-htag)("ex1@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex1@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a603,a600,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a603,a600,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a603,a600,top]@[]
OPS analysis/aac/benchmarks/ex1 fvs: BEnv (fromList []):[a603,a600,top]@[]
Evaluating: @open((+))((@open(ex1)(0)), 1) in BEnv (fromList []):[delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(ex1)(0) in BEnv (fromList []):[delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: ex1 in BEnv (fromList []):[delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i);
} in BEnv (fromList []):[top]@[]
Evaluating: 0 in BEnv (fromList []):[delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i) in BEnv (fromList [i]):[a646,delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a646,delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a646,delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a646,delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a646,delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a646,delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a646,delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a646,delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: 0 in BEnv (fromList [i]):[a646,delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: forall<e,a> ex1/@select in BEnv (fromList [i]):[a646,delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: ex1/@select in BEnv (fromList [i]):[a646,delim]@[(benchmarks:326,[a603,a600,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex1(_, (@ctl-ex1)) : analysis/aac/benchmarks/ex1<e,a> )
       -> @ctl-ex1;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a646,delim]@[(benchmarks:326,[a603,a600,top])]
Matched [a603,a600,top]@[]
Evaluating: @open((+))((resume((@open((+))(a, 1)))), 1) in BEnv (fromList [a,resume]):[a603,a600,top]@[]
Evaluating: (+) in BEnv (fromList [a,resume]):[a603,a600,top]@[]
Evaluating: resume((@open((+))(a, 1))) in BEnv (fromList [a,resume]):[a603,a600,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a603,a600,top]@[]
Evaluating: @open((+))(a, 1) in BEnv (fromList [a,resume]):[a603,a600,top]@[]
Evaluating: (+) in BEnv (fromList [a,resume]):[a603,a600,top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a603,a600,top]@[]
Evaluating: 1 in BEnv (fromList [a,resume]):[a603,a600,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a629,a603,a600,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a629,a603,a600,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a629,a603,a600,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a629,a603,a600,top]@[]
Applying continuation benchmarks:622 rebinding BEnv (fromList [])
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:622,[a622,a603,a600,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a644,delim]@[(benchmarks:622,[a622,a603,a600,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a644,delim]@[(benchmarks:622,[a622,a603,a600,top])]
Evaluating: x in BEnv (fromList [x,y]):[a644,delim]@[(benchmarks:622,[a622,a603,a600,top])]
Evaluating: y in BEnv (fromList [x,y]):[a644,delim]@[(benchmarks:622,[a622,a603,a600,top])]
Evaluating: 1 in BEnv (fromList [a,resume]):[a603,a600,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a620,a603,a600,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a620,a603,a600,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a620,a603,a600,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a620,a603,a600,top]@[]
Evaluating: 3 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 20 - nondeterminism");
(fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open(ex2)((Tuple2(1, 2))));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 20 - nondeterminism") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 20 - nondeterminism" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open(ex2)((Tuple2(1, 2))));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  @open(ex2)((Tuple2(1, 2)));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
    }))))), (fn(x){
    x;
  }), @action) in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: ex2/@handle in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: ex2/@handle in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex2/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
  })))) in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: @Hnd-ex2 in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: @Hnd-ex2 in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
})) in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: fn(a, resume){
  @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))));
} in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: fn(x){
  x;
} in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a726,top]@[]
Evaluating: @hhandle(ex2/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a729,a726,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a729,a726,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a729,a726,top]@[]
Evaluating: ex2/@tag in BEnv (fromList [action,hnd,ret]):[a729,a726,top]@[]
Evaluating: @open(@new-htag)("ex2@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex2@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a729,a726,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a729,a726,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a729,a726,top]@[]
OPS analysis/aac/benchmarks/ex2 fvs: BEnv (fromList []):[a729,a726,top]@[]
Evaluating: @open(ex2)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: ex2 in BEnv (fromList []):[delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a) in BEnv (fromList [a]):[a777,delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a777,delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a777,delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a777,delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a777,delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a777,delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a777,delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a777,delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: 0 in BEnv (fromList [a]):[a777,delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: forall<e,a> ex2/@select in BEnv (fromList [a]):[a777,delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: ex2/@select in BEnv (fromList [a]):[a777,delim]@[(benchmarks:681,[a729,a726,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex2(_, (@ctl-ex2)) : analysis/aac/benchmarks/ex2<e,a> )
       -> @ctl-ex2;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a777,delim]@[(benchmarks:681,[a729,a726,top])]
Matched [a729,a726,top]@[]
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))) in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: (+) in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a755,a729,a726,top]@[]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a755,a729,a726,top]@[]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a755,a729,a726,top]@[]
Applying continuation benchmarks:748 rebinding BEnv (fromList [])
Evaluating: resume((@open(tuple2/snd)(a))) in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: @open(tuple2/snd)(a) in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2(_, (@x)) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a729,a726,top]@[]
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a765,a729,a726,top]@[]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a765,a729,a726,top]@[]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a765,a729,a726,top]@[]
Applying continuation benchmarks:749 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a746,a729,a726,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a746,a729,a726,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a746,a729,a726,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a746,a729,a726,top]@[]
Evaluating: 3 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 20-1 - nondeterminism");
(fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume(2)), (resume(3))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex1)(1)), 1));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 20-1 - nondeterminism") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 20-1 - nondeterminism" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume(2)), (resume(3))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex1)(1)), 1));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume(2)), (resume(3))));
      }))))), (fn(x){
      x;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  @open((+))((@open(ex1)(1)), 1);
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume(2)), (resume(3))));
    }))))), (fn(x){
    x;
  }), @action) in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex1/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume(2)), (resume(3))));
  })))) in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume(2)), (resume(3))));
})) in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: fn(a, resume){
  @open((+))((resume(2)), (resume(3)));
} in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: fn(x){
  x;
} in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a802,top]@[]
Evaluating: @hhandle(ex1/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a805,a802,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a805,a802,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a805,a802,top]@[]
Evaluating: ex1/@tag in BEnv (fromList [action,hnd,ret]):[a805,a802,top]@[]
Evaluating: @open(@new-htag)("ex1@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex1@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a805,a802,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a805,a802,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a805,a802,top]@[]
OPS analysis/aac/benchmarks/ex1 fvs: BEnv (fromList []):[a805,a802,top]@[]
Evaluating: @open((+))((@open(ex1)(1)), 1) in BEnv (fromList []):[delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(ex1)(1) in BEnv (fromList []):[delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: ex1 in BEnv (fromList []):[delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i) in BEnv (fromList [i]):[a843,delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a843,delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a843,delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a843,delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a843,delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a843,delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a843,delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a843,delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: 0 in BEnv (fromList [i]):[a843,delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: forall<e,a> ex1/@select in BEnv (fromList [i]):[a843,delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: ex1/@select in BEnv (fromList [i]):[a843,delim]@[(benchmarks:326,[a805,a802,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex1(_, (@ctl-ex1)) : analysis/aac/benchmarks/ex1<e,a> )
       -> @ctl-ex1;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a843,delim]@[(benchmarks:326,[a805,a802,top])]
Matched [a805,a802,top]@[]
Evaluating: @open((+))((resume(2)), (resume(3))) in BEnv (fromList [resume]):[a805,a802,top]@[]
Evaluating: (+) in BEnv (fromList [resume]):[a805,a802,top]@[]
Evaluating: resume(2) in BEnv (fromList [resume]):[a805,a802,top]@[]
Evaluating: resume in BEnv (fromList [resume]):[a805,a802,top]@[]
Evaluating: 2 in BEnv (fromList [resume]):[a805,a802,top]@[]
Applying continuation benchmarks:824 rebinding BEnv (fromList [])
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:824,[a824,a805,a802,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a841,delim]@[(benchmarks:824,[a824,a805,a802,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a841,delim]@[(benchmarks:824,[a824,a805,a802,top])]
Evaluating: x in BEnv (fromList [x,y]):[a841,delim]@[(benchmarks:824,[a824,a805,a802,top])]
Evaluating: y in BEnv (fromList [x,y]):[a841,delim]@[(benchmarks:824,[a824,a805,a802,top])]
Evaluating: resume(3) in BEnv (fromList [resume]):[a805,a802,top]@[]
Evaluating: resume in BEnv (fromList [resume]):[a805,a802,top]@[]
Evaluating: 3 in BEnv (fromList [resume]):[a805,a802,top]@[]
Applying continuation benchmarks:825 rebinding BEnv (fromList [])
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:825,[a825,a805,a802,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a841,delim]@[(benchmarks:825,[a825,a805,a802,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a841,delim]@[(benchmarks:825,[a825,a805,a802,top])]
Evaluating: x in BEnv (fromList [x,y]):[a841,delim]@[(benchmarks:825,[a825,a805,a802,top])]
Evaluating: y in BEnv (fromList [x,y]):[a841,delim]@[(benchmarks:825,[a825,a805,a802,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a822,a805,a802,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a822,a805,a802,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a822,a805,a802,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a822,a805,a802,top]@[]
Evaluating: 7 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 21 - nondeterminism");
(fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex2)((Tuple2(1, 2)))), 1));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 21 - nondeterminism") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 21 - nondeterminism" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex2)((Tuple2(1, 2)))), 1));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  @open((+))((@open(ex2)((Tuple2(1, 2)))), 1);
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
    }))))), (fn(x){
    x;
  }), @action) in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: ex2/@handle in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: ex2/@handle in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex2/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
  })))) in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: @Hnd-ex2 in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: @Hnd-ex2 in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
})) in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: fn(a, resume){
  @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))));
} in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: fn(x){
  x;
} in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a869,top]@[]
Evaluating: @hhandle(ex2/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a872,a869,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a872,a869,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a872,a869,top]@[]
Evaluating: ex2/@tag in BEnv (fromList [action,hnd,ret]):[a872,a869,top]@[]
Evaluating: @open(@new-htag)("ex2@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex2@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a872,a869,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a872,a869,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a872,a869,top]@[]
OPS analysis/aac/benchmarks/ex2 fvs: BEnv (fromList []):[a872,a869,top]@[]
Evaluating: @open((+))((@open(ex2)((Tuple2(1, 2)))), 1) in BEnv (fromList []):[delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(ex2)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: ex2 in BEnv (fromList []):[delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a) in BEnv (fromList [a]):[a922,delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a922,delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a922,delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a922,delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a922,delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a922,delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a922,delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a922,delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: 0 in BEnv (fromList [a]):[a922,delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: forall<e,a> ex2/@select in BEnv (fromList [a]):[a922,delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: ex2/@select in BEnv (fromList [a]):[a922,delim]@[(benchmarks:681,[a872,a869,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex2(_, (@ctl-ex2)) : analysis/aac/benchmarks/ex2<e,a> )
       -> @ctl-ex2;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a922,delim]@[(benchmarks:681,[a872,a869,top])]
Matched [a872,a869,top]@[]
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))) in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: (+) in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a898,a872,a869,top]@[]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a898,a872,a869,top]@[]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a898,a872,a869,top]@[]
Applying continuation benchmarks:891 rebinding BEnv (fromList [])
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:891,[a891,a872,a869,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a920,delim]@[(benchmarks:891,[a891,a872,a869,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a920,delim]@[(benchmarks:891,[a891,a872,a869,top])]
Evaluating: x in BEnv (fromList [x,y]):[a920,delim]@[(benchmarks:891,[a891,a872,a869,top])]
Evaluating: y in BEnv (fromList [x,y]):[a920,delim]@[(benchmarks:891,[a891,a872,a869,top])]
Evaluating: resume((@open(tuple2/snd)(a))) in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: @open(tuple2/snd)(a) in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2(_, (@x)) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a872,a869,top]@[]
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a908,a872,a869,top]@[]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a908,a872,a869,top]@[]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a908,a872,a869,top]@[]
Applying continuation benchmarks:892 rebinding BEnv (fromList [])
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:892,[a892,a872,a869,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a920,delim]@[(benchmarks:892,[a892,a872,a869,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a920,delim]@[(benchmarks:892,[a892,a872,a869,top])]
Evaluating: x in BEnv (fromList [x,y]):[a920,delim]@[(benchmarks:892,[a892,a872,a869,top])]
Evaluating: y in BEnv (fromList [x,y]):[a920,delim]@[(benchmarks:892,[a892,a872,a869,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a889,a872,a869,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a889,a872,a869,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a889,a872,a869,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a889,a872,a869,top]@[]
Evaluating: 5 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 22 - nondeterminism twice");
(fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2))))));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 22 - nondeterminism twice") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 22 - nondeterminism twice" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2))))));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(x){
      x;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2)))));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex2/@handle((@Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
    }))))), (fn(x){
    x;
  }), @action) in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: ex2/@handle in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: ex2/@handle in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex2/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex2(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
  })))) in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: @Hnd-ex2 in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: @Hnd-ex2 in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
})) in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: fn(a, resume){
  @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))));
} in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: fn(x){
  x;
} in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a953,top]@[]
Evaluating: @hhandle(ex2/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a956,a953,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a956,a953,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a956,a953,top]@[]
Evaluating: ex2/@tag in BEnv (fromList [action,hnd,ret]):[a956,a953,top]@[]
Evaluating: @open(@new-htag)("ex2@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex2@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a956,a953,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a956,a953,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a956,a953,top]@[]
OPS analysis/aac/benchmarks/ex2 fvs: BEnv (fromList []):[a956,a953,top]@[]
Evaluating: @open((+))((@open(ex2)((Tuple2(1, 2)))), (@open(ex2)((Tuple2(1, 2))))) in BEnv (fromList []):[delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(ex2)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: ex2 in BEnv (fromList []):[delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a) in BEnv (fromList [a]):[a1006,delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1006,delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1006,delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1006,delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1006,delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1006,delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1006,delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1006,delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1006,delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: forall<e,a> ex2/@select in BEnv (fromList [a]):[a1006,delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: ex2/@select in BEnv (fromList [a]):[a1006,delim]@[(benchmarks:681,[a956,a953,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex2(_, (@ctl-ex2)) : analysis/aac/benchmarks/ex2<e,a> )
       -> @ctl-ex2;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a1006,delim]@[(benchmarks:681,[a956,a953,top])]
Matched [a956,a953,top]@[]
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))) in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: (+) in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a982,a956,a953,top]@[]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a982,a956,a953,top]@[]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a982,a956,a953,top]@[]
Applying continuation benchmarks:975 rebinding BEnv (fromList [])
Evaluating: @open(ex2)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: ex2 in BEnv (fromList []):[delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a) in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: forall<e,a> ex2/@select in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: ex2/@select in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:975,[a975,a956,a953,top])]
Evaluating: a in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:975,[a975,a956,a953,top])]
Matched [a975,a956,a953,top]@[]
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))) in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: (+) in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a982,a975,a956,a953,top]@[]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a982,a975,a956,a953,top]@[]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a982,a975,a956,a953,top]@[]
Applying continuation benchmarks:975 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:975,[a975,a975,a956,a953,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:975,[a975,a975,a956,a953,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:975,[a975,a975,a956,a953,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:975,[a975,a975,a956,a953,top])]
Evaluating: resume((@open(tuple2/snd)(a))) in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: @open(tuple2/snd)(a) in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2(_, (@x)) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a975,a956,a953,top]@[]
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a992,a975,a956,a953,top]@[]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a992,a975,a956,a953,top]@[]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a992,a975,a956,a953,top]@[]
Applying continuation benchmarks:976 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:976,[a976,a975,a956,a953,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:976,[a976,a975,a956,a953,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:976,[a976,a975,a956,a953,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:976,[a976,a975,a956,a953,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a973,a975,a956,a953,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a973,a975,a956,a953,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a973,a975,a956,a953,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a973,a975,a956,a953,top]@[]
Evaluating: resume((@open(tuple2/snd)(a))) in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: @open(tuple2/snd)(a) in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a956,a953,top]@[]
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a992,a956,a953,top]@[]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a992,a956,a953,top]@[]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a992,a956,a953,top]@[]
Applying continuation benchmarks:976 rebinding BEnv (fromList [])
Evaluating: @open(ex2)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: ex2 in BEnv (fromList []):[delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex2/@select), a) in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: forall<e,a> ex2/@select in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: ex2/@select in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:976,[a976,a956,a953,top])]
Evaluating: a in BEnv (fromList [a]):[a1007,delim]@[(benchmarks:976,[a976,a956,a953,top])]
Matched [a976,a956,a953,top]@[]
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))) in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: (+) in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a982,a976,a956,a953,top]@[]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a982,a976,a956,a953,top]@[]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a982,a976,a956,a953,top]@[]
Applying continuation benchmarks:975 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:975,[a975,a976,a956,a953,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:975,[a975,a976,a956,a953,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:975,[a975,a976,a956,a953,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:975,[a975,a976,a956,a953,top])]
Evaluating: resume((@open(tuple2/snd)(a))) in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: resume in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: @open(tuple2/snd)(a) in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a976,a956,a953,top]@[]
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a992,a976,a956,a953,top]@[]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a992,a976,a956,a953,top]@[]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a992,a976,a956,a953,top]@[]
Applying continuation benchmarks:976 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:976,[a976,a976,a956,a953,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:976,[a976,a976,a956,a953,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:976,[a976,a976,a956,a953,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1004,delim]@[(benchmarks:976,[a976,a976,a956,a953,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a973,a976,a956,a953,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a973,a976,a956,a953,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a973,a976,a956,a953,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a973,a976,a956,a953,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a973,a956,a953,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a973,a956,a953,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a973,a956,a953,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a973,a956,a953,top]@[]
Evaluating: 12 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 23 - nondeterminism twice");
(fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume(3)), (resume(4))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex1)(1)), (@open(ex1)(2))));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 23 - nondeterminism twice") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 23 - nondeterminism twice" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume(3)), (resume(4))));
      }))))), (fn(x){
      x;
    }), @action);
})((fn(){
  (@open((+))((@open(ex1)(1)), (@open(ex1)(2))));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume(3)), (resume(4))));
      }))))), (fn(x){
      x;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  @open((+))((@open(ex1)(1)), (@open(ex1)(2)));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex1/@handle((@Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume(3)), (resume(4))));
    }))))), (fn(x){
    x;
  }), @action) in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: ex1/@handle in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex1/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex1(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume(3)), (resume(4))));
  })))) in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: @Hnd-ex1 in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume(3)), (resume(4))));
})) in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: fn(a, resume){
  @open((+))((resume(3)), (resume(4)));
} in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: fn(x){
  x;
} in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a1048,top]@[]
Evaluating: @hhandle(ex1/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1051,a1048,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1051,a1048,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1051,a1048,top]@[]
Evaluating: ex1/@tag in BEnv (fromList [action,hnd,ret]):[a1051,a1048,top]@[]
Evaluating: @open(@new-htag)("ex1@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex1@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1051,a1048,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1051,a1048,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1051,a1048,top]@[]
OPS analysis/aac/benchmarks/ex1 fvs: BEnv (fromList []):[a1051,a1048,top]@[]
Evaluating: @open((+))((@open(ex1)(1)), (@open(ex1)(2))) in BEnv (fromList []):[delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(ex1)(1) in BEnv (fromList []):[delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: ex1 in BEnv (fromList []):[delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i) in BEnv (fromList [i]):[a1089,delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a1089,delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a1089,delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a1089,delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a1089,delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a1089,delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a1089,delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a1089,delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: 0 in BEnv (fromList [i]):[a1089,delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: forall<e,a> ex1/@select in BEnv (fromList [i]):[a1089,delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: ex1/@select in BEnv (fromList [i]):[a1089,delim]@[(benchmarks:326,[a1051,a1048,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex1(_, (@ctl-ex1)) : analysis/aac/benchmarks/ex1<e,a> )
       -> @ctl-ex1;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a1089,delim]@[(benchmarks:326,[a1051,a1048,top])]
Matched [a1051,a1048,top]@[]
Evaluating: @open((+))((resume(3)), (resume(4))) in BEnv (fromList [resume]):[a1051,a1048,top]@[]
Evaluating: (+) in BEnv (fromList [resume]):[a1051,a1048,top]@[]
Evaluating: resume(3) in BEnv (fromList [resume]):[a1051,a1048,top]@[]
Evaluating: resume in BEnv (fromList [resume]):[a1051,a1048,top]@[]
Evaluating: 3 in BEnv (fromList [resume]):[a1051,a1048,top]@[]
Applying continuation benchmarks:1070 rebinding BEnv (fromList [])
Evaluating: @open(ex1)(2) in BEnv (fromList []):[delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: ex1 in BEnv (fromList []):[delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i) in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: 0 in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: forall<e,a> ex1/@select in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: ex1/@select in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Evaluating: i in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1070,[a1070,a1051,a1048,top])]
Matched [a1070,a1051,a1048,top]@[]
Evaluating: @open((+))((resume(3)), (resume(4))) in BEnv (fromList [resume]):[a1070,a1051,a1048,top]@[]
Evaluating: (+) in BEnv (fromList [resume]):[a1070,a1051,a1048,top]@[]
Evaluating: resume(3) in BEnv (fromList [resume]):[a1070,a1051,a1048,top]@[]
Evaluating: resume in BEnv (fromList [resume]):[a1070,a1051,a1048,top]@[]
Evaluating: 3 in BEnv (fromList [resume]):[a1070,a1051,a1048,top]@[]
Applying continuation benchmarks:1070 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1070,[a1070,a1070,a1051,a1048,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1070,[a1070,a1070,a1051,a1048,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1070,[a1070,a1070,a1051,a1048,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1070,[a1070,a1070,a1051,a1048,top])]
Evaluating: resume(4) in BEnv (fromList [resume]):[a1070,a1051,a1048,top]@[]
Evaluating: resume in BEnv (fromList [resume]):[a1070,a1051,a1048,top]@[]
Evaluating: 4 in BEnv (fromList [resume]):[a1070,a1051,a1048,top]@[]
Applying continuation benchmarks:1071 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1071,[a1071,a1070,a1051,a1048,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1071,[a1071,a1070,a1051,a1048,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1071,[a1071,a1070,a1051,a1048,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1071,[a1071,a1070,a1051,a1048,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1068,a1070,a1051,a1048,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a1068,a1070,a1051,a1048,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a1068,a1070,a1051,a1048,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a1068,a1070,a1051,a1048,top]@[]
Evaluating: resume(4) in BEnv (fromList [resume]):[a1051,a1048,top]@[]
Evaluating: resume in BEnv (fromList [resume]):[a1051,a1048,top]@[]
Evaluating: 4 in BEnv (fromList [resume]):[a1051,a1048,top]@[]
Applying continuation benchmarks:1071 rebinding BEnv (fromList [])
Evaluating: @open(ex1)(2) in BEnv (fromList []):[delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: ex1 in BEnv (fromList []):[delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex1/@select), i) in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: 0 in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: forall<e,a> ex1/@select in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: ex1/@select in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Evaluating: i in BEnv (fromList [i]):[a1090,delim]@[(benchmarks:1071,[a1071,a1051,a1048,top])]
Matched [a1071,a1051,a1048,top]@[]
Evaluating: @open((+))((resume(3)), (resume(4))) in BEnv (fromList [resume]):[a1071,a1051,a1048,top]@[]
Evaluating: (+) in BEnv (fromList [resume]):[a1071,a1051,a1048,top]@[]
Evaluating: resume(3) in BEnv (fromList [resume]):[a1071,a1051,a1048,top]@[]
Evaluating: resume in BEnv (fromList [resume]):[a1071,a1051,a1048,top]@[]
Evaluating: 3 in BEnv (fromList [resume]):[a1071,a1051,a1048,top]@[]
Applying continuation benchmarks:1070 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1070,[a1070,a1071,a1051,a1048,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1070,[a1070,a1071,a1051,a1048,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1070,[a1070,a1071,a1051,a1048,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1070,[a1070,a1071,a1051,a1048,top])]
Evaluating: resume(4) in BEnv (fromList [resume]):[a1071,a1051,a1048,top]@[]
Evaluating: resume in BEnv (fromList [resume]):[a1071,a1051,a1048,top]@[]
Evaluating: 4 in BEnv (fromList [resume]):[a1071,a1051,a1048,top]@[]
Applying continuation benchmarks:1071 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1071,[a1071,a1071,a1051,a1048,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1071,[a1071,a1071,a1051,a1048,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1071,[a1071,a1071,a1051,a1048,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1087,delim]@[(benchmarks:1071,[a1071,a1071,a1051,a1048,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1068,a1071,a1051,a1048,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a1068,a1071,a1051,a1048,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a1068,a1071,a1051,a1048,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a1068,a1071,a1051,a1048,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1068,a1051,a1048,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a1068,a1051,a1048,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a1068,a1051,a1048,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a1068,a1051,a1048,top]@[]
Evaluating: 28 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 3 nested effects");
(fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex32/@handle((@Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
          (resume((@open(ex31)(y))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(ex32)(1));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 3 nested effects") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 3 nested effects" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex32/@handle((@Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
          (resume((@open(ex31)(y))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(ex32)(1));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex32/@handle((@Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
          (resume((@open(ex31)(y))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(ex32)(1));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
      (@open((+))((resume(z)), 1));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: ex31/@handle in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: ex31/@handle in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex31/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
    (@open((+))((resume(z)), 1));
  })))) in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: @Hnd-ex31 in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: @Hnd-ex31 in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (@open((+))((resume(z)), 1));
})) in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: fn(z, resume){
  @open((+))((resume(z)), 1);
} in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a1283,top]@[]
Evaluating: @hhandle(ex31/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1286,a1283,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1286,a1283,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1286,a1283,top]@[]
Evaluating: ex31/@tag in BEnv (fromList [action,hnd,ret]):[a1286,a1283,top]@[]
Evaluating: @open(@new-htag)("ex31@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex31@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1286,a1283,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1286,a1283,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1286,a1283,top]@[]
OPS analysis/aac/benchmarks/ex31 fvs: BEnv (fromList []):[a1286,a1283,top]@[]
Evaluating: (fn(@action){
  ex32/@handle((@Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
        (resume((@open(ex31)(y))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open(ex32)(1));
})) in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: fn(@action){
  ex32/@handle((@Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
        (resume((@open(ex31)(y))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: fn(){
  @open(ex32)(1);
} in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: ex32/@handle((@Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
      (resume((@open(ex31)(y))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: ex32/@handle in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: ex32/@handle in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex32/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
    (resume((@open(ex31)(y))));
  })))) in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @Hnd-ex32 in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @Hnd-ex32 in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @open(clause-control1)((fn(y, resume){
  (resume((@open(ex31)(y))));
})) in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: fn(y, resume){
  resume((@open(ex31)(y)));
} in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @action in BEnv (fromList [@action]):[a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @hhandle(ex32/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: ex32/@tag in BEnv (fromList [action,hnd,ret]):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @open(@new-htag)("ex32@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex32@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
OPS analysis/aac/benchmarks/ex32 fvs: BEnv (fromList []):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @open(ex32)(1) in BEnv (fromList []):[delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: ex32 in BEnv (fromList []):[delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex32/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex32/@select), a) in BEnv (fromList [a]):[a1353,delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1353,delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1353,delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1353,delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1353,delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1353,delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1353,delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1353,delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1353,delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: forall<e,a> ex32/@select in BEnv (fromList [a]):[a1353,delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: ex32/@select in BEnv (fromList [a]):[a1353,delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex32(_, (@ctl-ex32)) : analysis/aac/benchmarks/ex32<e,a> )
       -> @ctl-ex32;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a1353,delim]@[(benchmarks:1184,[a1322,a1319,delim]),(benchmarks:1130,[a1286,a1283,top])]
Matched [a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: resume((@open(ex31)(y))) in BEnv (fromList [resume,y]):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: resume in BEnv (fromList [resume,y]):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @open(ex31)(y) in BEnv (fromList [resume,y]):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: ex31 in BEnv (fromList [resume,y]):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex31/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: y in BEnv (fromList [resume,y]):[a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex31/@select), a) in BEnv (fromList [a]):[a1341,a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1341,a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1341,a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1341,a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1341,a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1341,a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1341,a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1341,a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1341,a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: forall<e,a> ex31/@select in BEnv (fromList [a]):[a1341,a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: ex31/@select in BEnv (fromList [a]):[a1341,a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex31(_, (@ctl-ex31)) : analysis/aac/benchmarks/ex31<e,a> )
       -> @ctl-ex31;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a1341,a1322,a1319,delim]@[(benchmarks:1130,[a1286,a1283,top])]
Matched [a1286,a1283,top]@[]
Evaluating: @open((+))((resume(z)), 1) in BEnv (fromList [resume,z]):[a1286,a1283,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a1286,a1283,top]@[]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: resume(z) in BEnv (fromList [resume,z]):[a1286,a1283,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a1286,a1283,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a1286,a1283,top]@[]
Applying continuation benchmarks:1305 rebinding BEnv (fromList [])
Applying continuation benchmarks:1339 rebinding BEnv (fromList [])
Evaluating: 1 in BEnv (fromList [resume,z]):[a1286,a1283,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1303,a1286,a1283,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a1303,a1286,a1283,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a1303,a1286,a1283,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a1303,a1286,a1283,top]@[]
Evaluating: 2 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 30 nested effects");
(fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex32/@handle((@Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
          (resume((@open(ex31)(y))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(ex31)(1));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 30 nested effects") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 30 nested effects" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex32/@handle((@Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
          (resume((@open(ex31)(y))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(ex31)(1));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex32/@handle((@Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
          (resume((@open(ex31)(y))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(ex31)(1));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
      (@open((+))((resume(z)), 1));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: ex31/@handle in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: ex31/@handle in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex31/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
    (@open((+))((resume(z)), 1));
  })))) in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: @Hnd-ex31 in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: @Hnd-ex31 in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (@open((+))((resume(z)), 1));
})) in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: fn(z, resume){
  @open((+))((resume(z)), 1);
} in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a1373,top]@[]
Evaluating: @hhandle(ex31/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1376,a1373,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1376,a1373,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1376,a1373,top]@[]
Evaluating: ex31/@tag in BEnv (fromList [action,hnd,ret]):[a1376,a1373,top]@[]
Evaluating: @open(@new-htag)("ex31@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex31@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1376,a1373,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1376,a1373,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1376,a1373,top]@[]
OPS analysis/aac/benchmarks/ex31 fvs: BEnv (fromList []):[a1376,a1373,top]@[]
Evaluating: (fn(@action){
  ex32/@handle((@Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
        (resume((@open(ex31)(y))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open(ex31)(1));
})) in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: fn(@action){
  ex32/@handle((@Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
        (resume((@open(ex31)(y))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: fn(){
  @open(ex31)(1);
} in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: ex32/@handle((@Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
      (resume((@open(ex31)(y))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: ex32/@handle in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: ex32/@handle in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex32/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex32(3, (@open(clause-control1)((fn(y, resume){
    (resume((@open(ex31)(y))));
  })))) in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @Hnd-ex32 in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @Hnd-ex32 in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @open(clause-control1)((fn(y, resume){
  (resume((@open(ex31)(y))));
})) in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: fn(y, resume){
  resume((@open(ex31)(y)));
} in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @action in BEnv (fromList [@action]):[a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @hhandle(ex32/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1412,a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1412,a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1412,a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: ex32/@tag in BEnv (fromList [action,hnd,ret]):[a1412,a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @open(@new-htag)("ex32@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex32@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1412,a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1412,a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1412,a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
OPS analysis/aac/benchmarks/ex32 fvs: BEnv (fromList []):[a1412,a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @open(ex31)(1) in BEnv (fromList []):[delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: ex31 in BEnv (fromList []):[delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex31/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex31/@select), a) in BEnv (fromList [a]):[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: forall<e,a> ex31/@select in BEnv (fromList [a]):[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: ex31/@select in BEnv (fromList [a]):[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex31(_, (@ctl-ex31)) : analysis/aac/benchmarks/ex31<e,a> )
       -> @ctl-ex31;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Link create IL@(1151:ex31:[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]) [a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Link create IL@(1151:ex31:[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]) [a1412,a1409,delim]@[(benchmarks:1130,[a1376,a1373,top])]
Matched [a1376,a1373,top]@[]
Evaluating: @open((+))((resume(z)), 1) in BEnv (fromList [resume,z]):[a1376,a1373,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a1376,a1373,top]@[]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: resume(z) in BEnv (fromList [resume,z]):[a1376,a1373,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a1376,a1373,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a1376,a1373,top]@[]
Applying continuation benchmarks:1395 rebinding BEnv (fromList [])
Link restore IL@(1151:ex31:[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]) [a1443,delim]@[(benchmarks:1395,[a1395,a1376,a1373,top])]
Link restore IL@(1151:ex31:[a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]) [a1443,delim]@[(benchmarks:1184,[a1412,a1409,delim]),(benchmarks:1130,[a1376,a1373,top])]
Evaluating: 1 in BEnv (fromList [resume,z]):[a1376,a1373,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1393,a1376,a1373,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a1393,a1376,a1373,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a1393,a1376,a1373,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a1393,a1376,a1373,top]@[]
Evaluating: 2 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 31 - mixed effects op in handler after resume");
(fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex31)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))(1, (@open(ex33)((Tuple2(1, 2))))));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 31 - mixed effects op in handler after resume") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 31 - mixed effects op in handler after resume" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex31)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))(1, (@open(ex33)((Tuple2(1, 2))))));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex31)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))(1, (@open(ex33)((Tuple2(1, 2))))));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
      (@open((+))((resume(z)), 1));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: ex31/@handle in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: ex31/@handle in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex31/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
    (@open((+))((resume(z)), 1));
  })))) in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: @Hnd-ex31 in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: @Hnd-ex31 in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (@open((+))((resume(z)), 1));
})) in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: fn(z, resume){
  @open((+))((resume(z)), 1);
} in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a1463,top]@[]
Evaluating: @hhandle(ex31/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1466,a1463,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1466,a1463,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1466,a1463,top]@[]
Evaluating: ex31/@tag in BEnv (fromList [action,hnd,ret]):[a1466,a1463,top]@[]
Evaluating: @open(@new-htag)("ex31@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex31@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1466,a1463,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1466,a1463,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1466,a1463,top]@[]
OPS analysis/aac/benchmarks/ex31 fvs: BEnv (fromList []):[a1466,a1463,top]@[]
Evaluating: (fn(@action){
  ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex31)((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))(1, (@open(ex33)((Tuple2(1, 2))))));
})) in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: fn(@action){
  ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex31)((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: fn(){
  @open((+))(1, (@open(ex33)((Tuple2(1, 2)))));
} in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex31)((@open(tuple2/snd)(a))))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: ex33/@handle in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: ex33/@handle in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex33/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex31)((@open(tuple2/snd)(a))))));
  })))) in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @Hnd-ex33 in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @Hnd-ex33 in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex31)((@open(tuple2/snd)(a))))));
})) in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: fn(a, resume){
  @open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex31)((@open(tuple2/snd)(a)))));
} in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @action in BEnv (fromList [@action]):[a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @hhandle(ex33/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: ex33/@tag in BEnv (fromList [action,hnd,ret]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @open(@new-htag)("ex33@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex33@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
OPS analysis/aac/benchmarks/ex33 fvs: BEnv (fromList []):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @open((+))(1, (@open(ex33)((Tuple2(1, 2))))) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @open(ex33)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: ex33 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex33/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex33/@select), a) in BEnv (fromList [a]):[a1556,delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1556,delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1556,delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1556,delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1556,delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1556,delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1556,delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1556,delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1556,delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: forall<e,a> ex33/@select in BEnv (fromList [a]):[a1556,delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: ex33/@select in BEnv (fromList [a]):[a1556,delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex33(_, (@ctl-ex33)) : analysis/aac/benchmarks/ex33<e,a> )
       -> @ctl-ex33;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a1556,delim]@[(benchmarks:1238,[a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Matched [a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex31)((@open(tuple2/snd)(a))))) in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: (+) in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: resume in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a1528,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a1528,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a1528,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Applying continuation benchmarks:1521 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1553,delim]@[(benchmarks:1521,[a1521,a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1553,delim]@[(benchmarks:1521,[a1521,a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1553,delim]@[(benchmarks:1521,[a1521,a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1553,delim]@[(benchmarks:1521,[a1521,a1502,a1499,delim]),(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @open(ex31)((@open(tuple2/snd)(a))) in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: ex31 in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex31/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(tuple2/snd)(a) in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2(_, (@x)) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a1538,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a1538,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a1538,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex31/@select), a) in BEnv (fromList [a]):[a1522,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1522,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1522,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1522,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1522,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1522,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1522,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1522,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1522,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: forall<e,a> ex31/@select in BEnv (fromList [a]):[a1522,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: ex31/@select in BEnv (fromList [a]):[a1522,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex31(_, (@ctl-ex31)) : analysis/aac/benchmarks/ex31<e,a> )
       -> @ctl-ex31;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a1522,a1502,a1499,delim]@[(benchmarks:1130,[a1466,a1463,top])]
Matched [a1466,a1463,top]@[]
Evaluating: @open((+))((resume(z)), 1) in BEnv (fromList [resume,z]):[a1466,a1463,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a1466,a1463,top]@[]
Evaluating: resume(z) in BEnv (fromList [resume,z]):[a1466,a1463,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a1466,a1463,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a1466,a1463,top]@[]
Applying continuation benchmarks:1485 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1519,a1502,a1499,delim]@[(benchmarks:1485,[a1485,a1466,a1463,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1519,a1502,a1499,delim]@[(benchmarks:1485,[a1485,a1466,a1463,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1519,a1502,a1499,delim]@[(benchmarks:1485,[a1485,a1466,a1463,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1519,a1502,a1499,delim]@[(benchmarks:1485,[a1485,a1466,a1463,top])]
Evaluating: 1 in BEnv (fromList [resume,z]):[a1466,a1463,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1483,a1466,a1463,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a1483,a1466,a1463,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a1483,a1466,a1463,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a1483,a1466,a1463,top]@[]
Evaluating: 5 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 32 - mixed effects op in handler before resume");
(fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((@open(ex31)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))(1, (@open(ex33)((Tuple2(1, 2))))));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 32 - mixed effects op in handler before resume") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 32 - mixed effects op in handler before resume" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((@open(ex31)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))(1, (@open(ex33)((Tuple2(1, 2))))));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((@open(ex31)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))(1, (@open(ex33)((Tuple2(1, 2))))));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
      (@open((+))((resume(z)), 1));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: ex31/@handle in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: ex31/@handle in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex31/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
    (@open((+))((resume(z)), 1));
  })))) in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: @Hnd-ex31 in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: @Hnd-ex31 in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (@open((+))((resume(z)), 1));
})) in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: fn(z, resume){
  @open((+))((resume(z)), 1);
} in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a1586,top]@[]
Evaluating: @hhandle(ex31/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1589,a1586,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1589,a1586,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1589,a1586,top]@[]
Evaluating: ex31/@tag in BEnv (fromList [action,hnd,ret]):[a1589,a1586,top]@[]
Evaluating: @open(@new-htag)("ex31@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex31@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1589,a1586,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1589,a1586,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1589,a1586,top]@[]
OPS analysis/aac/benchmarks/ex31 fvs: BEnv (fromList []):[a1589,a1586,top]@[]
Evaluating: (fn(@action){
  ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((@open(ex31)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))(1, (@open(ex33)((Tuple2(1, 2))))));
})) in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: fn(@action){
  ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((@open(ex31)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: fn(){
  @open((+))(1, (@open(ex33)((Tuple2(1, 2)))));
} in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((@open(ex31)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: ex33/@handle in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: ex33/@handle in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex33/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((@open(ex31)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
  })))) in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @Hnd-ex33 in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @Hnd-ex33 in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((@open(ex31)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
})) in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: fn(a, resume){
  @open((+))((@open(ex31)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))));
} in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @action in BEnv (fromList [@action]):[a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @hhandle(ex33/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: ex33/@tag in BEnv (fromList [action,hnd,ret]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @open(@new-htag)("ex33@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex33@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
OPS analysis/aac/benchmarks/ex33 fvs: BEnv (fromList []):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @open((+))(1, (@open(ex33)((Tuple2(1, 2))))) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @open(ex33)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: ex33 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex33/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex33/@select), a) in BEnv (fromList [a]):[a1679,delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1679,delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1679,delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1679,delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1679,delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1679,delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1679,delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1679,delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1679,delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: forall<e,a> ex33/@select in BEnv (fromList [a]):[a1679,delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: ex33/@select in BEnv (fromList [a]):[a1679,delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex33(_, (@ctl-ex33)) : analysis/aac/benchmarks/ex33<e,a> )
       -> @ctl-ex33;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a1679,delim]@[(benchmarks:1238,[a1625,a1622,delim]),(benchmarks:1130,[a1589,a1586,top])]
Matched [a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @open((+))((@open(ex31)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))) in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: (+) in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @open(ex31)((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: ex31 in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex31/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a1651,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a1651,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a1651,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex31/@select), a) in BEnv (fromList [a]):[a1644,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1644,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1644,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1644,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1644,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1644,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1644,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1644,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1644,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: forall<e,a> ex31/@select in BEnv (fromList [a]):[a1644,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: ex31/@select in BEnv (fromList [a]):[a1644,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex31(_, (@ctl-ex31)) : analysis/aac/benchmarks/ex31<e,a> )
       -> @ctl-ex31;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a1644,a1625,a1622,delim]@[(benchmarks:1130,[a1589,a1586,top])]
Matched [a1589,a1586,top]@[]
Evaluating: @open((+))((resume(z)), 1) in BEnv (fromList [resume,z]):[a1589,a1586,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a1589,a1586,top]@[]
Evaluating: resume(z) in BEnv (fromList [resume,z]):[a1589,a1586,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a1589,a1586,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a1589,a1586,top]@[]
Applying continuation benchmarks:1608 rebinding BEnv (fromList [])
Evaluating: resume((@open(tuple2/snd)(a))) in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: resume in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: @open(tuple2/snd)(a) in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2(_, (@x)) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a1664,a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a1664,a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a1664,a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Applying continuation benchmarks:1645 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1676,delim]@[(benchmarks:1645,[a1645,a1625,a1622,delim]),(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1676,delim]@[(benchmarks:1645,[a1645,a1625,a1622,delim]),(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1676,delim]@[(benchmarks:1645,[a1645,a1625,a1622,delim]),(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1676,delim]@[(benchmarks:1645,[a1645,a1625,a1622,delim]),(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1642,a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1642,a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1642,a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1642,a1625,a1622,delim]@[(benchmarks:1608,[a1608,a1589,a1586,top])]
Evaluating: 1 in BEnv (fromList [resume,z]):[a1589,a1586,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1606,a1589,a1586,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a1606,a1589,a1586,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a1606,a1589,a1586,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a1606,a1589,a1586,top]@[]
Evaluating: 5 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 33 - mixed effects under both handlers - inner first");
(fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))(1, (@open(ex33)((Tuple2(1, 2)))))), (@open(ex31)(0))));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 33 - mixed effects under both handlers - inner first") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 33 - mixed effects under both handlers - inner first" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))(1, (@open(ex33)((Tuple2(1, 2)))))), (@open(ex31)(0))));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))(1, (@open(ex33)((Tuple2(1, 2)))))), (@open(ex31)(0))));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
      (@open((+))((resume(z)), 1));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: ex31/@handle in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: ex31/@handle in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex31/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
    (@open((+))((resume(z)), 1));
  })))) in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: @Hnd-ex31 in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: @Hnd-ex31 in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (@open((+))((resume(z)), 1));
})) in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: fn(z, resume){
  @open((+))((resume(z)), 1);
} in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a1709,top]@[]
Evaluating: @hhandle(ex31/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1712,a1709,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1712,a1709,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1712,a1709,top]@[]
Evaluating: ex31/@tag in BEnv (fromList [action,hnd,ret]):[a1712,a1709,top]@[]
Evaluating: @open(@new-htag)("ex31@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex31@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1712,a1709,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1712,a1709,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1712,a1709,top]@[]
OPS analysis/aac/benchmarks/ex31 fvs: BEnv (fromList []):[a1712,a1709,top]@[]
Evaluating: (fn(@action){
  ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open(tuple2/fst)(a))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open((+))(1, (@open(ex33)((Tuple2(1, 2)))))), (@open(ex31)(0))));
})) in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: fn(@action){
  ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open(tuple2/fst)(a))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: fn(){
  @open((+))((@open((+))(1, (@open(ex33)((Tuple2(1, 2)))))), (@open(ex31)(0)));
} in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
      (resume((@open(tuple2/fst)(a))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: ex33/@handle in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: ex33/@handle in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex33/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
    (resume((@open(tuple2/fst)(a))));
  })))) in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @Hnd-ex33 in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @Hnd-ex33 in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @open(clause-control1)((fn(a, resume){
  (resume((@open(tuple2/fst)(a))));
})) in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: fn(a, resume){
  resume((@open(tuple2/fst)(a)));
} in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @action in BEnv (fromList [@action]):[a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @hhandle(ex33/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: ex33/@tag in BEnv (fromList [action,hnd,ret]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @open(@new-htag)("ex33@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex33@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
OPS analysis/aac/benchmarks/ex33 fvs: BEnv (fromList []):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @open((+))((@open((+))(1, (@open(ex33)((Tuple2(1, 2)))))), (@open(ex31)(0))) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open((+))(1, (@open(ex33)((Tuple2(1, 2))))) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @open(ex33)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: ex33 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex33/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex33/@select), a) in BEnv (fromList [a]):[a1789,delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1789,delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1789,delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1789,delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1789,delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1789,delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1789,delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1789,delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1789,delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: forall<e,a> ex33/@select in BEnv (fromList [a]):[a1789,delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: ex33/@select in BEnv (fromList [a]):[a1789,delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex33(_, (@ctl-ex33)) : analysis/aac/benchmarks/ex33<e,a> )
       -> @ctl-ex33;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a1789,delim]@[(benchmarks:1238,[a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Matched [a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: resume in BEnv (fromList [a,resume]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a1767,a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a1767,a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a1767,a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Applying continuation benchmarks:1765 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1781,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1781,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1781,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1781,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @open(ex31)(0) in BEnv (fromList []):[delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: ex31 in BEnv (fromList []):[delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex31/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: 0 in BEnv (fromList []):[delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex31/@select), a) in BEnv (fromList [a]):[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: forall<e,a> ex31/@select in BEnv (fromList [a]):[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: ex31/@select in BEnv (fromList [a]):[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex31(_, (@ctl-ex31)) : analysis/aac/benchmarks/ex31<e,a> )
       -> @ctl-ex31;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Link create IL@(1151:ex31:[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]) [a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Link create IL@(1151:ex31:[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]) [a1765,a1748,a1745,delim]@[(benchmarks:1130,[a1712,a1709,top])]
Matched [a1712,a1709,top]@[]
Evaluating: @open((+))((resume(z)), 1) in BEnv (fromList [resume,z]):[a1712,a1709,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a1712,a1709,top]@[]
Evaluating: resume(z) in BEnv (fromList [resume,z]):[a1712,a1709,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a1712,a1709,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a1712,a1709,top]@[]
Applying continuation benchmarks:1731 rebinding BEnv (fromList [])
Link restore IL@(1151:ex31:[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]) [a1782,delim]@[(benchmarks:1731,[a1731,a1712,a1709,top])]
Link restore IL@(1151:ex31:[a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]) [a1782,delim]@[(benchmarks:1765,[a1765,a1748,a1745,delim]),(benchmarks:1130,[a1712,a1709,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1779,delim]@[(benchmarks:1151,[a1782,delim]),(benchmarks:1731,[a1731,a1712,a1709,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1779,delim]@[(benchmarks:1151,[a1782,delim]),(benchmarks:1731,[a1731,a1712,a1709,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1779,delim]@[(benchmarks:1151,[a1782,delim]),(benchmarks:1731,[a1731,a1712,a1709,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1779,delim]@[(benchmarks:1151,[a1782,delim]),(benchmarks:1731,[a1731,a1712,a1709,top])]
Evaluating: 1 in BEnv (fromList [resume,z]):[a1712,a1709,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1729,a1712,a1709,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a1729,a1712,a1709,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a1729,a1712,a1709,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a1729,a1712,a1709,top]@[]
Evaluating: 3 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 34 - mixed effects under both handlers - outer first");
(fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))((@open(ex31)(0)), 1)), (@open(ex33)((Tuple2(1, 2))))));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 34 - mixed effects under both handlers - outer first") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 34 - mixed effects under both handlers - outer first" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))((@open(ex31)(0)), 1)), (@open(ex33)((Tuple2(1, 2))))));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))((@open(ex31)(0)), 1)), (@open(ex33)((Tuple2(1, 2))))));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex31/@handle((@Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
      (@open((+))((resume(z)), 1));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: ex31/@handle in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: ex31/@handle in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex31/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex31(3, (@open(clause-control1)((fn(z, resume){
    (@open((+))((resume(z)), 1));
  })))) in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: @Hnd-ex31 in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: @Hnd-ex31 in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (@open((+))((resume(z)), 1));
})) in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: fn(z, resume){
  @open((+))((resume(z)), 1);
} in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a1826,top]@[]
Evaluating: @hhandle(ex31/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1829,a1826,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1829,a1826,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1829,a1826,top]@[]
Evaluating: ex31/@tag in BEnv (fromList [action,hnd,ret]):[a1829,a1826,top]@[]
Evaluating: @open(@new-htag)("ex31@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex31@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1829,a1826,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1829,a1826,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1829,a1826,top]@[]
OPS analysis/aac/benchmarks/ex31 fvs: BEnv (fromList []):[a1829,a1826,top]@[]
Evaluating: (fn(@action){
  ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open(tuple2/fst)(a))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open((+))((@open(ex31)(0)), 1)), (@open(ex33)((Tuple2(1, 2))))));
})) in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: fn(@action){
  ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open(tuple2/fst)(a))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: fn(){
  @open((+))((@open((+))((@open(ex31)(0)), 1)), (@open(ex33)((Tuple2(1, 2)))));
} in BEnv (fromList []):[delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: ex33/@handle((@Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
      (resume((@open(tuple2/fst)(a))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: ex33/@handle in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: ex33/@handle in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex33/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex33(3, (@open(clause-control1)((fn(a, resume){
    (resume((@open(tuple2/fst)(a))));
  })))) in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @Hnd-ex33 in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @Hnd-ex33 in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @open(clause-control1)((fn(a, resume){
  (resume((@open(tuple2/fst)(a))));
})) in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: fn(a, resume){
  resume((@open(tuple2/fst)(a)));
} in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @action in BEnv (fromList [@action]):[a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @hhandle(ex33/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a1865,a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1865,a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a1865,a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: ex33/@tag in BEnv (fromList [action,hnd,ret]):[a1865,a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @open(@new-htag)("ex33@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex33@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a1865,a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a1865,a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a1865,a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
OPS analysis/aac/benchmarks/ex33 fvs: BEnv (fromList []):[a1865,a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @open((+))((@open((+))((@open(ex31)(0)), 1)), (@open(ex33)((Tuple2(1, 2))))) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open((+))((@open(ex31)(0)), 1) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @open(ex31)(0) in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: ex31 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex31/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: 0 in BEnv (fromList []):[delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex31/@select), a) in BEnv (fromList [a]):[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: forall<e,a> ex31/@select in BEnv (fromList [a]):[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: ex31/@select in BEnv (fromList [a]):[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex31(_, (@ctl-ex31)) : analysis/aac/benchmarks/ex31<e,a> )
       -> @ctl-ex31;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Link create IL@(1151:ex31:[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]) [a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Link create IL@(1151:ex31:[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]) [a1865,a1862,delim]@[(benchmarks:1130,[a1829,a1826,top])]
Matched [a1829,a1826,top]@[]
Evaluating: @open((+))((resume(z)), 1) in BEnv (fromList [resume,z]):[a1829,a1826,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a1829,a1826,top]@[]
Evaluating: resume(z) in BEnv (fromList [resume,z]):[a1829,a1826,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a1829,a1826,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a1829,a1826,top]@[]
Applying continuation benchmarks:1848 rebinding BEnv (fromList [])
Link restore IL@(1151:ex31:[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]) [a1905,delim]@[(benchmarks:1848,[a1848,a1829,a1826,top])]
Link restore IL@(1151:ex31:[a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]) [a1905,delim]@[(benchmarks:1238,[a1865,a1862,delim]),(benchmarks:1130,[a1829,a1826,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1898,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1898,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1898,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1898,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: @open(ex33)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: ex33 in BEnv (fromList []):[delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex33/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex33/@select), a) in BEnv (fromList [a]):[a1899,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1899,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a1899,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a1899,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1899,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a1899,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a1899,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a1899,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: 0 in BEnv (fromList [a]):[a1899,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: forall<e,a> ex33/@select in BEnv (fromList [a]):[a1899,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: ex33/@select in BEnv (fromList [a]):[a1899,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex33(_, (@ctl-ex33)) : analysis/aac/benchmarks/ex33<e,a> )
       -> @ctl-ex33;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a1899,delim]@[(benchmarks:1151,[a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Matched [a1905,delim]@[(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a1905,delim]@[(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: resume in BEnv (fromList [a,resume]):[a1905,delim]@[(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a1905,delim]@[(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a1905,delim]@[(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a1905,delim]@[(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a1905,delim]@[(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a1884,a1905,delim]@[(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a1884,a1905,delim]@[(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a1884,a1905,delim]@[(benchmarks:1848,[a1848,a1829,a1826,top])]
Applying continuation benchmarks:1882 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1896,delim]@[(benchmarks:1882,[a1882,a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a1896,delim]@[(benchmarks:1882,[a1882,a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: x in BEnv (fromList [x,y]):[a1896,delim]@[(benchmarks:1882,[a1882,a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: y in BEnv (fromList [x,y]):[a1896,delim]@[(benchmarks:1882,[a1882,a1905,delim]),(benchmarks:1848,[a1848,a1829,a1826,top])]
Evaluating: 1 in BEnv (fromList [resume,z]):[a1829,a1826,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a1846,a1829,a1826,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a1846,a1829,a1826,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a1846,a1829,a1826,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a1846,a1829,a1826,top]@[]
Evaluating: 3 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 4 nested effects (tail resume outer)");
(fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex42/@handle((@Hnd-ex42(3, (@open(clause-control1)((fn(y, resume){
          (resume((@open(ex41)(y))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(ex42)(1));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 4 nested effects (tail resume outer)") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 4 nested effects (tail resume outer)" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex42/@handle((@Hnd-ex42(3, (@open(clause-control1)((fn(y, resume){
          (resume((@open(ex41)(y))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(ex42)(1));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex42/@handle((@Hnd-ex42(3, (@open(clause-control1)((fn(y, resume){
          (resume((@open(ex41)(y))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(ex42)(1));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
      (resume((@open((+))(z, 1))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: ex41/@handle in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: ex41/@handle in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex41/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
    (resume((@open((+))(z, 1))));
  })))) in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: @Hnd-ex41 in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: @Hnd-ex41 in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (resume((@open((+))(z, 1))));
})) in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: fn(z, resume){
  resume((@open((+))(z, 1)));
} in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a2105,top]@[]
Evaluating: @hhandle(ex41/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2108,a2105,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2108,a2105,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2108,a2105,top]@[]
Evaluating: ex41/@tag in BEnv (fromList [action,hnd,ret]):[a2108,a2105,top]@[]
Evaluating: @open(@new-htag)("ex41@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex41@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2108,a2105,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2108,a2105,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2108,a2105,top]@[]
OPS analysis/aac/benchmarks/ex41 fvs: BEnv (fromList []):[a2108,a2105,top]@[]
Evaluating: (fn(@action){
  ex42/@handle((@Hnd-ex42(3, (@open(clause-control1)((fn(y, resume){
        (resume((@open(ex41)(y))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open(ex42)(1));
})) in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: fn(@action){
  ex42/@handle((@Hnd-ex42(3, (@open(clause-control1)((fn(y, resume){
        (resume((@open(ex41)(y))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: fn(){
  @open(ex42)(1);
} in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: ex42/@handle((@Hnd-ex42(3, (@open(clause-control1)((fn(y, resume){
      (resume((@open(ex41)(y))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: ex42/@handle in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: ex42/@handle in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex42/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex42(3, (@open(clause-control1)((fn(y, resume){
    (resume((@open(ex41)(y))));
  })))) in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @Hnd-ex42 in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @Hnd-ex42 in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @open(clause-control1)((fn(y, resume){
  (resume((@open(ex41)(y))));
})) in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: fn(y, resume){
  resume((@open(ex41)(y)));
} in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @action in BEnv (fromList [@action]):[a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @hhandle(ex42/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: ex42/@tag in BEnv (fromList [action,hnd,ret]):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @open(@new-htag)("ex42@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex42@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
OPS analysis/aac/benchmarks/ex42 fvs: BEnv (fromList []):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @open(ex42)(1) in BEnv (fromList []):[delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: ex42 in BEnv (fromList []):[delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex42/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex42/@select), a) in BEnv (fromList [a]):[a2175,delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2175,delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2175,delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2175,delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2175,delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2175,delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2175,delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2175,delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: 0 in BEnv (fromList [a]):[a2175,delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: forall<e,a> ex42/@select in BEnv (fromList [a]):[a2175,delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: ex42/@select in BEnv (fromList [a]):[a2175,delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex42(_, (@ctl-ex42)) : analysis/aac/benchmarks/ex42<e,a> )
       -> @ctl-ex42;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2175,delim]@[(benchmarks:2006,[a2144,a2141,delim]),(benchmarks:1952,[a2108,a2105,top])]
Matched [a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: resume((@open(ex41)(y))) in BEnv (fromList [resume,y]):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: resume in BEnv (fromList [resume,y]):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @open(ex41)(y) in BEnv (fromList [resume,y]):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: ex41 in BEnv (fromList [resume,y]):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: y in BEnv (fromList [resume,y]):[a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a) in BEnv (fromList [a]):[a2163,a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2163,a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2163,a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2163,a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2163,a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2163,a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2163,a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2163,a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: 0 in BEnv (fromList [a]):[a2163,a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: forall<e,a> ex41/@select in BEnv (fromList [a]):[a2163,a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: ex41/@select in BEnv (fromList [a]):[a2163,a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex41(_, (@ctl-ex41)) : analysis/aac/benchmarks/ex41<e,a> )
       -> @ctl-ex41;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2163,a2144,a2141,delim]@[(benchmarks:1952,[a2108,a2105,top])]
Matched [a2108,a2105,top]@[]
Evaluating: resume((@open((+))(z, 1))) in BEnv (fromList [resume,z]):[a2108,a2105,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a2108,a2105,top]@[]
Evaluating: @open((+))(z, 1) in BEnv (fromList [resume,z]):[a2108,a2105,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a2108,a2105,top]@[]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a2108,a2105,top]@[]
Evaluating: 1 in BEnv (fromList [resume,z]):[a2108,a2105,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2127,a2108,a2105,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a2127,a2108,a2105,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a2127,a2108,a2105,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a2127,a2108,a2105,top]@[]
Applying continuation benchmarks:2125 rebinding BEnv (fromList [])
Applying continuation benchmarks:2161 rebinding BEnv (fromList [])
Evaluating: 2 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 41 - mixed effects op in handler after resume (tail resume outer)");
(fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex41)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))(1, (@open(ex43)((Tuple2(1, 2))))));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 41 - mixed effects op in handler after resume (tail resume outer)") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 41 - mixed effects op in handler after resume (tail resume outer)" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex41)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))(1, (@open(ex43)((Tuple2(1, 2))))));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex41)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))(1, (@open(ex43)((Tuple2(1, 2))))));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
      (resume((@open((+))(z, 1))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: ex41/@handle in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: ex41/@handle in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex41/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
    (resume((@open((+))(z, 1))));
  })))) in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: @Hnd-ex41 in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: @Hnd-ex41 in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (resume((@open((+))(z, 1))));
})) in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: fn(z, resume){
  resume((@open((+))(z, 1)));
} in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a2195,top]@[]
Evaluating: @hhandle(ex41/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2198,a2195,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2198,a2195,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2198,a2195,top]@[]
Evaluating: ex41/@tag in BEnv (fromList [action,hnd,ret]):[a2198,a2195,top]@[]
Evaluating: @open(@new-htag)("ex41@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex41@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2198,a2195,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2198,a2195,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2198,a2195,top]@[]
OPS analysis/aac/benchmarks/ex41 fvs: BEnv (fromList []):[a2198,a2195,top]@[]
Evaluating: (fn(@action){
  ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex41)((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))(1, (@open(ex43)((Tuple2(1, 2))))));
})) in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: fn(@action){
  ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex41)((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: fn(){
  @open((+))(1, (@open(ex43)((Tuple2(1, 2)))));
} in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex41)((@open(tuple2/snd)(a))))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: ex43/@handle in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: ex43/@handle in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex43/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex41)((@open(tuple2/snd)(a))))));
  })))) in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @Hnd-ex43 in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @Hnd-ex43 in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex41)((@open(tuple2/snd)(a))))));
})) in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: fn(a, resume){
  @open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex41)((@open(tuple2/snd)(a)))));
} in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @action in BEnv (fromList [@action]):[a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @hhandle(ex43/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: ex43/@tag in BEnv (fromList [action,hnd,ret]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @open(@new-htag)("ex43@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex43@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
OPS analysis/aac/benchmarks/ex43 fvs: BEnv (fromList []):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @open((+))(1, (@open(ex43)((Tuple2(1, 2))))) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @open(ex43)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: ex43 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex43/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex43/@select), a) in BEnv (fromList [a]):[a2288,delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2288,delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2288,delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2288,delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2288,delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2288,delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2288,delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2288,delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: 0 in BEnv (fromList [a]):[a2288,delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: forall<e,a> ex43/@select in BEnv (fromList [a]):[a2288,delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: ex43/@select in BEnv (fromList [a]):[a2288,delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex43(_, (@ctl-ex43)) : analysis/aac/benchmarks/ex43<e,a> )
       -> @ctl-ex43;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2288,delim]@[(benchmarks:2060,[a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Matched [a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex41)((@open(tuple2/snd)(a))))) in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: (+) in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: resume in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a2260,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a2260,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a2260,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Applying continuation benchmarks:2253 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2285,delim]@[(benchmarks:2253,[a2253,a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a2285,delim]@[(benchmarks:2253,[a2253,a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: x in BEnv (fromList [x,y]):[a2285,delim]@[(benchmarks:2253,[a2253,a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: y in BEnv (fromList [x,y]):[a2285,delim]@[(benchmarks:2253,[a2253,a2234,a2231,delim]),(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @open(ex41)((@open(tuple2/snd)(a))) in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: ex41 in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(tuple2/snd)(a) in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2(_, (@x)) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a2270,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a2270,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a2270,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a) in BEnv (fromList [a]):[a2254,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2254,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2254,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2254,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2254,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2254,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2254,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2254,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: 0 in BEnv (fromList [a]):[a2254,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: forall<e,a> ex41/@select in BEnv (fromList [a]):[a2254,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: ex41/@select in BEnv (fromList [a]):[a2254,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex41(_, (@ctl-ex41)) : analysis/aac/benchmarks/ex41<e,a> )
       -> @ctl-ex41;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2254,a2234,a2231,delim]@[(benchmarks:1952,[a2198,a2195,top])]
Matched [a2198,a2195,top]@[]
Evaluating: resume((@open((+))(z, 1))) in BEnv (fromList [resume,z]):[a2198,a2195,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a2198,a2195,top]@[]
Evaluating: @open((+))(z, 1) in BEnv (fromList [resume,z]):[a2198,a2195,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a2198,a2195,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a2198,a2195,top]@[]
Evaluating: 1 in BEnv (fromList [resume,z]):[a2198,a2195,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2217,a2198,a2195,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a2217,a2198,a2195,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a2217,a2198,a2195,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a2217,a2198,a2195,top]@[]
Applying continuation benchmarks:2215 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2251,a2234,a2231,delim]@[(benchmarks:2215,[a2215,a2198,a2195,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a2251,a2234,a2231,delim]@[(benchmarks:2215,[a2215,a2198,a2195,top])]
Evaluating: x in BEnv (fromList [x,y]):[a2251,a2234,a2231,delim]@[(benchmarks:2215,[a2215,a2198,a2195,top])]
Evaluating: y in BEnv (fromList [x,y]):[a2251,a2234,a2231,delim]@[(benchmarks:2215,[a2215,a2198,a2195,top])]
Evaluating: 5 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 42 - mixed effects op in handler before resume (tail resume outer)");
(fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((@open(ex41)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))(1, (@open(ex43)((Tuple2(1, 2))))));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 42 - mixed effects op in handler before resume (tail resume outer)") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 42 - mixed effects op in handler before resume (tail resume outer)" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((@open(ex41)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))(1, (@open(ex43)((Tuple2(1, 2))))));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((@open(ex41)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))(1, (@open(ex43)((Tuple2(1, 2))))));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
      (resume((@open((+))(z, 1))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: ex41/@handle in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: ex41/@handle in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex41/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
    (resume((@open((+))(z, 1))));
  })))) in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: @Hnd-ex41 in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: @Hnd-ex41 in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (resume((@open((+))(z, 1))));
})) in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: fn(z, resume){
  resume((@open((+))(z, 1)));
} in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a2318,top]@[]
Evaluating: @hhandle(ex41/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2321,a2318,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2321,a2318,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2321,a2318,top]@[]
Evaluating: ex41/@tag in BEnv (fromList [action,hnd,ret]):[a2321,a2318,top]@[]
Evaluating: @open(@new-htag)("ex41@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex41@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2321,a2318,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2321,a2318,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2321,a2318,top]@[]
OPS analysis/aac/benchmarks/ex41 fvs: BEnv (fromList []):[a2321,a2318,top]@[]
Evaluating: (fn(@action){
  ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((@open(ex41)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))(1, (@open(ex43)((Tuple2(1, 2))))));
})) in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: fn(@action){
  ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((@open(ex41)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: fn(){
  @open((+))(1, (@open(ex43)((Tuple2(1, 2)))));
} in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((@open(ex41)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: ex43/@handle in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: ex43/@handle in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex43/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((@open(ex41)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
  })))) in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @Hnd-ex43 in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @Hnd-ex43 in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((@open(ex41)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))));
})) in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: fn(a, resume){
  @open((+))((@open(ex41)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a)))));
} in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @action in BEnv (fromList [@action]):[a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @hhandle(ex43/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: ex43/@tag in BEnv (fromList [action,hnd,ret]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @open(@new-htag)("ex43@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex43@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
OPS analysis/aac/benchmarks/ex43 fvs: BEnv (fromList []):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @open((+))(1, (@open(ex43)((Tuple2(1, 2))))) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @open(ex43)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: ex43 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex43/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex43/@select), a) in BEnv (fromList [a]):[a2411,delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2411,delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2411,delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2411,delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2411,delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2411,delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2411,delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2411,delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: 0 in BEnv (fromList [a]):[a2411,delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: forall<e,a> ex43/@select in BEnv (fromList [a]):[a2411,delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: ex43/@select in BEnv (fromList [a]):[a2411,delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex43(_, (@ctl-ex43)) : analysis/aac/benchmarks/ex43<e,a> )
       -> @ctl-ex43;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2411,delim]@[(benchmarks:2060,[a2357,a2354,delim]),(benchmarks:1952,[a2321,a2318,top])]
Matched [a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @open((+))((@open(ex41)((@open(tuple2/fst)(a)))), (resume((@open(tuple2/snd)(a))))) in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: (+) in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @open(ex41)((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: ex41 in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a2383,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a2383,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a2383,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a) in BEnv (fromList [a]):[a2376,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2376,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2376,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2376,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2376,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2376,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2376,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2376,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: 0 in BEnv (fromList [a]):[a2376,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: forall<e,a> ex41/@select in BEnv (fromList [a]):[a2376,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: ex41/@select in BEnv (fromList [a]):[a2376,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex41(_, (@ctl-ex41)) : analysis/aac/benchmarks/ex41<e,a> )
       -> @ctl-ex41;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2376,a2357,a2354,delim]@[(benchmarks:1952,[a2321,a2318,top])]
Matched [a2321,a2318,top]@[]
Evaluating: resume((@open((+))(z, 1))) in BEnv (fromList [resume,z]):[a2321,a2318,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a2321,a2318,top]@[]
Evaluating: @open((+))(z, 1) in BEnv (fromList [resume,z]):[a2321,a2318,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a2321,a2318,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a2321,a2318,top]@[]
Evaluating: 1 in BEnv (fromList [resume,z]):[a2321,a2318,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2340,a2321,a2318,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a2340,a2321,a2318,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a2340,a2321,a2318,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a2340,a2321,a2318,top]@[]
Applying continuation benchmarks:2338 rebinding BEnv (fromList [])
Evaluating: resume((@open(tuple2/snd)(a))) in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: resume in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: @open(tuple2/snd)(a) in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2(_, (@x)) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a2396,a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a2396,a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a2396,a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Applying continuation benchmarks:2377 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2408,delim]@[(benchmarks:2377,[a2377,a2357,a2354,delim]),(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a2408,delim]@[(benchmarks:2377,[a2377,a2357,a2354,delim]),(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: x in BEnv (fromList [x,y]):[a2408,delim]@[(benchmarks:2377,[a2377,a2357,a2354,delim]),(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: y in BEnv (fromList [x,y]):[a2408,delim]@[(benchmarks:2377,[a2377,a2357,a2354,delim]),(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2374,a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a2374,a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: x in BEnv (fromList [x,y]):[a2374,a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: y in BEnv (fromList [x,y]):[a2374,a2357,a2354,delim]@[(benchmarks:2338,[a2338,a2321,a2318,top])]
Evaluating: 5 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 43 - mixed effects under both handlers - inner first (tail resume outer)");
(fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))(1, (@open(ex43)((Tuple2(1, 2)))))), (@open(ex41)(0))));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 43 - mixed effects under both handlers - inner first (tail resume outer)") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 43 - mixed effects under both handlers - inner first (tail resume outer)" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))(1, (@open(ex43)((Tuple2(1, 2)))))), (@open(ex41)(0))));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))(1, (@open(ex43)((Tuple2(1, 2)))))), (@open(ex41)(0))));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
      (resume((@open((+))(z, 1))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: ex41/@handle in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: ex41/@handle in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex41/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
    (resume((@open((+))(z, 1))));
  })))) in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: @Hnd-ex41 in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: @Hnd-ex41 in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (resume((@open((+))(z, 1))));
})) in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: fn(z, resume){
  resume((@open((+))(z, 1)));
} in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a2441,top]@[]
Evaluating: @hhandle(ex41/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2444,a2441,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2444,a2441,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2444,a2441,top]@[]
Evaluating: ex41/@tag in BEnv (fromList [action,hnd,ret]):[a2444,a2441,top]@[]
Evaluating: @open(@new-htag)("ex41@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex41@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2444,a2441,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2444,a2441,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2444,a2441,top]@[]
OPS analysis/aac/benchmarks/ex41 fvs: BEnv (fromList []):[a2444,a2441,top]@[]
Evaluating: (fn(@action){
  ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open(tuple2/fst)(a))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open((+))(1, (@open(ex43)((Tuple2(1, 2)))))), (@open(ex41)(0))));
})) in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: fn(@action){
  ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open(tuple2/fst)(a))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: fn(){
  @open((+))((@open((+))(1, (@open(ex43)((Tuple2(1, 2)))))), (@open(ex41)(0)));
} in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
      (resume((@open(tuple2/fst)(a))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: ex43/@handle in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: ex43/@handle in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex43/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
    (resume((@open(tuple2/fst)(a))));
  })))) in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @Hnd-ex43 in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @Hnd-ex43 in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @open(clause-control1)((fn(a, resume){
  (resume((@open(tuple2/fst)(a))));
})) in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: fn(a, resume){
  resume((@open(tuple2/fst)(a)));
} in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @action in BEnv (fromList [@action]):[a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @hhandle(ex43/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: ex43/@tag in BEnv (fromList [action,hnd,ret]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @open(@new-htag)("ex43@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex43@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
OPS analysis/aac/benchmarks/ex43 fvs: BEnv (fromList []):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @open((+))((@open((+))(1, (@open(ex43)((Tuple2(1, 2)))))), (@open(ex41)(0))) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open((+))(1, (@open(ex43)((Tuple2(1, 2))))) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @open(ex43)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: ex43 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex43/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex43/@select), a) in BEnv (fromList [a]):[a2521,delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2521,delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2521,delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2521,delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2521,delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2521,delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2521,delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2521,delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: 0 in BEnv (fromList [a]):[a2521,delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: forall<e,a> ex43/@select in BEnv (fromList [a]):[a2521,delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: ex43/@select in BEnv (fromList [a]):[a2521,delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex43(_, (@ctl-ex43)) : analysis/aac/benchmarks/ex43<e,a> )
       -> @ctl-ex43;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2521,delim]@[(benchmarks:2060,[a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Matched [a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: resume in BEnv (fromList [a,resume]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a2499,a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a2499,a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a2499,a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Applying continuation benchmarks:2497 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2513,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a2513,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: x in BEnv (fromList [x,y]):[a2513,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: y in BEnv (fromList [x,y]):[a2513,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @open(ex41)(0) in BEnv (fromList []):[delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: ex41 in BEnv (fromList []):[delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: 0 in BEnv (fromList []):[delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a) in BEnv (fromList [a]):[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: 0 in BEnv (fromList [a]):[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: forall<e,a> ex41/@select in BEnv (fromList [a]):[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: ex41/@select in BEnv (fromList [a]):[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex41(_, (@ctl-ex41)) : analysis/aac/benchmarks/ex41<e,a> )
       -> @ctl-ex41;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Link create IL@(1973:ex41:[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]) [a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Link create IL@(1973:ex41:[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]) [a2497,a2480,a2477,delim]@[(benchmarks:1952,[a2444,a2441,top])]
Matched [a2444,a2441,top]@[]
Evaluating: resume((@open((+))(z, 1))) in BEnv (fromList [resume,z]):[a2444,a2441,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a2444,a2441,top]@[]
Evaluating: @open((+))(z, 1) in BEnv (fromList [resume,z]):[a2444,a2441,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a2444,a2441,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a2444,a2441,top]@[]
Evaluating: 1 in BEnv (fromList [resume,z]):[a2444,a2441,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2463,a2444,a2441,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a2463,a2444,a2441,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a2463,a2444,a2441,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a2463,a2444,a2441,top]@[]
Applying continuation benchmarks:2461 rebinding BEnv (fromList [])
Link restore IL@(1973:ex41:[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]) [a2514,delim]@[(benchmarks:2461,[a2461,a2444,a2441,top])]
Link restore IL@(1973:ex41:[a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]) [a2514,delim]@[(benchmarks:2497,[a2497,a2480,a2477,delim]),(benchmarks:1952,[a2444,a2441,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2511,delim]@[(benchmarks:1973,[a2514,delim]),(benchmarks:2461,[a2461,a2444,a2441,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a2511,delim]@[(benchmarks:1973,[a2514,delim]),(benchmarks:2461,[a2461,a2444,a2441,top])]
Evaluating: x in BEnv (fromList [x,y]):[a2511,delim]@[(benchmarks:1973,[a2514,delim]),(benchmarks:2461,[a2461,a2444,a2441,top])]
Evaluating: y in BEnv (fromList [x,y]):[a2511,delim]@[(benchmarks:1973,[a2514,delim]),(benchmarks:2461,[a2461,a2444,a2441,top])]
Evaluating: 3 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 44 - mixed effects under both handlers - outer first (tail resume outer)");
(fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2))))));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 44 - mixed effects under both handlers - outer first (tail resume outer)") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 44 - mixed effects under both handlers - outer first (tail resume outer)" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2))))));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2))))));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
      (resume((@open((+))(z, 1))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: ex41/@handle in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: ex41/@handle in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex41/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
    (resume((@open((+))(z, 1))));
  })))) in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: @Hnd-ex41 in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: @Hnd-ex41 in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (resume((@open((+))(z, 1))));
})) in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: fn(z, resume){
  resume((@open((+))(z, 1)));
} in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a2558,top]@[]
Evaluating: @hhandle(ex41/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2561,a2558,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2561,a2558,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2561,a2558,top]@[]
Evaluating: ex41/@tag in BEnv (fromList [action,hnd,ret]):[a2561,a2558,top]@[]
Evaluating: @open(@new-htag)("ex41@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex41@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2561,a2558,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2561,a2558,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2561,a2558,top]@[]
OPS analysis/aac/benchmarks/ex41 fvs: BEnv (fromList []):[a2561,a2558,top]@[]
Evaluating: (fn(@action){
  ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open(tuple2/fst)(a))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2))))));
})) in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: fn(@action){
  ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open(tuple2/fst)(a))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: fn(){
  @open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2)))));
} in BEnv (fromList []):[delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
      (resume((@open(tuple2/fst)(a))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: ex43/@handle in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: ex43/@handle in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex43/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
    (resume((@open(tuple2/fst)(a))));
  })))) in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @Hnd-ex43 in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @Hnd-ex43 in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @open(clause-control1)((fn(a, resume){
  (resume((@open(tuple2/fst)(a))));
})) in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: fn(a, resume){
  resume((@open(tuple2/fst)(a)));
} in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @action in BEnv (fromList [@action]):[a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @hhandle(ex43/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2597,a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2597,a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2597,a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: ex43/@tag in BEnv (fromList [action,hnd,ret]):[a2597,a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @open(@new-htag)("ex43@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex43@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2597,a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2597,a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2597,a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
OPS analysis/aac/benchmarks/ex43 fvs: BEnv (fromList []):[a2597,a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2))))) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open((+))((@open(ex41)(0)), 1) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @open(ex41)(0) in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: ex41 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: 0 in BEnv (fromList []):[delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a) in BEnv (fromList [a]):[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: 0 in BEnv (fromList [a]):[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: forall<e,a> ex41/@select in BEnv (fromList [a]):[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: ex41/@select in BEnv (fromList [a]):[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex41(_, (@ctl-ex41)) : analysis/aac/benchmarks/ex41<e,a> )
       -> @ctl-ex41;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Link create IL@(1973:ex41:[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]) [a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Link create IL@(1973:ex41:[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]) [a2597,a2594,delim]@[(benchmarks:1952,[a2561,a2558,top])]
Matched [a2561,a2558,top]@[]
Evaluating: resume((@open((+))(z, 1))) in BEnv (fromList [resume,z]):[a2561,a2558,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a2561,a2558,top]@[]
Evaluating: @open((+))(z, 1) in BEnv (fromList [resume,z]):[a2561,a2558,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a2561,a2558,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a2561,a2558,top]@[]
Evaluating: 1 in BEnv (fromList [resume,z]):[a2561,a2558,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2580,a2561,a2558,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a2580,a2561,a2558,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a2580,a2561,a2558,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a2580,a2561,a2558,top]@[]
Applying continuation benchmarks:2578 rebinding BEnv (fromList [])
Link restore IL@(1973:ex41:[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]) [a2637,delim]@[(benchmarks:2578,[a2578,a2561,a2558,top])]
Link restore IL@(1973:ex41:[a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]) [a2637,delim]@[(benchmarks:2060,[a2597,a2594,delim]),(benchmarks:1952,[a2561,a2558,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2630,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a2630,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: x in BEnv (fromList [x,y]):[a2630,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: y in BEnv (fromList [x,y]):[a2630,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: @open(ex43)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: ex43 in BEnv (fromList []):[delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex43/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex43/@select), a) in BEnv (fromList [a]):[a2631,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2631,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2631,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2631,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2631,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2631,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2631,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2631,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: 0 in BEnv (fromList [a]):[a2631,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: forall<e,a> ex43/@select in BEnv (fromList [a]):[a2631,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: ex43/@select in BEnv (fromList [a]):[a2631,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex43(_, (@ctl-ex43)) : analysis/aac/benchmarks/ex43<e,a> )
       -> @ctl-ex43;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2631,delim]@[(benchmarks:1973,[a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Matched [a2637,delim]@[(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a2637,delim]@[(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: resume in BEnv (fromList [a,resume]):[a2637,delim]@[(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a2637,delim]@[(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a2637,delim]@[(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a2637,delim]@[(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a2637,delim]@[(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a2616,a2637,delim]@[(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a2616,a2637,delim]@[(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a2616,a2637,delim]@[(benchmarks:2578,[a2578,a2561,a2558,top])]
Applying continuation benchmarks:2614 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2628,delim]@[(benchmarks:2614,[a2614,a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a2628,delim]@[(benchmarks:2614,[a2614,a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: x in BEnv (fromList [x,y]):[a2628,delim]@[(benchmarks:2614,[a2614,a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: y in BEnv (fromList [x,y]):[a2628,delim]@[(benchmarks:2614,[a2614,a2637,delim]),(benchmarks:2578,[a2578,a2561,a2558,top])]
Evaluating: 3 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 50 - whole lot of effects");
(fn(@action){
  ex51/@handle((@Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
            (@open((+))((resume(b)), b));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@open((+))((@open((+))(1, (@open(ex52)((Tuple2(1, 2)))))), (@open(ex53)(1))));
    })));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 50 - whole lot of effects") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 50 - whole lot of effects" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex51/@handle((@Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
            (@open((+))((resume(b)), b));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@open((+))((@open((+))(1, (@open(ex52)((Tuple2(1, 2)))))), (@open(ex53)(1))));
    })));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex51/@handle((@Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
            (@open((+))((resume(b)), b));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@open((+))((@open((+))(1, (@open(ex52)((Tuple2(1, 2)))))), (@open(ex53)(1))));
    })));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex51/@handle((@Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
      (@open((+))((resume(z)), 1));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: ex51/@handle in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: ex51/@handle in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex51/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
    (@open((+))((resume(z)), 1));
  })))) in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: @Hnd-ex51 in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: @Hnd-ex51 in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (@open((+))((resume(z)), 1));
})) in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: fn(z, resume){
  @open((+))((resume(z)), 1);
} in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a2837,top]@[]
Evaluating: @hhandle(ex51/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2840,a2837,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2840,a2837,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2840,a2837,top]@[]
Evaluating: ex51/@tag in BEnv (fromList [action,hnd,ret]):[a2840,a2837,top]@[]
Evaluating: @open(@new-htag)("ex51@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex51@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2840,a2837,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2840,a2837,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2840,a2837,top]@[]
OPS analysis/aac/benchmarks/ex51 fvs: BEnv (fromList []):[a2840,a2837,top]@[]
Evaluating: (fn(@action){
  ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
          (@open((+))((resume(b)), b));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))(1, (@open(ex52)((Tuple2(1, 2)))))), (@open(ex53)(1))));
  })));
})) in BEnv (fromList []):[delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: fn(@action){
  ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: fn(){
  (fn(@action){
    ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
          (@open((+))((resume(b)), b));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))(1, (@open(ex52)((Tuple2(1, 2)))))), (@open(ex53)(1))));
  }));
} in BEnv (fromList []):[delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: ex52/@handle in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: ex52/@handle in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex52/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
  })))) in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @Hnd-ex52 in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @Hnd-ex52 in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
})) in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: fn(a, resume){
  @open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a)))));
} in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @action in BEnv (fromList [@action]):[a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @hhandle(ex52/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: ex52/@tag in BEnv (fromList [action,hnd,ret]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @open(@new-htag)("ex52@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex52@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
OPS analysis/aac/benchmarks/ex52 fvs: BEnv (fromList []):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: (fn(@action){
  ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
        (@open((+))((resume(b)), b));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open((+))(1, (@open(ex52)((Tuple2(1, 2)))))), (@open(ex53)(1))));
})) in BEnv (fromList []):[delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: fn(@action){
  ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
        (@open((+))((resume(b)), b));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: fn(){
  @open((+))((@open((+))(1, (@open(ex52)((Tuple2(1, 2)))))), (@open(ex53)(1)));
} in BEnv (fromList []):[delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
      (@open((+))((resume(b)), b));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: ex53/@handle in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: ex53/@handle in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex53/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
    (@open((+))((resume(b)), b));
  })))) in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @Hnd-ex53 in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @Hnd-ex53 in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @open(clause-control1)((fn(b, resume){
  (@open((+))((resume(b)), b));
})) in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: fn(b, resume){
  @open((+))((resume(b)), b);
} in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @action in BEnv (fromList [@action]):[a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @hhandle(ex53/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a2930,a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2930,a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a2930,a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: ex53/@tag in BEnv (fromList [action,hnd,ret]):[a2930,a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @open(@new-htag)("ex53@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex53@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a2930,a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a2930,a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a2930,a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
OPS analysis/aac/benchmarks/ex53 fvs: BEnv (fromList []):[a2930,a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @open((+))((@open((+))(1, (@open(ex52)((Tuple2(1, 2)))))), (@open(ex53)(1))) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open((+))(1, (@open(ex52)((Tuple2(1, 2))))) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: @open(ex52)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: ex52 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex52/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex52/@select), a) in BEnv (fromList [a]):[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: 0 in BEnv (fromList [a]):[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: forall<e,a> ex52/@select in BEnv (fromList [a]):[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: ex52/@select in BEnv (fromList [a]):[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex52(_, (@ctl-ex52)) : analysis/aac/benchmarks/ex52<e,a> )
       -> @ctl-ex52;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Link create IL@(2759:ex52:[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]) [a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Link create IL@(2759:ex52:[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]) [a2930,a2927,delim]@[(benchmarks:2738,[a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Matched [a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))) in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: (+) in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: resume in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a2902,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a2902,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a2902,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Applying continuation benchmarks:2895 rebinding BEnv (fromList [])
Link restore IL@(2759:ex52:[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]) [a2973,delim]@[(benchmarks:2895,[a2895,a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Link restore IL@(2759:ex52:[a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]) [a2973,delim]@[(benchmarks:2792,[a2930,a2927,delim]),(benchmarks:2738,[a2876,a2873,delim])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2965,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: int-add in BEnv (fromList [x,y]):[a2965,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: x in BEnv (fromList [x,y]):[a2965,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: y in BEnv (fromList [x,y]):[a2965,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: @open(ex53)(1) in BEnv (fromList []):[delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: ex53 in BEnv (fromList []):[delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex53/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex53/@select), a) in BEnv (fromList [a]):[a2966,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2966,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2966,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2966,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2966,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2966,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2966,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2966,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: 0 in BEnv (fromList [a]):[a2966,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: forall<e,a> ex53/@select in BEnv (fromList [a]):[a2966,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: ex53/@select in BEnv (fromList [a]):[a2966,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex53(_, (@ctl-ex53)) : analysis/aac/benchmarks/ex53<e,a> )
       -> @ctl-ex53;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2966,delim]@[(benchmarks:2759,[a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Matched [a2973,delim]@[(benchmarks:2895,[a2895,a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @open((+))((resume(b)), b) in BEnv (fromList [b,resume]):[a2973,delim]@[(benchmarks:2895,[a2895,a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: (+) in BEnv (fromList [b,resume]):[a2973,delim]@[(benchmarks:2895,[a2895,a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[a2973,delim]@[(benchmarks:2895,[a2895,a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: resume in BEnv (fromList [b,resume]):[a2973,delim]@[(benchmarks:2895,[a2895,a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: b in BEnv (fromList [b,resume]):[a2973,delim]@[(benchmarks:2895,[a2895,a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Applying continuation benchmarks:2949 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2963,delim]@[(benchmarks:2949,[a2949,a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: int-add in BEnv (fromList [x,y]):[a2963,delim]@[(benchmarks:2949,[a2949,a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: x in BEnv (fromList [x,y]):[a2963,delim]@[(benchmarks:2949,[a2949,a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: y in BEnv (fromList [x,y]):[a2963,delim]@[(benchmarks:2949,[a2949,a2973,delim]),(benchmarks:2895,[a2895,a2876,a2873,delim])]
Evaluating: b in BEnv (fromList [b,resume]):[a2973,delim]@[(benchmarks:2895,[a2895,a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2947,a2973,delim]@[(benchmarks:2895,[a2895,a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a2947,a2973,delim]@[(benchmarks:2895,[a2895,a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: x in BEnv (fromList [x,y]):[a2947,a2973,delim]@[(benchmarks:2895,[a2895,a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: y in BEnv (fromList [x,y]):[a2947,a2973,delim]@[(benchmarks:2895,[a2895,a2876,a2873,delim]),(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @open(ex51)((@open(tuple2/snd)(a))) in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: ex51 in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex51/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(tuple2/snd)(a) in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2(_, (@x)) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a2912,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a2912,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a2912,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex51/@select), a) in BEnv (fromList [a]):[a2896,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2896,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a2896,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a2896,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2896,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a2896,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a2896,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a2896,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: 0 in BEnv (fromList [a]):[a2896,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: forall<e,a> ex51/@select in BEnv (fromList [a]):[a2896,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: ex51/@select in BEnv (fromList [a]):[a2896,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex51(_, (@ctl-ex51)) : analysis/aac/benchmarks/ex51<e,a> )
       -> @ctl-ex51;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a2896,a2876,a2873,delim]@[(benchmarks:2684,[a2840,a2837,top])]
Matched [a2840,a2837,top]@[]
Evaluating: @open((+))((resume(z)), 1) in BEnv (fromList [resume,z]):[a2840,a2837,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a2840,a2837,top]@[]
Evaluating: resume(z) in BEnv (fromList [resume,z]):[a2840,a2837,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a2840,a2837,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a2840,a2837,top]@[]
Applying continuation benchmarks:2859 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2893,a2876,a2873,delim]@[(benchmarks:2859,[a2859,a2840,a2837,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a2893,a2876,a2873,delim]@[(benchmarks:2859,[a2859,a2840,a2837,top])]
Evaluating: x in BEnv (fromList [x,y]):[a2893,a2876,a2873,delim]@[(benchmarks:2859,[a2859,a2840,a2837,top])]
Evaluating: y in BEnv (fromList [x,y]):[a2893,a2876,a2873,delim]@[(benchmarks:2859,[a2859,a2840,a2837,top])]
Evaluating: 1 in BEnv (fromList [resume,z]):[a2840,a2837,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a2857,a2840,a2837,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a2857,a2840,a2837,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a2857,a2840,a2837,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a2857,a2840,a2837,top]@[]
Evaluating: 7 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 51 - whole lot of effects inner first");
(fn(@action){
  ex51/@handle((@Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
            (@open((+))((resume(b)), b));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@open((+))((@open((+))((@open(ex53)(1)), (@open(ex52)((Tuple2(1, 2)))))), 1));
    })));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 51 - whole lot of effects inner first") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 51 - whole lot of effects inner first" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex51/@handle((@Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
            (@open((+))((resume(b)), b));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@open((+))((@open((+))((@open(ex53)(1)), (@open(ex52)((Tuple2(1, 2)))))), 1));
    })));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex51/@handle((@Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
        (@open((+))((resume(z)), 1));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
            (@open((+))((resume(b)), b));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@open((+))((@open((+))((@open(ex53)(1)), (@open(ex52)((Tuple2(1, 2)))))), 1));
    })));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex51/@handle((@Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
      (@open((+))((resume(z)), 1));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: ex51/@handle in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: ex51/@handle in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex51/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
    (@open((+))((resume(z)), 1));
  })))) in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: @Hnd-ex51 in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: @Hnd-ex51 in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (@open((+))((resume(z)), 1));
})) in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: fn(z, resume){
  @open((+))((resume(z)), 1);
} in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a3010,top]@[]
Evaluating: @hhandle(ex51/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a3013,a3010,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a3013,a3010,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a3013,a3010,top]@[]
Evaluating: ex51/@tag in BEnv (fromList [action,hnd,ret]):[a3013,a3010,top]@[]
Evaluating: @open(@new-htag)("ex51@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex51@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a3013,a3010,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a3013,a3010,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a3013,a3010,top]@[]
OPS analysis/aac/benchmarks/ex51 fvs: BEnv (fromList []):[a3013,a3010,top]@[]
Evaluating: (fn(@action){
  ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
          (@open((+))((resume(b)), b));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))((@open(ex53)(1)), (@open(ex52)((Tuple2(1, 2)))))), 1));
  })));
})) in BEnv (fromList []):[delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: fn(@action){
  ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: fn(){
  (fn(@action){
    ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
          (@open((+))((resume(b)), b));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))((@open(ex53)(1)), (@open(ex52)((Tuple2(1, 2)))))), 1));
  }));
} in BEnv (fromList []):[delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: ex52/@handle in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: ex52/@handle in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex52/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
  })))) in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @Hnd-ex52 in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @Hnd-ex52 in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
})) in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: fn(a, resume){
  @open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a)))));
} in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @action in BEnv (fromList [@action]):[a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @hhandle(ex52/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: ex52/@tag in BEnv (fromList [action,hnd,ret]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @open(@new-htag)("ex52@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex52@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
OPS analysis/aac/benchmarks/ex52 fvs: BEnv (fromList []):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: (fn(@action){
  ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
        (@open((+))((resume(b)), b));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open((+))((@open(ex53)(1)), (@open(ex52)((Tuple2(1, 2)))))), 1));
})) in BEnv (fromList []):[delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: fn(@action){
  ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
        (@open((+))((resume(b)), b));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: fn(){
  @open((+))((@open((+))((@open(ex53)(1)), (@open(ex52)((Tuple2(1, 2)))))), 1);
} in BEnv (fromList []):[delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
      (@open((+))((resume(b)), b));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: ex53/@handle in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: ex53/@handle in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex53/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
    (@open((+))((resume(b)), b));
  })))) in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @Hnd-ex53 in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @Hnd-ex53 in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @open(clause-control1)((fn(b, resume){
  (@open((+))((resume(b)), b));
})) in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: fn(b, resume){
  @open((+))((resume(b)), b);
} in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @action in BEnv (fromList [@action]):[a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @hhandle(ex53/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: ex53/@tag in BEnv (fromList [action,hnd,ret]):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @open(@new-htag)("ex53@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex53@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
OPS analysis/aac/benchmarks/ex53 fvs: BEnv (fromList []):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @open((+))((@open((+))((@open(ex53)(1)), (@open(ex52)((Tuple2(1, 2)))))), 1) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open((+))((@open(ex53)(1)), (@open(ex52)((Tuple2(1, 2))))) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @open(ex53)(1) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: ex53 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex53/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex53/@select), a) in BEnv (fromList [a]):[a3145,delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3145,delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3145,delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a3145,delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3145,delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3145,delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a3145,delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a3145,delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: 0 in BEnv (fromList [a]):[a3145,delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: forall<e,a> ex53/@select in BEnv (fromList [a]):[a3145,delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: ex53/@select in BEnv (fromList [a]):[a3145,delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex53(_, (@ctl-ex53)) : analysis/aac/benchmarks/ex53<e,a> )
       -> @ctl-ex53;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a3145,delim]@[(benchmarks:2792,[a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Matched [a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @open((+))((resume(b)), b) in BEnv (fromList [b,resume]):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: (+) in BEnv (fromList [b,resume]):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: resume in BEnv (fromList [b,resume]):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: b in BEnv (fromList [b,resume]):[a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Applying continuation benchmarks:3122 rebinding BEnv (fromList [])
Evaluating: @open(ex52)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: ex52 in BEnv (fromList []):[delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex52/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex52/@select), a) in BEnv (fromList [a]):[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: 0 in BEnv (fromList [a]):[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: forall<e,a> ex52/@select in BEnv (fromList [a]):[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: ex52/@select in BEnv (fromList [a]):[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex52(_, (@ctl-ex52)) : analysis/aac/benchmarks/ex52<e,a> )
       -> @ctl-ex52;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Link create IL@(2759:ex52:[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]) [a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Link create IL@(2759:ex52:[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]) [a3122,a3103,a3100,delim]@[(benchmarks:2738,[a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Matched [a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))) in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: (+) in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: resume in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a3075,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a3075,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a3075,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Applying continuation benchmarks:3068 rebinding BEnv (fromList [])
Link restore IL@(2759:ex52:[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]) [a3146,delim]@[(benchmarks:3068,[a3068,a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Link restore IL@(2759:ex52:[a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]) [a3146,delim]@[(benchmarks:3122,[a3122,a3103,a3100,delim]),(benchmarks:2738,[a3049,a3046,delim])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a3138,delim]@[(benchmarks:2759,[a3146,delim]),(benchmarks:3068,[a3068,a3049,a3046,delim])]
Evaluating: int-add in BEnv (fromList [x,y]):[a3138,delim]@[(benchmarks:2759,[a3146,delim]),(benchmarks:3068,[a3068,a3049,a3046,delim])]
Evaluating: x in BEnv (fromList [x,y]):[a3138,delim]@[(benchmarks:2759,[a3146,delim]),(benchmarks:3068,[a3068,a3049,a3046,delim])]
Evaluating: y in BEnv (fromList [x,y]):[a3138,delim]@[(benchmarks:2759,[a3146,delim]),(benchmarks:3068,[a3068,a3049,a3046,delim])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2759,[a3146,delim]),(benchmarks:3068,[a3068,a3049,a3046,delim])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a3136,delim]@[(benchmarks:2759,[a3146,delim]),(benchmarks:3068,[a3068,a3049,a3046,delim])]
Evaluating: int-add in BEnv (fromList [x,y]):[a3136,delim]@[(benchmarks:2759,[a3146,delim]),(benchmarks:3068,[a3068,a3049,a3046,delim])]
Evaluating: x in BEnv (fromList [x,y]):[a3136,delim]@[(benchmarks:2759,[a3146,delim]),(benchmarks:3068,[a3068,a3049,a3046,delim])]
Evaluating: y in BEnv (fromList [x,y]):[a3136,delim]@[(benchmarks:2759,[a3146,delim]),(benchmarks:3068,[a3068,a3049,a3046,delim])]
Evaluating: b in BEnv (fromList [b,resume]):[a3103,a3100,delim]@[(benchmarks:3068,[a3068,a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a3120,a3103,a3100,delim]@[(benchmarks:3068,[a3068,a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a3120,a3103,a3100,delim]@[(benchmarks:3068,[a3068,a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: x in BEnv (fromList [x,y]):[a3120,a3103,a3100,delim]@[(benchmarks:3068,[a3068,a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: y in BEnv (fromList [x,y]):[a3120,a3103,a3100,delim]@[(benchmarks:3068,[a3068,a3049,a3046,delim]),(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @open(ex51)((@open(tuple2/snd)(a))) in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: ex51 in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex51/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(tuple2/snd)(a) in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2(_, (@x)) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a3085,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a3085,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a3085,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex51/@select), a) in BEnv (fromList [a]):[a3069,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3069,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3069,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a3069,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3069,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3069,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a3069,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a3069,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: 0 in BEnv (fromList [a]):[a3069,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: forall<e,a> ex51/@select in BEnv (fromList [a]):[a3069,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: ex51/@select in BEnv (fromList [a]):[a3069,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex51(_, (@ctl-ex51)) : analysis/aac/benchmarks/ex51<e,a> )
       -> @ctl-ex51;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a3069,a3049,a3046,delim]@[(benchmarks:2684,[a3013,a3010,top])]
Matched [a3013,a3010,top]@[]
Evaluating: @open((+))((resume(z)), 1) in BEnv (fromList [resume,z]):[a3013,a3010,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a3013,a3010,top]@[]
Evaluating: resume(z) in BEnv (fromList [resume,z]):[a3013,a3010,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a3013,a3010,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a3013,a3010,top]@[]
Applying continuation benchmarks:3032 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a3066,a3049,a3046,delim]@[(benchmarks:3032,[a3032,a3013,a3010,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a3066,a3049,a3046,delim]@[(benchmarks:3032,[a3032,a3013,a3010,top])]
Evaluating: x in BEnv (fromList [x,y]):[a3066,a3049,a3046,delim]@[(benchmarks:3032,[a3032,a3013,a3010,top])]
Evaluating: y in BEnv (fromList [x,y]):[a3066,a3049,a3046,delim]@[(benchmarks:3032,[a3032,a3013,a3010,top])]
Evaluating: 1 in BEnv (fromList [resume,z]):[a3013,a3010,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a3030,a3013,a3010,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a3030,a3013,a3010,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a3030,a3013,a3010,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a3030,a3013,a3010,top]@[]
Evaluating: 7 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example 52 - whole lot of effects two outer calls");
(fn(@action){
  ex51/@handle((@Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
            (@open((+))((resume(b)), (@open(ex51)(b))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@open((+))((@open(ex52)((Tuple2(1, 2)))), (@open(ex53)(1))));
    })));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example 52 - whole lot of effects two outer calls") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example 52 - whole lot of effects two outer calls" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  ex51/@handle((@Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
            (@open((+))((resume(b)), (@open(ex51)(b))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@open((+))((@open(ex52)((Tuple2(1, 2)))), (@open(ex53)(1))));
    })));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: fn(@action){
  ex51/@handle((@Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
        (resume((@open((+))(z, 1))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
          (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
            (@open((+))((resume(b)), (@open(ex51)(b))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@open((+))((@open(ex52)((Tuple2(1, 2)))), (@open(ex53)(1))));
    })));
  }));
} in BEnv (fromList [_]):[top]@[]
Evaluating: ex51/@handle((@Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
      (resume((@open((+))(z, 1))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: ex51/@handle in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: ex51/@handle in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex51/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex51(3, (@open(clause-control1)((fn(z, resume){
    (resume((@open((+))(z, 1))));
  })))) in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: @Hnd-ex51 in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: @Hnd-ex51 in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: 3 in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: @open(clause-control1)((fn(z, resume){
  (resume((@open((+))(z, 1))));
})) in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: fn(z, resume){
  resume((@open((+))(z, 1)));
} in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: @action in BEnv (fromList [@action]):[a3183,top]@[]
Evaluating: @hhandle(ex51/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a3186,a3183,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a3186,a3183,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a3186,a3183,top]@[]
Evaluating: ex51/@tag in BEnv (fromList [action,hnd,ret]):[a3186,a3183,top]@[]
Evaluating: @open(@new-htag)("ex51@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex51@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a3186,a3183,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a3186,a3183,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a3186,a3183,top]@[]
OPS analysis/aac/benchmarks/ex51 fvs: BEnv (fromList []):[a3186,a3183,top]@[]
Evaluating: (fn(@action){
  ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
          (@open((+))((resume(b)), (@open(ex51)(b))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open(ex52)((Tuple2(1, 2)))), (@open(ex53)(1))));
  })));
})) in BEnv (fromList []):[delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: fn(@action){
  ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
        (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: fn(){
  (fn(@action){
    ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
          (@open((+))((resume(b)), (@open(ex51)(b))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open(ex52)((Tuple2(1, 2)))), (@open(ex53)(1))));
  }));
} in BEnv (fromList []):[delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: ex52/@handle((@Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
      (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: ex52/@handle in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: ex52/@handle in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex52/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex52(3, (@open(clause-control1)((fn(a, resume){
    (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
  })))) in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @Hnd-ex52 in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @Hnd-ex52 in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @open(clause-control1)((fn(a, resume){
  (@open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))));
})) in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: fn(a, resume){
  @open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a)))));
} in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @action in BEnv (fromList [@action]):[a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @hhandle(ex52/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: ex52/@tag in BEnv (fromList [action,hnd,ret]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @open(@new-htag)("ex52@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex52@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
OPS analysis/aac/benchmarks/ex52 fvs: BEnv (fromList []):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: (fn(@action){
  ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
        (@open((+))((resume(b)), (@open(ex51)(b))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open(ex52)((Tuple2(1, 2)))), (@open(ex53)(1))));
})) in BEnv (fromList []):[delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: fn(@action){
  ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
        (@open((+))((resume(b)), (@open(ex51)(b))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: fn(){
  @open((+))((@open(ex52)((Tuple2(1, 2)))), (@open(ex53)(1)));
} in BEnv (fromList []):[delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: ex53/@handle((@Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
      (@open((+))((resume(b)), (@open(ex51)(b))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: ex53/@handle in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: ex53/@handle in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(ex53/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-ex53(3, (@open(clause-control1)((fn(b, resume){
    (@open((+))((resume(b)), (@open(ex51)(b))));
  })))) in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @Hnd-ex53 in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @Hnd-ex53 in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @open(clause-control1)((fn(b, resume){
  (@open((+))((resume(b)), (@open(ex51)(b))));
})) in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: fn(b, resume){
  @open((+))((resume(b)), (@open(ex51)(b)));
} in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @action in BEnv (fromList [@action]):[a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @hhandle(ex53/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a3276,a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a3276,a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a3276,a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: ex53/@tag in BEnv (fromList [action,hnd,ret]):[a3276,a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @open(@new-htag)("ex53@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "ex53@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a3276,a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a3276,a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a3276,a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
OPS analysis/aac/benchmarks/ex53 fvs: BEnv (fromList []):[a3276,a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @open((+))((@open(ex52)((Tuple2(1, 2)))), (@open(ex53)(1))) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: (+) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: fn(x, y){
  @open(int-add)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: @open(ex52)((Tuple2(1, 2))) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: ex52 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex52/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: Tuple2(1, 2) in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: Tuple2 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: 2 in BEnv (fromList []):[delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex52/@select), a) in BEnv (fromList [a]):[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: 0 in BEnv (fromList [a]):[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: forall<e,a> ex52/@select in BEnv (fromList [a]):[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: ex52/@select in BEnv (fromList [a]):[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex52(_, (@ctl-ex52)) : analysis/aac/benchmarks/ex52<e,a> )
       -> @ctl-ex52;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Link create IL@(2759:ex52:[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]) [a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Link create IL@(2759:ex52:[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]) [a3276,a3273,delim]@[(benchmarks:2738,[a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Matched [a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @open((+))((resume((@open(tuple2/fst)(a)))), (@open(ex51)((@open(tuple2/snd)(a))))) in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: (+) in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: resume((@open(tuple2/fst)(a))) in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: resume in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @open(tuple2/fst)(a) in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: tuple2/fst in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2((@x), _) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a3248,a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a3248,a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a3248,a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Applying continuation benchmarks:3241 rebinding BEnv (fromList [])
Link restore IL@(2759:ex52:[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]) [a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Link restore IL@(2759:ex52:[a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]) [a3317,delim]@[(benchmarks:2792,[a3276,a3273,delim]),(benchmarks:2738,[a3222,a3219,delim])]
Evaluating: @open(ex53)(1) in BEnv (fromList []):[delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: ex53 in BEnv (fromList []):[delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex53/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: 1 in BEnv (fromList []):[delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex53/@select), a) in BEnv (fromList [a]):[a3318,delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3318,delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3318,delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a3318,delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3318,delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3318,delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a3318,delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a3318,delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: 0 in BEnv (fromList [a]):[a3318,delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: forall<e,a> ex53/@select in BEnv (fromList [a]):[a3318,delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: ex53/@select in BEnv (fromList [a]):[a3318,delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex53(_, (@ctl-ex53)) : analysis/aac/benchmarks/ex53<e,a> )
       -> @ctl-ex53;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a3318,delim]@[(benchmarks:2759,[a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Matched [a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @open((+))((resume(b)), (@open(ex51)(b))) in BEnv (fromList [b,resume]):[a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: (+) in BEnv (fromList [b,resume]):[a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: resume in BEnv (fromList [b,resume]):[a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: b in BEnv (fromList [b,resume]):[a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Applying continuation benchmarks:3295 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a3315,delim]@[(benchmarks:3295,[a3295,a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: int-add in BEnv (fromList [x,y]):[a3315,delim]@[(benchmarks:3295,[a3295,a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: x in BEnv (fromList [x,y]):[a3315,delim]@[(benchmarks:3295,[a3295,a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: y in BEnv (fromList [x,y]):[a3315,delim]@[(benchmarks:3295,[a3295,a3317,delim]),(benchmarks:3241,[a3241,a3222,a3219,delim])]
Evaluating: @open(ex51)(b) in BEnv (fromList [b,resume]):[a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: ex51 in BEnv (fromList [b,resume]):[a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: fn(a){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex51/@select), a);
} in BEnv (fromList []):[top]@[]
Evaluating: b in BEnv (fromList [b,resume]):[a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex51/@select), a) in BEnv (fromList [a]):[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: 0 in BEnv (fromList [a]):[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: forall<e,a> ex51/@select in BEnv (fromList [a]):[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: ex51/@select in BEnv (fromList [a]):[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-ex51(_, (@ctl-ex51)) : analysis/aac/benchmarks/ex51<e,a> )
       -> @ctl-ex51;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a]):[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Link create IL@(2705:ex51:[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]) [a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Link create IL@(2705:ex51:[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]) [a3241,a3222,a3219,delim]@[(benchmarks:2684,[a3186,a3183,top])]
Matched [a3186,a3183,top]@[]
Evaluating: resume((@open((+))(z, 1))) in BEnv (fromList [resume,z]):[a3186,a3183,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a3186,a3183,top]@[]
Evaluating: @open((+))(z, 1) in BEnv (fromList [resume,z]):[a3186,a3183,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a3186,a3183,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a3186,a3183,top]@[]
Evaluating: 1 in BEnv (fromList [resume,z]):[a3186,a3183,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a3205,a3186,a3183,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a3205,a3186,a3183,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a3205,a3186,a3183,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a3205,a3186,a3183,top]@[]
Applying continuation benchmarks:3203 rebinding BEnv (fromList [])
Link restore IL@(2705:ex51:[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]) [a3296,a3317,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Link restore IL@(2705:ex51:[a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]) [a3296,a3317,delim]@[(benchmarks:3241,[a3241,a3222,a3219,delim]),(benchmarks:2684,[a3186,a3183,top])]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a3293,a3317,delim]@[(benchmarks:2705,[a3296,a3317,delim]),(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a3293,a3317,delim]@[(benchmarks:2705,[a3296,a3317,delim]),(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: x in BEnv (fromList [x,y]):[a3293,a3317,delim]@[(benchmarks:2705,[a3296,a3317,delim]),(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: y in BEnv (fromList [x,y]):[a3293,a3317,delim]@[(benchmarks:2705,[a3296,a3317,delim]),(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: @open(ex51)((@open(tuple2/snd)(a))) in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: ex51 in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: @open(tuple2/snd)(a) in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: tuple2/snd in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: forall<a,b> fn(tuple2){
  (match (tuple2) {
    (@skip Tuple2(_, (@x)) : (a, b) )
       -> @x;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: a in BEnv (fromList [a,resume]):[a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: match (tuple2) {
  (@skip Tuple2(_, (@x)) : (a, b) )
     -> @x;
} in BEnv (fromList [tuple2]):[a3258,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: tuple2 in BEnv (fromList [tuple2]):[a3258,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: @x in BEnv (fromList [@x,tuple2]):[a3258,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex51/@select), a) in BEnv (fromList [a]):[a3242,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3242,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: @perform1 in BEnv (fromList [a]):[a3242,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [a]):[a3242,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3242,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: @evv-at in BEnv (fromList [a]):[a3242,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [a]):[a3242,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: @make-ssize_t in BEnv (fromList [a]):[a3242,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: 0 in BEnv (fromList [a]):[a3242,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: forall<e,a> ex51/@select in BEnv (fromList [a]):[a3242,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: ex51/@select in BEnv (fromList [a]):[a3242,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Evaluating: a in BEnv (fromList [a]):[a3242,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3186,a3183,top])]
Matched [a3203,a3186,a3183,top]@[]
Evaluating: resume((@open((+))(z, 1))) in BEnv (fromList [resume,z]):[a3203,a3186,a3183,top]@[]
Evaluating: resume in BEnv (fromList [resume,z]):[a3203,a3186,a3183,top]@[]
Evaluating: @open((+))(z, 1) in BEnv (fromList [resume,z]):[a3203,a3186,a3183,top]@[]
Evaluating: (+) in BEnv (fromList [resume,z]):[a3203,a3186,a3183,top]@[]
Evaluating: z in BEnv (fromList [resume,z]):[a3203,a3186,a3183,top]@[]
Evaluating: 1 in BEnv (fromList [resume,z]):[a3203,a3186,a3183,top]@[]
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a3205,a3203,a3186,a3183,top]@[]
Evaluating: int-add in BEnv (fromList [x,y]):[a3205,a3203,a3186,a3183,top]@[]
Evaluating: x in BEnv (fromList [x,y]):[a3205,a3203,a3186,a3183,top]@[]
Evaluating: y in BEnv (fromList [x,y]):[a3205,a3203,a3186,a3183,top]@[]
Applying continuation benchmarks:3203 rebinding BEnv (fromList [])
Evaluating: @open(int-add)(x, y) in BEnv (fromList [x,y]):[a3239,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3203,a3186,a3183,top])]
Evaluating: int-add in BEnv (fromList [x,y]):[a3239,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3203,a3186,a3183,top])]
Evaluating: x in BEnv (fromList [x,y]):[a3239,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3203,a3186,a3183,top])]
Evaluating: y in BEnv (fromList [x,y]):[a3239,a3222,a3219,delim]@[(benchmarks:3203,[a3203,a3203,a3186,a3183,top])]
Evaluating: 7 in BEnv (fromList []):[top]@[]
Evaluating: val _ : ()
      = @open(trace)("Example get/set");
val x : int
      = 2;
(fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
        (resume(x));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
          ((fn(@override-action){
            (fn(@action){
              get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                    (resume(b));
                  }))))), (fn(@res){
                  @res;
                }), @action);
            })((fn(){
              (@mask-at((@evv-index(get/@tag)), True, @override-action));
            }));
          })((fn(){
            (resume(Unit));
          })));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(countdown)(0));
  })));
})) in BEnv (fromList []):[top]@[]
Evaluating: @open(trace)("Example get/set") in BEnv (fromList []):[top]@[]
Evaluating: trace in BEnv (fromList []):[top]@[]
Evaluating: "Example get/set" in BEnv (fromList []):[top]@[]
Binding _ to Unit in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: val x : int
      = 2;
(fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
        (resume(x));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
          ((fn(@override-action){
            (fn(@action){
              get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                    (resume(b));
                  }))))), (fn(@res){
                  @res;
                }), @action);
            })((fn(){
              (@mask-at((@evv-index(get/@tag)), True, @override-action));
            }));
          })((fn(){
            (resume(Unit));
          })));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(countdown)(0));
  })));
})) in BEnv (fromList [_]):[top]@[]
Evaluating: 2 in BEnv (fromList [_]):[top]@[]
Binding x to int -> 2 in [top]@[] old: [top]@[]
Applying Let: 0 0
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
        (resume(x));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
          ((fn(@override-action){
            (fn(@action){
              get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                    (resume(b));
                  }))))), (fn(@res){
                  @res;
                }), @action);
            })((fn(){
              (@mask-at((@evv-index(get/@tag)), True, @override-action));
            }));
          })((fn(){
            (resume(Unit));
          })));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(countdown)(0));
  })));
})) in BEnv (fromList [_,x]):[top]@[]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
        (resume(x));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_,x]):[top]@[]
Evaluating: fn(){
  (fn(@action){
    set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
          ((fn(@override-action){
            (fn(@action){
              get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                    (resume(b));
                  }))))), (fn(@res){
                  @res;
                }), @action);
            })((fn(){
              (@mask-at((@evv-index(get/@tag)), True, @override-action));
            }));
          })((fn(){
            (resume(Unit));
          })));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open(countdown)(0));
  }));
} in BEnv (fromList [_,x]):[top]@[]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
      (resume(x));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: get/@handle in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: get/@handle in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(get/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
    (resume(x));
  })))) in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: 3 in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: @open(clause-control1)((fn(_w-l302-c16, resume){
  (resume(x));
})) in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: fn(_w-l302-c16, resume){
  resume(x);
} in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: @action in BEnv (fromList [@action,x]):[a4190,top]@[]
Evaluating: @hhandle(get/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a4193,a4190,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a4193,a4190,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a4193,a4190,top]@[]
Evaluating: get/@tag in BEnv (fromList [action,hnd,ret]):[a4193,a4190,top]@[]
Evaluating: @open(@new-htag)("get@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "get@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a4193,a4190,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a4193,a4190,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a4193,a4190,top]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[a4193,a4190,top]@[]
Evaluating: (fn(@action){
  set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
        ((fn(@override-action){
          (fn(@action){
            get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                  (resume(b));
                }))))), (fn(@res){
                @res;
              }), @action);
          })((fn(){
            (@mask-at((@evv-index(get/@tag)), True, @override-action));
          }));
        })((fn(){
          (resume(Unit));
        })));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open(countdown)(0));
})) in BEnv (fromList []):[delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: fn(@action){
  set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
        ((fn(@override-action){
          (fn(@action){
            get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                  (resume(b));
                }))))), (fn(@res){
                @res;
              }), @action);
          })((fn(){
            (@mask-at((@evv-index(get/@tag)), True, @override-action));
          }));
        })((fn(){
          (resume(Unit));
        })));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList []):[delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: fn(){
  @open(countdown)(0);
} in BEnv (fromList []):[delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
      ((fn(@override-action){
        (fn(@action){
          get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                (resume(b));
              }))))), (fn(@res){
              @res;
            }), @action);
        })((fn(){
          (@mask-at((@evv-index(get/@tag)), True, @override-action));
        }));
      })((fn(){
        (resume(Unit));
      })));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: set/@handle in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: set/@handle in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(set/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-set(3, (@open(clause-control1)((fn(a, resume){
    ((fn(@override-action){
      (fn(@action){
        get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
              (resume(b));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (@mask-at((@evv-index(get/@tag)), True, @override-action));
      }));
    })((fn(){
      (resume(Unit));
    })));
  })))) in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @Hnd-set in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @Hnd-set in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @open(clause-control1)((fn(a, resume){
  ((fn(@override-action){
    (fn(@action){
      get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
            (resume(b));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@mask-at((@evv-index(get/@tag)), True, @override-action));
    }));
  })((fn(){
    (resume(Unit));
  })));
})) in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: fn(a, resume){
  (fn(@override-action){
    (fn(@action){
      get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
            (resume(b));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@mask-at((@evv-index(get/@tag)), True, @override-action));
    }));
  })((fn(){
    (resume(Unit));
  }));
} in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @action in BEnv (fromList [@action]):[a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @hhandle(set/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a4221,a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a4221,a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a4221,a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: set/@tag in BEnv (fromList [action,hnd,ret]):[a4221,a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @open(@new-htag)("set@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "set@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a4221,a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a4221,a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a4221,a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[a4221,a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @open(countdown)(0) in BEnv (fromList []):[delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: countdown in BEnv (fromList []):[delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: fn(@_wildcard-x293_15){
  val i : int
        = @open(get)(0);
  match ((@open((==))(i, 0))) {
    (True() : bool )
       -> i;
    (@skip False() : bool )
       -> val _ : ()
                = @open(set)((@open((-))(i, 1)));
      countdown(0);
  };
} in BEnv (fromList []):[top]@[]
Evaluating: 0 in BEnv (fromList []):[delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList []):[a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @open(get)(0) in BEnv (fromList []):[a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: get in BEnv (fromList []):[a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i);
} in BEnv (fromList []):[top]@[]
Evaluating: 0 in BEnv (fromList []):[a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i) in BEnv (fromList [i]):[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: 0 in BEnv (fromList [i]):[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: forall<e,a> get/@select in BEnv (fromList [i]):[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: get/@select in BEnv (fromList [i]):[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-get(_, (@ctl-get)) : analysis/aac/benchmarks/get<e,a> )
       -> @ctl-get;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Link create IL@(4063:get:[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]) [a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Link create IL@(4063:get:[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]) [a4221,a4218,delim]@[(benchmarks:4042,[a4193,a4190,top])]
Matched [a4193,a4190,top]@[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[a4193,a4190,top]@[]
Evaluating: resume in BEnv (fromList [resume,x]):[a4193,a4190,top]@[]
Evaluating: x in BEnv (fromList [resume,x]):[a4193,a4190,top]@[]
Applying continuation benchmarks:4210 rebinding BEnv (fromList [x])
Link restore IL@(4063:get:[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]) [a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Link restore IL@(4063:get:[a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]) [a4140,a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Binding i to int -> 2 in [a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])] old: [a4289,delim]@[(benchmarks:4096,[a4221,a4218,delim]),(benchmarks:4042,[a4193,a4190,top])]
Applying Let: 0 0
Evaluating: match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList [i]):[a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @open((==))(i, 0) in BEnv (fromList [i]):[a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: (==) in BEnv (fromList [i]):[a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: i in BEnv (fromList [i]):[a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: 0 in BEnv (fromList [i]):[a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: val _ : ()
      = @open(set)((@open((-))(i, 1)));
countdown(0) in BEnv (fromList [i]):[a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @open(set)((@open((-))(i, 1))) in BEnv (fromList [i]):[a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: set in BEnv (fromList [i]):[a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i);
} in BEnv (fromList []):[top]@[]
Evaluating: @open((-))(i, 1) in BEnv (fromList [i]):[a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: (-) in BEnv (fromList [i]):[a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: fn(x, y){
  @open(int-sub)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: 1 in BEnv (fromList [i]):[a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @open(int-sub)(x, y) in BEnv (fromList [x,y]):[a4163,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: int-sub in BEnv (fromList [x,y]):[a4163,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: x in BEnv (fromList [x,y]):[a4163,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: y in BEnv (fromList [x,y]):[a4163,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i) in BEnv (fromList [i]):[a4156,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a4156,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a4156,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a4156,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a4156,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a4156,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a4156,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a4156,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: 0 in BEnv (fromList [i]):[a4156,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: forall<e,a> set/@select in BEnv (fromList [i]):[a4156,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: set/@select in BEnv (fromList [i]):[a4156,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-set(_, (@ctl-set)) : analysis/aac/benchmarks/set<e,a> )
       -> @ctl-set;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a4156,a4289,delim]@[(benchmarks:4063,[a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Matched [a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: (fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(b));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
})((fn(){
  (resume(Unit));
})) in BEnv (fromList [resume]):[a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(b));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
} in BEnv (fromList [resume]):[a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: fn(){
  resume(Unit);
} in BEnv (fromList [resume]):[a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
})) in BEnv (fromList [@override-action]):[a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [@override-action]):[a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
} in BEnv (fromList [@override-action]):[a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(b));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: get/@handle in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: get/@handle in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(b));
  })))) in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @open(clause-control1)((fn(b, resume){
  (resume(b));
})) in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: fn(b, resume){
  resume(b);
} in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @action in BEnv (fromList [@action]):[a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @hhandle(get/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a4244,a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a4244,a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a4244,a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: get/@tag in BEnv (fromList [action,hnd,ret]):[a4244,a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a4244,a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a4244,a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a4244,a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[a4244,a4241,a4238,a4140,a4289,delim]@[(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @mask-at((@evv-index(get/@tag)), True, @override-action) in BEnv (fromList [@override-action]):[delim]@[(benchmarks:4042,[a4244,a4241,a4238,a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Evaluating: @override-action in BEnv (fromList [@override-action]):[delim]@[(benchmarks:4042,[a4244,a4241,a4238,a4140,a4289,delim]),(benchmarks:4210,[a4210,a4193,a4190,top])]
Failed to compile analysis/aac/benchmarks.kk
