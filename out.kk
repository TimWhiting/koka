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
})): with env (t_[top]@[],fromList [])
Next AppParam tail-outer:340 0 "Example 44 - mixed effects under both handlers - outer first (tail resume outer)"
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
})): with env (t_[top]@[],fromList [])
Next AppParam tail-outer:236 0 fn(){
  (fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2))))));
  }));
}
Evaluating: ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
      (resume((@open((+))(z, 1))));
    }))))), (fn(@res){
    @res;
  }), @action): with env (t_[a234,top]@[],fromList [(@action,tail-outer:235)])
Next AppParam tail-outer:239 0 @Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
    (resume((@open((+))(z, 1))));
  }))))
Evaluating: @Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
    (resume((@open((+))(z, 1))));
  })))): with env (t_[a234,top]@[],fromList [])
Next AppParam tail-outer:244 0 3
Next AppParam tail-outer:245 1 @open(clause-control1)((fn(z, resume){
  (resume((@open((+))(z, 1))));
}))
Next AppParam tail-outer:249 0 fn(z, resume){
  resume((@open((+))(z, 1)));
}
Next AppParam tail-outer:240 1 fn(@res){
  @res;
}
Next AppParam tail-outer:241 2 @action
Evaluating: @hhandle(ex41/@tag, hnd, ret, action): with env (t_[a237,a234,top]@[],fromList [(action,tail-outer:7),(hnd,tail-outer:7),(ret,tail-outer:7)])
Next AppParam tail-outer:59 0 ex41/@tag
Next AppParam tail-outer:51 0 "ex41@tail-outer"
Next AppParam tail-outer:60 1 hnd
Next AppParam tail-outer:61 2 ret
Next AppParam tail-outer:62 3 action
Evaluating: (fn(@action){
  ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open(tuple2/fst)(a))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2))))));
})): with env (d_[delim]@[((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [])
Next AppParam tail-outer:272 0 fn(){
  @open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2)))));
}
Evaluating: ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
      (resume((@open(tuple2/fst)(a))));
    }))))), (fn(@res){
    @res;
  }), @action): with env (d_[a270,delim]@[((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [(@action,tail-outer:271)])
Next AppParam tail-outer:275 0 @Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
    (resume((@open(tuple2/fst)(a))));
  }))))
Evaluating: @Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
    (resume((@open(tuple2/fst)(a))));
  })))): with env (d_[a270,delim]@[((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [])
Next AppParam tail-outer:280 0 3
Next AppParam tail-outer:281 1 @open(clause-control1)((fn(a, resume){
  (resume((@open(tuple2/fst)(a))));
}))
Next AppParam tail-outer:285 0 fn(a, resume){
  resume((@open(tuple2/fst)(a)));
}
Next AppParam tail-outer:276 1 fn(@res){
  @res;
}
Next AppParam tail-outer:277 2 @action
Evaluating: @hhandle(ex43/@tag, hnd, ret, action): with env (d_[a273,a270,delim]@[((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [(action,tail-outer:31),(hnd,tail-outer:31),(ret,tail-outer:31)])
Next AppParam tail-outer:185 0 ex43/@tag
Next AppParam tail-outer:177 0 "ex43@tail-outer"
Next AppParam tail-outer:186 1 hnd
Next AppParam tail-outer:187 2 ret
Next AppParam tail-outer:188 3 action
Next AppParam tail-outer:306 0 @open((+))((@open(ex41)(0)), 1)
Next AppParam tail-outer:313 0 @open(ex41)(0)
Next AppParam tail-outer:320 0 0
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a): with env (d_[a313,delim]@[((tail-outer:183,analysis/test/tail-outer/ex43),d_[a273,a270,delim]),((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [(a,tail-outer:13)])
Next AppParam tail-outer:86 0 @open(@evv-at)((@open(@make-ssize_t)(0)))
Next AppParam tail-outer:91 0 @open(@make-ssize_t)(0)
Next AppParam tail-outer:97 0 0
Next AppParam tail-outer:87 1 forall<e,a> ex41/@select
Next AppParam tail-outer:88 2 a
Evaluating: resume((@open((+))(z, 1))): with env (t_[a237,a234,top]@[],fromList [(resume,tail-outer:249),(z,tail-outer:249)])
Next AppParam tail-outer:256 0 @open((+))(z, 1)
Next AppParam tail-outer:259 0 z
Next AppParam tail-outer:260 1 1
Next AppParam int:423 0 x
Next AppParam int:424 1 y
Next AppParam tail-outer:314 1 1
Next AppParam int:423 0 x
Next AppParam int:424 1 y
Next AppParam tail-outer:307 1 @open(ex43)((Tuple2(1, 2)))
New result at VStore BI@(421:d_[delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])])
SV int -> (tail-outer:314,2)
Not in:
SValue  lit: (tail-outer:260,1),⊥,⊥,⊥
New:
SV int -> top
New result at VStore B@(x:d_[a306,delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])])
SV int -> top
Not in:
SValue  lit: (tail-outer:260,1),⊥,⊥,⊥
New:
SV int -> top
New result at VStore BI@(421:d_[a306,delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])])
SV int -> top
Not in:
SValue  lit: (tail-outer:314,2),⊥,⊥,⊥
New:
SV int -> top
Next AppParam tail-outer:328 0 Tuple2(1, 2)
Evaluating: Tuple2(1, 2): with env (d_[delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])],fromList [])
Next AppParam tail-outer:334 0 1
Next AppParam tail-outer:335 1 2
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex43/@select), a): with env (d_[a307,delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])],fromList [(a,tail-outer:37)])
Next AppParam tail-outer:212 0 @open(@evv-at)((@open(@make-ssize_t)(0)))
Next AppParam tail-outer:217 0 @open(@make-ssize_t)(0)
Next AppParam tail-outer:223 0 0
Next AppParam tail-outer:213 1 forall<e,a> ex43/@select
Next AppParam tail-outer:214 2 a
Evaluating: resume((@open(tuple2/fst)(a))): with env (d_[a304,a273,a270,delim]@[((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])],fromList [(a,tail-outer:285),(resume,tail-outer:285)])
Next AppParam tail-outer:292 0 @open(tuple2/fst)(a)
Next AppParam tail-outer:295 0 a
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
}: with env (d_[a292,a304,a273,a270,delim]@[((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])],fromList [(tuple2,types:437)])
Next AppParam int:423 0 x
Next AppParam int:424 1 y
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
})): with env (t_[top]@[],fromList [])
Next AppParam tail-outer:340 0 "Example 44 - mixed effects under both handlers - outer first (tail resume outer)"
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
})): with env (t_[top]@[],fromList [])
Next AppParam tail-outer:236 0 fn(){
  (fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2))))));
  }));
}
Evaluating: ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
      (resume((@open((+))(z, 1))));
    }))))), (fn(@res){
    @res;
  }), @action): with env (t_[a234,top]@[],fromList [(@action,tail-outer:235)])
Next AppParam tail-outer:239 0 @Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
    (resume((@open((+))(z, 1))));
  }))))
Evaluating: @Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
    (resume((@open((+))(z, 1))));
  })))): with env (t_[a234,top]@[],fromList [])
Next AppParam tail-outer:244 0 3
Next AppParam tail-outer:245 1 @open(clause-control1)((fn(z, resume){
  (resume((@open((+))(z, 1))));
}))
Next AppParam tail-outer:249 0 fn(z, resume){
  resume((@open((+))(z, 1)));
}
Next AppParam tail-outer:240 1 fn(@res){
  @res;
}
Next AppParam tail-outer:241 2 @action
Evaluating: @hhandle(ex41/@tag, hnd, ret, action): with env (t_[a237,a234,top]@[],fromList [(action,tail-outer:7),(hnd,tail-outer:7),(ret,tail-outer:7)])
Next AppParam tail-outer:59 0 ex41/@tag
Next AppParam tail-outer:51 0 "ex41@tail-outer"
Next AppParam tail-outer:60 1 hnd
Next AppParam tail-outer:61 2 ret
Next AppParam tail-outer:62 3 action
Evaluating: (fn(@action){
  ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open(tuple2/fst)(a))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2))))));
})): with env (d_[delim]@[((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [])
Next AppParam tail-outer:272 0 fn(){
  @open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2)))));
}
Evaluating: ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
      (resume((@open(tuple2/fst)(a))));
    }))))), (fn(@res){
    @res;
  }), @action): with env (d_[a270,delim]@[((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [(@action,tail-outer:271)])
Next AppParam tail-outer:275 0 @Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
    (resume((@open(tuple2/fst)(a))));
  }))))
Evaluating: @Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
    (resume((@open(tuple2/fst)(a))));
  })))): with env (d_[a270,delim]@[((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [])
Next AppParam tail-outer:280 0 3
Next AppParam tail-outer:281 1 @open(clause-control1)((fn(a, resume){
  (resume((@open(tuple2/fst)(a))));
}))
Next AppParam tail-outer:285 0 fn(a, resume){
  resume((@open(tuple2/fst)(a)));
}
Next AppParam tail-outer:276 1 fn(@res){
  @res;
}
Next AppParam tail-outer:277 2 @action
Evaluating: @hhandle(ex43/@tag, hnd, ret, action): with env (d_[a273,a270,delim]@[((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [(action,tail-outer:31),(hnd,tail-outer:31),(ret,tail-outer:31)])
Next AppParam tail-outer:185 0 ex43/@tag
Next AppParam tail-outer:177 0 "ex43@tail-outer"
Next AppParam tail-outer:186 1 hnd
Next AppParam tail-outer:187 2 ret
Next AppParam tail-outer:188 3 action
Next AppParam tail-outer:306 0 @open((+))((@open(ex41)(0)), 1)
Next AppParam tail-outer:313 0 @open(ex41)(0)
Next AppParam tail-outer:320 0 0
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a): with env (d_[a313,delim]@[((tail-outer:183,analysis/test/tail-outer/ex43),d_[a273,a270,delim]),((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [(a,tail-outer:13)])
Next AppParam tail-outer:86 0 @open(@evv-at)((@open(@make-ssize_t)(0)))
Next AppParam tail-outer:91 0 @open(@make-ssize_t)(0)
Next AppParam tail-outer:97 0 0
Next AppParam tail-outer:87 1 forall<e,a> ex41/@select
Next AppParam tail-outer:88 2 a
Evaluating: resume((@open((+))(z, 1))): with env (t_[a237,a234,top]@[],fromList [(resume,tail-outer:249),(z,tail-outer:249)])
Next AppParam tail-outer:256 0 @open((+))(z, 1)
Next AppParam tail-outer:259 0 z
Next AppParam tail-outer:260 1 1
Next AppParam int:423 0 x
Next AppParam int:424 1 y
Next AppParam tail-outer:314 1 1
Next AppParam int:423 0 x
Next AppParam int:424 1 y
Next AppParam tail-outer:307 1 @open(ex43)((Tuple2(1, 2)))
New result at VStore BI@(421:d_[delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])])
SV int -> (tail-outer:314,2)
Not in:
SValue  lit: (tail-outer:260,1),⊥,⊥,⊥
New:
SV int -> top
New result at VStore B@(x:d_[a306,delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])])
SV int -> top
Not in:
SValue  lit: (tail-outer:260,1),⊥,⊥,⊥
New:
SV int -> top
New result at VStore BI@(421:d_[a306,delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])])
SV int -> top
Not in:
SValue  lit: (tail-outer:314,2),⊥,⊥,⊥
New:
SV int -> top
Next AppParam tail-outer:328 0 Tuple2(1, 2)
Evaluating: Tuple2(1, 2): with env (d_[delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])],fromList [])
Next AppParam tail-outer:334 0 1
Next AppParam tail-outer:335 1 2
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex43/@select), a): with env (d_[a307,delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])],fromList [(a,tail-outer:37)])
Next AppParam tail-outer:212 0 @open(@evv-at)((@open(@make-ssize_t)(0)))
Next AppParam tail-outer:217 0 @open(@make-ssize_t)(0)
Next AppParam tail-outer:223 0 0
Next AppParam tail-outer:213 1 forall<e,a> ex43/@select
Next AppParam tail-outer:214 2 a
Evaluating: resume((@open(tuple2/fst)(a))): with env (d_[a304,a273,a270,delim]@[((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])],fromList [(a,tail-outer:285),(resume,tail-outer:285)])
Next AppParam tail-outer:292 0 @open(tuple2/fst)(a)
Next AppParam tail-outer:295 0 a
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
}: with env (d_[a292,a304,a273,a270,delim]@[((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])],fromList [(tuple2,types:437)])
Next AppParam int:423 0 x
Next AppParam int:424 1 y
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
})): with env (t_[top]@[],fromList [])
Next AppParam tail-outer:340 0 "Example 44 - mixed effects under both handlers - outer first (tail resume outer)"
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
})): with env (t_[top]@[],fromList [])
Next AppParam tail-outer:236 0 fn(){
  (fn(@action){
    ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
          (resume((@open(tuple2/fst)(a))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2))))));
  }));
}
Evaluating: ex41/@handle((@Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
      (resume((@open((+))(z, 1))));
    }))))), (fn(@res){
    @res;
  }), @action): with env (t_[a234,top]@[],fromList [(@action,tail-outer:235)])
Next AppParam tail-outer:239 0 @Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
    (resume((@open((+))(z, 1))));
  }))))
Evaluating: @Hnd-ex41(3, (@open(clause-control1)((fn(z, resume){
    (resume((@open((+))(z, 1))));
  })))): with env (t_[a234,top]@[],fromList [])
Next AppParam tail-outer:244 0 3
Next AppParam tail-outer:245 1 @open(clause-control1)((fn(z, resume){
  (resume((@open((+))(z, 1))));
}))
Next AppParam tail-outer:249 0 fn(z, resume){
  resume((@open((+))(z, 1)));
}
Next AppParam tail-outer:240 1 fn(@res){
  @res;
}
Next AppParam tail-outer:241 2 @action
Evaluating: @hhandle(ex41/@tag, hnd, ret, action): with env (t_[a237,a234,top]@[],fromList [(action,tail-outer:7),(hnd,tail-outer:7),(ret,tail-outer:7)])
Next AppParam tail-outer:59 0 ex41/@tag
Next AppParam tail-outer:51 0 "ex41@tail-outer"
Next AppParam tail-outer:60 1 hnd
Next AppParam tail-outer:61 2 ret
Next AppParam tail-outer:62 3 action
Evaluating: (fn(@action){
  ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
        (resume((@open(tuple2/fst)(a))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2))))));
})): with env (d_[delim]@[((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [])
Next AppParam tail-outer:272 0 fn(){
  @open((+))((@open((+))((@open(ex41)(0)), 1)), (@open(ex43)((Tuple2(1, 2)))));
}
Evaluating: ex43/@handle((@Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
      (resume((@open(tuple2/fst)(a))));
    }))))), (fn(@res){
    @res;
  }), @action): with env (d_[a270,delim]@[((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [(@action,tail-outer:271)])
Next AppParam tail-outer:275 0 @Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
    (resume((@open(tuple2/fst)(a))));
  }))))
Evaluating: @Hnd-ex43(3, (@open(clause-control1)((fn(a, resume){
    (resume((@open(tuple2/fst)(a))));
  })))): with env (d_[a270,delim]@[((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [])
Next AppParam tail-outer:280 0 3
Next AppParam tail-outer:281 1 @open(clause-control1)((fn(a, resume){
  (resume((@open(tuple2/fst)(a))));
}))
Next AppParam tail-outer:285 0 fn(a, resume){
  resume((@open(tuple2/fst)(a)));
}
Next AppParam tail-outer:276 1 fn(@res){
  @res;
}
Next AppParam tail-outer:277 2 @action
Evaluating: @hhandle(ex43/@tag, hnd, ret, action): with env (d_[a273,a270,delim]@[((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [(action,tail-outer:31),(hnd,tail-outer:31),(ret,tail-outer:31)])
Next AppParam tail-outer:185 0 ex43/@tag
Next AppParam tail-outer:177 0 "ex43@tail-outer"
Next AppParam tail-outer:186 1 hnd
Next AppParam tail-outer:187 2 ret
Next AppParam tail-outer:188 3 action
Next AppParam tail-outer:306 0 @open((+))((@open(ex41)(0)), 1)
Next AppParam tail-outer:313 0 @open(ex41)(0)
Next AppParam tail-outer:320 0 0
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex41/@select), a): with env (d_[a313,delim]@[((tail-outer:183,analysis/test/tail-outer/ex43),d_[a273,a270,delim]),((tail-outer:57,analysis/test/tail-outer/ex41),t_[a237,a234,top])],fromList [(a,tail-outer:13)])
Next AppParam tail-outer:86 0 @open(@evv-at)((@open(@make-ssize_t)(0)))
Next AppParam tail-outer:91 0 @open(@make-ssize_t)(0)
Next AppParam tail-outer:97 0 0
Next AppParam tail-outer:87 1 forall<e,a> ex41/@select
Next AppParam tail-outer:88 2 a
Evaluating: resume((@open((+))(z, 1))): with env (t_[a237,a234,top]@[],fromList [(resume,tail-outer:249),(z,tail-outer:249)])
Next AppParam tail-outer:256 0 @open((+))(z, 1)
Next AppParam tail-outer:259 0 z
Next AppParam tail-outer:260 1 1
Next AppParam int:423 0 x
Next AppParam int:424 1 y
Next AppParam tail-outer:314 1 1
Next AppParam int:423 0 x
Next AppParam int:424 1 y
Next AppParam tail-outer:307 1 @open(ex43)((Tuple2(1, 2)))
New result at VStore BI@(421:d_[delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])])
SV int -> (tail-outer:314,2)
Not in:
SValue  lit: (tail-outer:260,1),⊥,⊥,⊥
New:
SV int -> top
New result at VStore B@(x:d_[a306,delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])])
SV int -> top
Not in:
SValue  lit: (tail-outer:260,1),⊥,⊥,⊥
New:
SV int -> top
New result at VStore BI@(421:d_[a306,delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])])
SV int -> top
Not in:
SValue  lit: (tail-outer:314,2),⊥,⊥,⊥
New:
SV int -> top
Next AppParam tail-outer:328 0 Tuple2(1, 2)
Evaluating: Tuple2(1, 2): with env (d_[delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])],fromList [])
Next AppParam tail-outer:334 0 1
Next AppParam tail-outer:335 1 2
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> ex43/@select), a): with env (d_[a307,delim]@[((tail-outer:304,analysis/test/tail-outer/ex43),d_[a304,a273,a270,delim]),((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])],fromList [(a,tail-outer:37)])
Next AppParam tail-outer:212 0 @open(@evv-at)((@open(@make-ssize_t)(0)))
Next AppParam tail-outer:217 0 @open(@make-ssize_t)(0)
Next AppParam tail-outer:223 0 0
Next AppParam tail-outer:213 1 forall<e,a> ex43/@select
Next AppParam tail-outer:214 2 a
Evaluating: resume((@open(tuple2/fst)(a))): with env (d_[a304,a273,a270,delim]@[((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])],fromList [(a,tail-outer:285),(resume,tail-outer:285)])
Next AppParam tail-outer:292 0 @open(tuple2/fst)(a)
Next AppParam tail-outer:295 0 a
Evaluating: match (tuple2) {
  (@skip Tuple2((@x), _) : (a, b) )
     -> @x;
}: with env (d_[a292,a304,a273,a270,delim]@[((tail-outer:254,analysis/test/tail-outer/ex41),t_[a254,a237,a234,top])],fromList [(tuple2,types:437)])
Next AppParam int:423 0 x
Next AppParam int:424 1 y
dmcfa,analysis/test/tail-outer/nested-tail-outer-first,5,20,0,152,13,1.0,1.0,1.0,1.0661157024793388,0.009791,0.008338,0.00882
