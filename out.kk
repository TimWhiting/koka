koka-3.2.2: unregistering (local file changes: src/Core/FlowAnalysis/Full/DMCFAR/DMCFA.hs)
koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.2..
Building library for koka-3.2.2..
[125 of 143] Compiling Core.FlowAnalysis.Full.DMCFAR.DMCFA [Source file changed]
Warning: The following header files listed in the main library's c-sources
will not be used: src/Platform/cpp/Platform/cconsole.h.
Header files should be in the 'include' or 'install-include' stanza.
See https://cabal.readthedocs.io/en/3.10/cabal-package.html#pkg-field-includes
Preprocessing executable 'koka-plain' for koka-3.2.2..
Building executable 'koka-plain' for koka-3.2.2..
[3 of 3] Linking .stack-work/dist/x86_64-linux/ghc-9.6.6/build/koka-plain/koka-plain [Library changed]
Preprocessing executable 'koka' for koka-3.2.2..
Building executable 'koka' for koka-3.2.2..
[18 of 18] Linking .stack-work/dist/x86_64-linux/ghc-9.6.6/build/koka/koka [Library changed]
koka> copy/register
Installing library in /home/tim/koka/.stack-work/install/x86_64-linux/b0990f9ce7f176afb926501e29e9595b91936665080ae0b1590539787cff559a/9.6.6/lib/x86_64-linux-ghc-9.6.6/koka-3.2.2-8GBEfjISoFBMgz1sr3wgW
Installing executable koka-plain in /home/tim/koka/.stack-work/install/x86_64-linux/b0990f9ce7f176afb926501e29e9595b91936665080ae0b1590539787cff559a/9.6.6/bin
Installing executable koka in /home/tim/koka/.stack-work/install/x86_64-linux/b0990f9ce7f176afb926501e29e9595b91936665080ae0b1590539787cff559a/9.6.6/bin
Registering library for koka-3.2.2..
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
  }), @action) in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: get/@handle in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: get/@handle in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(get/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
    (resume(x));
  })))) in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: 3 in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: @open(clause-control1)((fn(_w-l302-c16, resume){
  (resume(x));
})) in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: clause-control1 in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: fn(_w-l302-c16, resume){
  resume(x);
} in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: @action in BEnv (fromList [@action,x]):[a192,top]@[]
Evaluating: @hhandle(get/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a195,a192,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a195,a192,top]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a195,a192,top]@[]
Evaluating: get/@tag in BEnv (fromList [action,hnd,ret]):[a195,a192,top]@[]
Evaluating: @open(@new-htag)("get@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "get@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a195,a192,top]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a195,a192,top]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a195,a192,top]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[a195,a192,top]@[]
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
})) in BEnv (fromList []):[delim]@[(benchmarks:44,[a195,a192,top])]
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
} in BEnv (fromList []):[delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: fn(){
  @open(countdown)(0);
} in BEnv (fromList []):[delim]@[(benchmarks:44,[a195,a192,top])]
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
  }), @action) in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: set/@handle in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: set/@handle in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
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
  })))) in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @Hnd-set in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @Hnd-set in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
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
})) in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
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
} in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @action in BEnv (fromList [@action]):[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @hhandle(set/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: set/@tag in BEnv (fromList [action,hnd,ret]):[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @open(@new-htag)("set@benchmarks") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: "set@benchmarks" in BEnv (fromList []):[top]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @open(countdown)(0) in BEnv (fromList []):[delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: countdown in BEnv (fromList []):[delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: fn(@_wildcard-x293_15){
  val i : int
        = @open(get)(0);
  match ((@open((==))(i, 0))) {
    (True() : bool )
       -> 0;
    (@skip False() : bool )
       -> val _ : ()
                = @open(set)((@open((-))(i, 1)));
      countdown(0);
  };
} in BEnv (fromList []):[top]@[]
Evaluating: 0 in BEnv (fromList []):[delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> 0;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList []):[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @open(get)(0) in BEnv (fromList []):[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: get in BEnv (fromList []):[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i);
} in BEnv (fromList []):[top]@[]
Evaluating: 0 in BEnv (fromList []):[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i) in BEnv (fromList [i]):[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: 0 in BEnv (fromList [i]):[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: forall<e,a> get/@select in BEnv (fromList [i]):[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: get/@select in BEnv (fromList [i]):[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-get(_, (@ctl-get)) : analysis/aac/benchmarks/get<e,a> )
       -> @ctl-get;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Link create IL@(65:get:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]) [a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Link create IL@(65:get:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]) [a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Matched [a195,a192,top]@[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[a195,a192,top]@[]
Evaluating: resume in BEnv (fromList [resume,x]):[a195,a192,top]@[]
Evaluating: x in BEnv (fromList [resume,x]):[a195,a192,top]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])
Link restore IL@(65:get:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]) [a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Link restore IL@(65:get:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]) [a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Binding i to int -> 2 in [a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])] old: [a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Applying Let: 0 0
Evaluating: match ((@open((==))(i, 0))) {
  (True() : bool )
     -> 0;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList [i]):[a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @open((==))(i, 0) in BEnv (fromList [i]):[a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: (==) in BEnv (fromList [i]):[a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: i in BEnv (fromList [i]):[a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: 0 in BEnv (fromList [i]):[a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: val _ : ()
      = @open(set)((@open((-))(i, 1)));
countdown(0) in BEnv (fromList [i]):[a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @open(set)((@open((-))(i, 1))) in BEnv (fromList [i]):[a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: set in BEnv (fromList [i]):[a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i);
} in BEnv (fromList []):[top]@[]
Evaluating: @open((-))(i, 1) in BEnv (fromList [i]):[a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: (-) in BEnv (fromList [i]):[a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(x, y){
  @open(int-sub)(x, y);
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: 1 in BEnv (fromList [i]):[a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @open(int-sub)(x, y) in BEnv (fromList [x,y]):[a165,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: int-sub in BEnv (fromList [x,y]):[a165,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: x in BEnv (fromList [x,y]):[a165,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: y in BEnv (fromList [x,y]):[a165,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i) in BEnv (fromList [i]):[a158,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a158,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @perform1 in BEnv (fromList [i]):[a158,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[a158,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a158,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @evv-at in BEnv (fromList [i]):[a158,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[a158,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[a158,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: 0 in BEnv (fromList [i]):[a158,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: forall<e,a> set/@select in BEnv (fromList [i]):[a158,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: set/@select in BEnv (fromList [i]):[a158,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-set(_, (@ctl-set)) : analysis/aac/benchmarks/set<e,a> )
       -> @ctl-set;
  });
} in BEnv (fromList []):[top]@[]
Evaluating: i in BEnv (fromList [i]):[a158,a291,delim]@[(benchmarks:65,[a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Matched [a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
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
})) in BEnv (fromList [resume]):[a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
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
} in BEnv (fromList [resume]):[a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(){
  resume(Unit);
} in BEnv (fromList [resume]):[a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
})) in BEnv (fromList [@override-action]):[a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [@override-action]):[a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
} in BEnv (fromList [@override-action]):[a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(b));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: get/@handle in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: get/@handle in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(b));
  })))) in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: 3 in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @open(clause-control1)((fn(b, resume){
  (resume(b));
})) in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: clause-control1 in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(b, resume){
  resume(b);
} in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @action in BEnv (fromList [@action]):[a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @hhandle(get/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a246,a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a246,a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a246,a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: get/@tag in BEnv (fromList [action,hnd,ret]):[a246,a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a246,a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a246,a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a246,a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[a246,a243,a240,a142,a291,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @mask-at((@evv-index(get/@tag)), True, @override-action) in BEnv (fromList [@override-action]):[delim]@[(benchmarks:44,[a246,a243,a240,a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @override-action in BEnv (fromList [@override-action]):[delim]@[(benchmarks:44,[a246,a243,a240,a142,a291,delim]),(benchmarks:212,[a212,a195,a192,top])]
Failed to compile analysis/aac/benchmarks.kk
