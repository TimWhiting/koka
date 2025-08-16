koka-3.2.2: unregistering (local file changes: src/Core/Core.hs src/Core/FlowAnalysis/FixpointMonad.hs src/Core/FlowAnalysis/Full/DMCFAR/DMCFA.hs)
koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.2..
Building library for koka-3.2.2..
[ 15 of 143] Compiling Core.FlowAnalysis.FixpointMonad [Source file changed]
[ 53 of 143] Compiling Core.Core [Source file changed]
[125 of 143] Compiling Core.FlowAnalysis.Full.DMCFAR.DMCFA [Source file changed]
Warning: The following header files listed in the main library's c-sources
will not be used: src/Platform/cpp/Platform/cconsole.h.
Header files should be in the 'include' or 'install-include' stanza.
See https://cabal.readthedocs.io/en/3.10/cabal-package.html#pkg-field-includes
Preprocessing executable 'koka-plain' for koka-3.2.2..
Building executable 'koka-plain' for koka-3.2.2..
[3 of 3] Linking .stack-work/dist/aarch64-osx/ghc-9.6.6/build/koka-plain/koka-plain [Library changed]
Preprocessing executable 'koka' for koka-3.2.2..
Building executable 'koka' for koka-3.2.2..
[18 of 18] Linking .stack-work/dist/aarch64-osx/ghc-9.6.6/build/koka/koka [Library changed]
koka> copy/register
Installing library in /Users/timwhiting/koka/.stack-work/install/aarch64-osx/50e7567ab93459510bfd412b9898f4e9df3111e36f9d2dfd4eb8cba51d1770ee/9.6.6/lib/aarch64-osx-ghc-9.6.6/koka-3.2.2-8GBEfjISoFBMgz1sr3wgW
Installing executable koka-plain in /Users/timwhiting/koka/.stack-work/install/aarch64-osx/50e7567ab93459510bfd412b9898f4e9df3111e36f9d2dfd4eb8cba51d1770ee/9.6.6/bin
Installing executable koka in /Users/timwhiting/koka/.stack-work/install/aarch64-osx/50e7567ab93459510bfd412b9898f4e9df3111e36f9d2dfd4eb8cba51d1770ee/9.6.6/bin
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
})) in BEnv (fromList []):[]@[]
Evaluating: @open(trace)("Example get/set") in BEnv (fromList []):[]@[]
Evaluating: trace in BEnv (fromList []):[]@[]
Evaluating: "Example get/set" in BEnv (fromList []):[]@[]
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
})) in BEnv (fromList [_]):[]@[]
Evaluating: 2 in BEnv (fromList [_]):[]@[]
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
})) in BEnv (fromList [_,x]):[]@[]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
        (resume(x));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [_,x]):[]@[]
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
} in BEnv (fromList [_,x]):[]@[]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
      (resume(x));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action,x]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action,x]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action,x]):[]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(get/@tag, hnd, ret, action);
} in BEnv (fromList []):[]@[]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
    (resume(x));
  })))) in BEnv (fromList [@action,x]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action,x]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action,x]):[]@[]
Evaluating: 3 in BEnv (fromList [@action,x]):[]@[]
Evaluating: @open(clause-control1)((fn(_w-l302-c16, resume){
  (resume(x));
})) in BEnv (fromList [@action,x]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action,x]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action,x]):[]@[]
Evaluating: fn(_w-l302-c16, resume){
  resume(x);
} in BEnv (fromList [@action,x]):[]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action,x]):[]@[]
Evaluating: @action in BEnv (fromList [@action,x]):[]@[]
Evaluating: @hhandle(get/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: get/@tag in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @open(@new-htag)("get@benchmarks") in BEnv (fromList []):[]@[]
Evaluating: @new-htag in BEnv (fromList []):[]@[]
Evaluating: @new-htag in BEnv (fromList []):[]@[]
Evaluating: "get@benchmarks" in BEnv (fromList []):[]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
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
})) in BEnv (fromList []):[]@[]
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
} in BEnv (fromList []):[]@[]
Evaluating: fn(){
  @open(countdown)(0);
} in BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Evaluating: @open(countdown)(0) in BEnv (fromList []):[]@[]
Evaluating: countdown in BEnv (fromList []):[]@[]
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
} in BEnv (fromList []):[]@[]
Evaluating: 0 in BEnv (fromList []):[]@[]
Evaluating: val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> 0;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList []):[]@[]
Evaluating: @open(get)(0) in BEnv (fromList []):[]@[]
Evaluating: get in BEnv (fromList []):[]@[]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i);
} in BEnv (fromList []):[]@[]
Evaluating: 0 in BEnv (fromList []):[]@[]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i) in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[]@[]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: forall<e,a> get/@select in BEnv (fromList [i]):[]@[]
Evaluating: get/@select in BEnv (fromList [i]):[]@[]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-get(_, (@ctl-get)) : analysis/aac/benchmarks/get<e,a> )
       -> @ctl-get;
  });
} in BEnv (fromList []):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume in BEnv (fromList [resume,x]):[]@[]
Evaluating: x in BEnv (fromList [resume,x]):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Evaluating: match ((@open((==))(i, 0))) {
  (True() : bool )
     -> 0;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList [i]):[]@[]
Evaluating: @open((==))(i, 0) in BEnv (fromList [i]):[]@[]
Evaluating: (==) in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: val _ : ()
      = @open(set)((@open((-))(i, 1)));
countdown(0) in BEnv (fromList [i]):[]@[]
Evaluating: @open(set)((@open((-))(i, 1))) in BEnv (fromList [i]):[]@[]
Evaluating: set in BEnv (fromList [i]):[]@[]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i);
} in BEnv (fromList []):[]@[]
Evaluating: @open((-))(i, 1) in BEnv (fromList [i]):[]@[]
Evaluating: (-) in BEnv (fromList [i]):[]@[]
Evaluating: fn(x, y){
  @open(int-sub)(x, y);
} in BEnv (fromList []):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: 1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(int-sub)(x, y) in BEnv (fromList [x,y]):[]@[]
Evaluating: int-sub in BEnv (fromList [x,y]):[]@[]
Evaluating: x in BEnv (fromList [x,y]):[]@[]
Evaluating: y in BEnv (fromList [x,y]):[]@[]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i) in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[]@[]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: forall<e,a> set/@select in BEnv (fromList [i]):[]@[]
Evaluating: set/@select in BEnv (fromList [i]):[]@[]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-set(_, (@ctl-set)) : analysis/aac/benchmarks/set<e,a> )
       -> @ctl-set;
  });
} in BEnv (fromList []):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
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
  }), @action) in BEnv (fromList [@action]):[]@[]
Evaluating: set/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: set/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(set/@tag, hnd, ret, action);
} in BEnv (fromList []):[]@[]
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
  })))) in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-set in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-set in BEnv (fromList [@action]):[]@[]
Evaluating: 3 in BEnv (fromList [@action]):[]@[]
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
})) in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
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
} in BEnv (fromList [@action]):[]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[]@[]
Evaluating: @action in BEnv (fromList [@action]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Evaluating: @hhandle(set/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: set/@tag in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @open(@new-htag)("set@benchmarks") in BEnv (fromList []):[]@[]
Evaluating: @new-htag in BEnv (fromList []):[]@[]
Evaluating: @new-htag in BEnv (fromList []):[]@[]
Evaluating: "set@benchmarks" in BEnv (fromList []):[]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
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
})) in BEnv (fromList []):[]@[]
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
} in BEnv (fromList []):[]@[]
Evaluating: fn(){
  @open(countdown)(0);
} in BEnv (fromList []):[]@[]
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
  }), @action) in BEnv (fromList [@action]):[]@[]
Evaluating: set/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: set/@handle in BEnv (fromList [@action]):[]@[]
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
  })))) in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-set in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-set in BEnv (fromList [@action]):[]@[]
Evaluating: 3 in BEnv (fromList [@action]):[]@[]
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
})) in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
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
} in BEnv (fromList [@action]):[]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[]@[]
Evaluating: @action in BEnv (fromList [@action]):[]@[]
Evaluating: @hhandle(set/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: set/@tag in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
Evaluating: @open(countdown)(0) in BEnv (fromList []):[]@[]
Evaluating: countdown in BEnv (fromList []):[]@[]
Evaluating: 0 in BEnv (fromList []):[]@[]
Evaluating: val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> 0;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList []):[]@[]
Evaluating: @open(get)(0) in BEnv (fromList []):[]@[]
Evaluating: get in BEnv (fromList []):[]@[]
Evaluating: 0 in BEnv (fromList []):[]@[]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i) in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[]@[]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: forall<e,a> get/@select in BEnv (fromList [i]):[]@[]
Evaluating: get/@select in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Link []
Evaluating: match ((@open((==))(i, 0))) {
  (True() : bool )
     -> 0;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList [i]):[]@[]
Evaluating: @open((==))(i, 0) in BEnv (fromList [i]):[]@[]
Evaluating: (==) in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: val _ : ()
      = @open(set)((@open((-))(i, 1)));
countdown(0) in BEnv (fromList [i]):[]@[]
Evaluating: @open(set)((@open((-))(i, 1))) in BEnv (fromList [i]):[]@[]
Evaluating: set in BEnv (fromList [i]):[]@[]
Evaluating: @open((-))(i, 1) in BEnv (fromList [i]):[]@[]
Evaluating: (-) in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: 1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(int-sub)(x, y) in BEnv (fromList [x,y]):[]@[]
Evaluating: int-sub in BEnv (fromList [x,y]):[]@[]
Evaluating: x in BEnv (fromList [x,y]):[]@[]
Evaluating: y in BEnv (fromList [x,y]):[]@[]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i) in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[]@[]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: forall<e,a> set/@select in BEnv (fromList [i]):[]@[]
Evaluating: set/@select in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
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
})) in BEnv (fromList [resume]):[]@[]
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
} in BEnv (fromList [resume]):[]@[]
Evaluating: fn(){
  resume(Unit);
} in BEnv (fromList [resume]):[]@[]
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
})) in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
} in BEnv (fromList [@override-action]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
Evaluating: @mask-at((@evv-index(get/@tag)), True, @override-action) in BEnv (fromList [@override-action]):[]@[]
Evaluating: @override-action in BEnv (fromList [@override-action]):[]@[]
Evaluating: resume(Unit) in BEnv (fromList [resume]):[]@[]
Evaluating: resume in BEnv (fromList [resume]):[]@[]
Evaluating: Unit in BEnv (fromList [resume]):[]@[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
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
})) in BEnv (fromList [resume]):[]@[]
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
} in BEnv (fromList [resume]):[]@[]
Evaluating: fn(){
  resume(Unit);
} in BEnv (fromList [resume]):[]@[]
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
})) in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(b));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(b));
  })))) in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: 3 in BEnv (fromList [@action]):[]@[]
Evaluating: @open(clause-control1)((fn(b, resume){
  (resume(b));
})) in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: fn(b, resume){
  resume(b);
} in BEnv (fromList [@action]):[]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[]@[]
Evaluating: @action in BEnv (fromList [@action]):[]@[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Evaluating: resume in BEnv (fromList [b,resume]):[]@[]
Evaluating: b in BEnv (fromList [b,resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Evaluating: match ((@open((==))(i, 0))) {
  (True() : bool )
     -> 0;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList [i]):[]@[]
Evaluating: @open((==))(i, 0) in BEnv (fromList [i]):[]@[]
Evaluating: (==) in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: val _ : ()
      = @open(set)((@open((-))(i, 1)));
countdown(0) in BEnv (fromList [i]):[]@[]
Evaluating: @open(set)((@open((-))(i, 1))) in BEnv (fromList [i]):[]@[]
Evaluating: set in BEnv (fromList [i]):[]@[]
Evaluating: @open((-))(i, 1) in BEnv (fromList [i]):[]@[]
Evaluating: (-) in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: 1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(int-sub)(x, y) in BEnv (fromList [x,y]):[]@[]
Evaluating: int-sub in BEnv (fromList [x,y]):[]@[]
Evaluating: x in BEnv (fromList [x,y]):[]@[]
Evaluating: y in BEnv (fromList [x,y]):[]@[]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i) in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[]@[]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: forall<e,a> set/@select in BEnv (fromList [i]):[]@[]
Evaluating: set/@select in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Link []
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
})) in BEnv (fromList [resume]):[]@[]
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
} in BEnv (fromList [resume]):[]@[]
Evaluating: fn(){
  resume(Unit);
} in BEnv (fromList [resume]):[]@[]
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
})) in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(b));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(b));
  })))) in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: 3 in BEnv (fromList [@action]):[]@[]
Evaluating: @open(clause-control1)((fn(b, resume){
  (resume(b));
})) in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: fn(b, resume){
  resume(b);
} in BEnv (fromList [@action]):[]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[]@[]
Evaluating: @action in BEnv (fromList [@action]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
Link []
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Evaluating: countdown(0) in BEnv (fromList [_,i]):[]@[]
Evaluating: countdown in BEnv (fromList [_,i]):[]@[]
Evaluating: 0 in BEnv (fromList [_,i]):[]@[]
Evaluating: val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> 0;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList []):[]@[]
Evaluating: @open(get)(0) in BEnv (fromList []):[]@[]
Evaluating: get in BEnv (fromList []):[]@[]
Evaluating: 0 in BEnv (fromList []):[]@[]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i) in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[]@[]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: forall<e,a> get/@select in BEnv (fromList [i]):[]@[]
Evaluating: get/@select in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Link []
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
})) in BEnv (fromList [resume]):[]@[]
Link []
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
})) in BEnv (fromList [resume]):[]@[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Evaluating: countdown(0) in BEnv (fromList [_,i]):[]@[]
Evaluating: countdown in BEnv (fromList [_,i]):[]@[]
Evaluating: 0 in BEnv (fromList [_,i]):[]@[]
Evaluating: val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> 0;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList []):[]@[]
Evaluating: @open(get)(0) in BEnv (fromList []):[]@[]
Evaluating: get in BEnv (fromList []):[]@[]
Evaluating: 0 in BEnv (fromList []):[]@[]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i) in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[]@[]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: forall<e,a> get/@select in BEnv (fromList [i]):[]@[]
Evaluating: get/@select in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
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
})) in BEnv (fromList [resume]):[]@[]
Evaluating: countdown(0) in BEnv (fromList [_,i]):[]@[]
Evaluating: countdown in BEnv (fromList [_,i]):[]@[]
Evaluating: 0 in BEnv (fromList [_,i]):[]@[]
Evaluating: val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> 0;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList []):[]@[]
Evaluating: @open(get)(0) in BEnv (fromList []):[]@[]
Evaluating: get in BEnv (fromList []):[]@[]
Evaluating: 0 in BEnv (fromList []):[]@[]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i) in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[]@[]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: forall<e,a> get/@select in BEnv (fromList [i]):[]@[]
Evaluating: get/@select in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Link []
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
})) in BEnv (fromList [resume]):[]@[]
Link []
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
})) in BEnv (fromList [resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Evaluating: resume in BEnv (fromList [resume,x]):[]@[]
Evaluating: x in BEnv (fromList [resume,x]):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Evaluating: resume in BEnv (fromList [b,resume]):[]@[]
Evaluating: b in BEnv (fromList [b,resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Link []
Link []
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
})) in BEnv (fromList [resume]):[]@[]
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
} in BEnv (fromList [resume]):[]@[]
Evaluating: fn(){
  resume(Unit);
} in BEnv (fromList [resume]):[]@[]
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
})) in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(b));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(b));
  })))) in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: 3 in BEnv (fromList [@action]):[]@[]
Evaluating: @open(clause-control1)((fn(b, resume){
  (resume(b));
})) in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: fn(b, resume){
  resume(b);
} in BEnv (fromList [@action]):[]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[]@[]
Evaluating: @action in BEnv (fromList [@action]):[]@[]
Evaluating: @hhandle(get/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: get/@tag in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Link []
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
})) in BEnv (fromList [resume]):[]@[]
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
} in BEnv (fromList [resume]):[]@[]
Evaluating: fn(){
  resume(Unit);
} in BEnv (fromList [resume]):[]@[]
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
})) in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(b));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(b));
  })))) in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: 3 in BEnv (fromList [@action]):[]@[]
Evaluating: @open(clause-control1)((fn(b, resume){
  (resume(b));
})) in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: fn(b, resume){
  resume(b);
} in BEnv (fromList [@action]):[]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[]@[]
Evaluating: @action in BEnv (fromList [@action]):[]@[]
Evaluating: @hhandle(get/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: get/@tag in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume in BEnv (fromList [resume,x]):[]@[]
Evaluating: x in BEnv (fromList [resume,x]):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Evaluating: resume in BEnv (fromList [b,resume]):[]@[]
Evaluating: b in BEnv (fromList [b,resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
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
})) in BEnv (fromList [resume]):[]@[]
Link []
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
})) in BEnv (fromList [resume]):[]@[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Evaluating: countdown(0) in BEnv (fromList [_,i]):[]@[]
Evaluating: countdown in BEnv (fromList [_,i]):[]@[]
Evaluating: 0 in BEnv (fromList [_,i]):[]@[]
Evaluating: val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> 0;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList []):[]@[]
Evaluating: @open(get)(0) in BEnv (fromList []):[]@[]
Evaluating: get in BEnv (fromList []):[]@[]
Evaluating: 0 in BEnv (fromList []):[]@[]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i) in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[]@[]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: forall<e,a> get/@select in BEnv (fromList [i]):[]@[]
Evaluating: get/@select in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume in BEnv (fromList [resume,x]):[]@[]
Evaluating: x in BEnv (fromList [resume,x]):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Evaluating: resume in BEnv (fromList [b,resume]):[]@[]
Evaluating: b in BEnv (fromList [b,resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume in BEnv (fromList [resume,x]):[]@[]
Evaluating: x in BEnv (fromList [resume,x]):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Evaluating: resume in BEnv (fromList [b,resume]):[]@[]
Evaluating: b in BEnv (fromList [b,resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
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
})) in BEnv (fromList [resume]):[]@[]
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
} in BEnv (fromList [resume]):[]@[]
Evaluating: fn(){
  resume(Unit);
} in BEnv (fromList [resume]):[]@[]
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
})) in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(b));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(b));
  })))) in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: 3 in BEnv (fromList [@action]):[]@[]
Evaluating: @open(clause-control1)((fn(b, resume){
  (resume(b));
})) in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: fn(b, resume){
  resume(b);
} in BEnv (fromList [@action]):[]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[]@[]
Evaluating: @action in BEnv (fromList [@action]):[]@[]
Evaluating: @hhandle(get/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: get/@tag in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Evaluating: @mask-at((@evv-index(get/@tag)), True, @override-action) in BEnv (fromList [@override-action]):[]@[]
Evaluating: @override-action in BEnv (fromList [@override-action]):[]@[]
Evaluating: resume(Unit) in BEnv (fromList [resume]):[]@[]
Evaluating: resume in BEnv (fromList [resume]):[]@[]
Evaluating: Unit in BEnv (fromList [resume]):[]@[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume in BEnv (fromList [resume,x]):[]@[]
Evaluating: x in BEnv (fromList [resume,x]):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Evaluating: resume in BEnv (fromList [b,resume]):[]@[]
Evaluating: b in BEnv (fromList [b,resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
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
})) in BEnv (fromList [resume]):[]@[]
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
} in BEnv (fromList [resume]):[]@[]
Evaluating: fn(){
  resume(Unit);
} in BEnv (fromList [resume]):[]@[]
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
})) in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(b));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(b));
  })))) in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: 3 in BEnv (fromList [@action]):[]@[]
Evaluating: @open(clause-control1)((fn(b, resume){
  (resume(b));
})) in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: fn(b, resume){
  resume(b);
} in BEnv (fromList [@action]):[]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[]@[]
Evaluating: @action in BEnv (fromList [@action]):[]@[]
Evaluating: @hhandle(get/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: get/@tag in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Link []
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Link []
Link []
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Link []
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
Link []
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Link []
Link []
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Link []
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
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
})) in BEnv (fromList [resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Link []
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume in BEnv (fromList [resume,x]):[]@[]
Evaluating: x in BEnv (fromList [resume,x]):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Evaluating: resume in BEnv (fromList [b,resume]):[]@[]
Evaluating: b in BEnv (fromList [b,resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
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
})) in BEnv (fromList [resume]):[]@[]
Link []
Link []
Link []
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Link []
Link []
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
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
})) in BEnv (fromList [resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
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
})) in BEnv (fromList [resume]):[]@[]
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
} in BEnv (fromList [resume]):[]@[]
Evaluating: fn(){
  resume(Unit);
} in BEnv (fromList [resume]):[]@[]
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
})) in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(b));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
} in BEnv (fromList [@override-action]):[]@[]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(b));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(b));
  })))) in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: 3 in BEnv (fromList [@action]):[]@[]
Evaluating: @open(clause-control1)((fn(b, resume){
  (resume(b));
})) in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: fn(b, resume){
  resume(b);
} in BEnv (fromList [@action]):[]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[]@[]
Evaluating: @action in BEnv (fromList [@action]):[]@[]
Evaluating: @hhandle(get/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: get/@tag in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
Link []
Link []
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
})) in BEnv (fromList [resume]):[]@[]
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume in BEnv (fromList [resume,x]):[]@[]
Evaluating: x in BEnv (fromList [resume,x]):[]@[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Evaluating: resume(x) in BEnv (fromList [resume,x]):[]@[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Evaluating: resume in BEnv (fromList [b,resume]):[]@[]
Evaluating: b in BEnv (fromList [b,resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Evaluating: resume(b) in BEnv (fromList [b,resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
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
})) in BEnv (fromList [resume]):[]@[]
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
})) in BEnv (fromList [resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
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
})) in BEnv (fromList [resume]):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Link []
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Evaluating: @hhandle(get/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: get/@tag in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
Evaluating: @hhandle(get/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: get/@tag in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[]@[]
Evaluating: action in BEnv (fromList [action,hnd,ret]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
Evaluating: match ((@open((==))(i, 0))) {
  (True() : bool )
     -> 0;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} in BEnv (fromList [i]):[]@[]
Evaluating: @open((==))(i, 0) in BEnv (fromList [i]):[]@[]
Evaluating: (==) in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: val _ : ()
      = @open(set)((@open((-))(i, 1)));
countdown(0) in BEnv (fromList [i]):[]@[]
Evaluating: @open(set)((@open((-))(i, 1))) in BEnv (fromList [i]):[]@[]
Evaluating: set in BEnv (fromList [i]):[]@[]
Evaluating: @open((-))(i, 1) in BEnv (fromList [i]):[]@[]
Evaluating: (-) in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: 1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(int-sub)(x, y) in BEnv (fromList [x,y]):[]@[]
Evaluating: int-sub in BEnv (fromList [x,y]):[]@[]
Evaluating: x in BEnv (fromList [x,y]):[]@[]
Evaluating: y in BEnv (fromList [x,y]):[]@[]
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i) in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @perform1 in BEnv (fromList [i]):[]@[]
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @evv-at in BEnv (fromList [i]):[]@[]
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [i]):[]@[]
Evaluating: @make-ssize_t in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Evaluating: forall<e,a> set/@select in BEnv (fromList [i]):[]@[]
Evaluating: set/@select in BEnv (fromList [i]):[]@[]
Evaluating: i in BEnv (fromList [i]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/get,AI@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [])for
Kont(analysis/aac/benchmarks/get,IL@(65:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/get fvs: BEnv (fromList [x]):[]@[]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(b));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: get/@handle in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(b));
  })))) in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: @Hnd-get in BEnv (fromList [@action]):[]@[]
Evaluating: 3 in BEnv (fromList [@action]):[]@[]
Evaluating: @open(clause-control1)((fn(b, resume){
  (resume(b));
})) in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: clause-control1 in BEnv (fromList [@action]):[]@[]
Evaluating: fn(b, resume){
  resume(b);
} in BEnv (fromList [@action]):[]@[]
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action]):[]@[]
Evaluating: @action in BEnv (fromList [@action]):[]@[]
Evaluating: 0 in BEnv (fromList [i]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,AI@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(65:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(65:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(212:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(212:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(44:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(44:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(44:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(119:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(119:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(263:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(263:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(283:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(283:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
AI@(98:[]@[])
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
AI@(98:[]@[])
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Applying continuation benchmarks:263 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(265:[]@[])
EndMKAddr
B@(b:[]@[])
[]
Applying continuation benchmarks:283 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(285:[]@[])
AI@(98:[]@[])
BI@(285:[]@[])
[]
Applying continuation benchmarks:212 rebinding BEnv (fromList [x])for
Kont(analysis/aac/benchmarks/set,IL@(119:[]@[]),[]@[],Handler {ops = B@(hnd:[]@[]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
AI@(214:[]@[])
EndMKAddr
B@(x:[]@[])
[]
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
Link []
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList [x]):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
OPS analysis/aac/benchmarks/set fvs: BEnv (fromList []):[]@[]
Evaluating: 0 in BEnv (fromList []):[]@[]
d=0,m=0
Result 1 / 1
Result 100.0%, time: 0.427437s
