koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.2..
Building library for koka-3.2.2..
[125 of 143] Compiling Core.FlowAnalysis.Full.DMCFAR.DMCFA [Source file changed]
Warning: The following header files listed in the main library's c-sources
will not be used: src/Platform/cpp/Platform/cconsole.h.
Header files should be in the 'include' or 'install-include' stanza.
See https://cabal.readthedocs.io/en/3.10/cabal-package.html#pkg-field-includes
Preprocessing executable 'koka' for koka-3.2.2..
Building executable 'koka' for koka-3.2.2..
[18 of 18] Linking .stack-work/dist/aarch64-osx/ghc-9.6.6/build/koka/koka [Library changed]
koka> copy/register
Installing library in /Users/timwhiting/koka/.stack-work/install/aarch64-osx/50e7567ab93459510bfd412b9898f4e9df3111e36f9d2dfd4eb8cba51d1770ee/9.6.6/lib/aarch64-osx-ghc-9.6.6/koka-3.2.2-8GBEfjISoFBMgz1sr3wgW
Installing executable koka in /Users/timwhiting/koka/.stack-work/install/aarch64-osx/50e7567ab93459510bfd412b9898f4e9df3111e36f9d2dfd4eb8cba51d1770ee/9.6.6/bin
Registering library for koka-3.2.2..
Evaluating: bio((fn(){
  (session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    })));
})) unix:913:[top]@[]
Evaluating: bio unix:914:[top]@[]
Evaluating: bio unix:916:[top]@[]
Evaluating: forall<a,e> fn(action1){
  local-scope((forall<h> fn(){
    val iev@671 : hdiv<h,string,e>;
    val iev@720 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
    local-var("", (fn(buf){
        ((fn(@action){
          bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
                (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
              }))))), (fn(@res){
              @res;
            }), @action);
        })((fn(){
          (Tuple2(((fn(){
              @mask-builtin((fn(){
                (action1());
              }));
            })()), (local-get(buf, iev@720))));
        })));
      }));
  }));
} unix:19:[top]@[]
Extending store: BI@(19:[top]@[]) with DefNonRec(bio)
Extending store: T@analysis/benchmarks/handlers/unix/bio with DefNonRec(bio)
New result at Step (CEval ExprBasic bio AI@(914:[top]@[]) EndMKAddr [top]@[])
N (CApply AI@(914:[top]@[]) EndMKAddr T@analysis/benchmarks/handlers/unix/bio [])
Not in:
Next (fromList [CEval DefNonRec pub fun bio : forall<a,e> (action1 : () -> <analysis/benchmarks/handlers/unix/bio|e> a) -> e (a, string); EndKAddr T@analysis/benchmarks/handlers/unix/bio [top]@[]])
New:
N (CApply AI@(914:[top]@[]) EndMKAddr T@analysis/benchmarks/handlers/unix/bio [])
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:915 0 fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
}], resolvedArgs = [], parent = LamBody [] bio((fn(){
  (session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    })));
}))}
Evaluating: fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
} unix:915:[top]@[]
Extending store: BI@(915:[top]@[]) with AppParam(fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/bio], parent = LamBody [] bio((fn(){
  (session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    })));
}))}
Extending store: B@(action1:[a913,top]@[]) with AppParam(fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
})
Evaluating: local-scope((forall<h> fn(){
  val iev@671 : hdiv<h,string,e>;
  val iev@720 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action1());
            }));
          })()), (local-get(buf, iev@720))));
      })));
    }));
})) unix:197:[a913,top]@[]
Evaluating: local-scope unix:198:[a913,top]@[]
Evaluating: local-scope unix:200:[a913,top]@[]
Evaluating: forall<a,e> fn(action){
  @open(unsafe-no-local-cast)((forall<h> action))();
} types:1608:[top]@[]
Extending store: BI@(1608:[top]@[]) with DefNonRec(local-scope)
Extending store: T@std/core/types/local-scope with DefNonRec(local-scope)
New result at Step (CEval ExprBasic local-scope AI@(198:[a913,top]@[]) EndMKAddr [a913,top]@[])
N (CApply AI@(198:[a913,top]@[]) EndMKAddr T@std/core/types/local-scope [])
Not in:
Next (fromList [CEval DefNonRec // _Internal_: if local mutation is unobservable, the `:local` effect can be erased by using the `local-scope` function.
// See also: _State in Haskell, by Simon Peyton Jones and John Launchbury_.
pub fun local-scope : forall<a,e> (action : forall<h> () -> <local<h>|e> a) -> e a; EndKAddr T@std/core/types/local-scope [top]@[]])
New:
N (CApply AI@(198:[a913,top]@[]) EndMKAddr T@std/core/types/local-scope [])
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:199 0 forall<h> fn(){
  val iev@671 : hdiv<h,string,e>;
  val iev@720 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action1());
            }));
          })()), (local-get(buf, iev@720))));
      })));
    }));
}], resolvedArgs = [], parent = LamBody [action1] local-scope((forall<h> fn(){
  val iev@671 : hdiv<h,string,e>;
  val iev@720 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action1());
            }));
          })()), (local-get(buf, iev@720))));
      })));
    }));
}))}
Evaluating: forall<h> fn(){
  val iev@671 : hdiv<h,string,e>;
  val iev@720 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action1());
            }));
          })()), (local-get(buf, iev@720))));
      })));
    }));
} unix:199:[a913,top]@[]
Extending store: BI@(199:[a913,top]@[]) with AppParam(forall<h> fn(){
  val iev@671 : hdiv<h,string,e>;
  val iev@720 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action1());
            })
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/types/local-scope], parent = LamBody [action1] local-scope((forall<h> fn(){
  val iev@671 : hdiv<h,string,e>;
  val iev@720 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action1());
            }));
          })()), (local-get(buf, iev@720))));
      })));
    }));
}))}
Extending store: B@(action:[a197,a913,top]@[]) with AppParam(forall<h> fn(){
  val iev@671 : hdiv<h,string,e>;
  val iev@720 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action1());
            })
Evaluating: @open(unsafe-no-local-cast)((forall<h> action))() types:1615:[a197,a913,top]@[]
Evaluating: @open(unsafe-no-local-cast)((forall<h> action)) types:1616:[a197,a913,top]@[]
Evaluating: unsafe-no-local-cast types:1620:[a197,a913,top]@[]
Evaluating: unsafe-no-local-cast types:1621:[a197,a913,top]@[]
Extending store: BI@(1621:[a197,a913,top]@[]) with std/core/types/unsafe-no-local-cast
Applying FApp {totalArgs = 1, leftArgs = [AppParam types:1618 0 forall<h> action], resolvedArgs = [], parent = AppLambda @open(unsafe-no-local-cast)((forall<h> action))}
Evaluating: forall<h> action types:1618:[a197,a913,top]@[]
Evaluating: action types:1622:[a197,a913,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(1621:[a197,a913,top]@[])], parent = AppLambda @open(unsafe-no-local-cast)((forall<h> action))}
Extending store: BI@(1616:[a197,a913,top]@[]) with AppParam(forall<h> fn(){
  val iev@671 : hdiv<h,string,e>;
  val iev@720 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action1());
            })
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [action] @open(unsafe-no-local-cast)((forall<h> action))()}
Rebinding: fromList [action1] from [a913,top]@[] to [a1615,a197,a913,top]@[]
Extending store: B@(action1:[a1615,a197,a913,top]@[]) with AppParam(fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
})
Evaluating: val iev@671 : hdiv<h,string,e>;
val iev@720 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action1());
          }));
        })()), (local-get(buf, iev@720))));
    })));
  })) unix:201:[a1615,a197,a913,top]@[]
Evaluating: @Hnodiv unix:205:[a1615,a197,a913,top]@[]
Evaluating: @Hnodiv unix:274:[a1615,a197,a913,top]@[]
Extending store: BI@(274:[a1615,a197,a913,top]@[]) with @Hnodiv
Applying FLet {groupIdx = 0, numGroups = 2, bindingIdx = 0, numBindings = 1, name = iev@671, resolved = [], parent = LamBody [] val iev@671 : hdiv<h,string,e>;
val iev@720 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action1());
          }));
        })()), (local-get(buf, iev@720))));
    })));
  }))}
Extending store: B@(iev@671:[a1615,a197,a913,top]@[]) with @Hnodiv
Evaluating: @Hnodiv unix:203:[a1615,a197,a913,top]@[]
Evaluating: @Hnodiv unix:275:[a1615,a197,a913,top]@[]
Extending store: BI@(275:[a1615,a197,a913,top]@[]) with @Hnodiv
Applying FLet {groupIdx = 1, numGroups = 2, bindingIdx = 0, numBindings = 1, name = iev@720, resolved = [], parent = LamBody [] val iev@671 : hdiv<h,string,e>;
val iev@720 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action1());
          }));
        })()), (local-get(buf, iev@720))));
    })));
  }))}
Extending store: B@(iev@720:[a1615,a197,a913,top]@[]) with @Hnodiv
Evaluating: local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action1());
          }));
        })()), (local-get(buf, iev@720))));
    })));
  })) unix:206:[a1615,a197,a913,top]@[]
Evaluating: local-var unix:207:[a1615,a197,a913,top]@[]
Evaluating: local-var unix:210:[a1615,a197,a913,top]@[]
Extending store: BI@(210:[a1615,a197,a913,top]@[]) with std/core/hnd/local-var
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:208 0 "",AppParam unix:209 1 fn(buf){
  (fn(@action){
    bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
          (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (Tuple2(((fn(){
        @mask-builtin((fn(){
          (action1());
        }));
      })()), (local-get(buf, iev@720))));
  }));
}], resolvedArgs = [], parent = LetBody local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action1());
          }));
        })()), (local-get(buf, iev@720))));
    })));
  }))}
Evaluating: "" unix:208:[a1615,a197,a913,top]@[]
Extending store: BI@(208:[a1615,a197,a913,top]@[]) with string -> ""
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:209 1 fn(buf){
  (fn(@action){
    bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
          (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (Tuple2(((fn(){
        @mask-builtin((fn(){
          (action1());
        }));
      })()), (local-get(buf, iev@720))));
  }));
}], resolvedArgs = [BI@(210:[a1615,a197,a913,top]@[])], parent = LetBody local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action1());
          }));
        })()), (local-get(buf, iev@720))));
    })));
  }))}
Evaluating: fn(buf){
  (fn(@action){
    bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
          (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (Tuple2(((fn(){
        @mask-builtin((fn(){
          (action1());
        }));
      })()), (local-get(buf, iev@720))));
  }));
} unix:209:[a1615,a197,a913,top]@[]
Extending store: BI@(209:[a1615,a197,a913,top]@[]) with AppParam(fn(buf){
  (fn(@action){
    bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
          (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (Tuple2(((fn(){
        @mask-builtin((fn(){
          (action1());
        }));
      })()), (local-get(buf, iev@720))));
  }));
})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(210:[a1615,a197,a913,top]@[]),BI@(208:[a1615,a197,a913,top]@[])], parent = LetBody local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action1());
          }));
        })()), (local-get(buf, iev@720))));
    })));
  }))}
LocalVar: std/core/hnd/local-var std/core/hnd/local-var
Extending store: B@(buf:[a1615,a197,a913,top]@[]) with string -> ""
Rebinding: fromList [action1,buf,iev@671,iev@720] from [a1615,a197,a913,top]@[] to [delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action1:[delim]@[(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
})
Extending store: B@(buf:[delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> ""
Extending store: B@(iev@671:[delim]@[(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(iev@720:[delim]@[(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Evaluating: (fn(@action){
  bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
        (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (Tuple2(((fn(){
      @mask-builtin((fn(){
        (action1());
      }));
    })()), (local-get(buf, iev@720))));
})) unix:212:[delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(@action){
  bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
        (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
      }))))), (fn(@res){
      @res;
    }), @action);
} unix:213:[delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(213:[delim]@[(unix:206,[a1615,a197,a913,top])]) with AppLambda(fn(@action){
  bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
        (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
      }))))), (fn(@res){
      @res;
    }), @action);
})
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:214 0 fn(){
  Tuple2(((fn(){
      @mask-builtin((fn(){
        (action1());
      }));
    })()), (local-get(buf, iev@720)));
}], resolvedArgs = [], parent = LamBody [buf] (fn(@action){
  bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
        (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (Tuple2(((fn(){
      @mask-builtin((fn(){
        (action1());
      }));
    })()), (local-get(buf, iev@720))));
}))}
Evaluating: fn(){
  Tuple2(((fn(){
      @mask-builtin((fn(){
        (action1());
      }));
    })()), (local-get(buf, iev@720)));
} unix:214:[delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(214:[delim]@[(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  Tuple2(((fn(){
      @mask-builtin((fn(){
        (action1());
      }));
    })()), (local-get(buf, iev@720)));
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(213:[delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [buf] (fn(@action){
  bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
        (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (Tuple2(((fn(){
      @mask-builtin((fn(){
        (action1());
      }));
    })()), (local-get(buf, iev@720))));
}))}
Extending store: B@(@action:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  Tuple2(((fn(){
      @mask-builtin((fn(){
        (action1());
      }));
    })()), (local-get(buf, iev@720)));
})
Rebinding: fromList [buf,iev@671] from [delim]@[(unix:206,[a1615,a197,a913,top])] to [a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: B@(buf:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> ""
Extending store: B@(iev@671:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Evaluating: bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
      (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
    }))))), (fn(@res){
    @res;
  }), @action) unix:215:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: bio/@handle unix:216:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: bio/@handle unix:220:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(bio/@tag, hnd, ret, action);
} unix:7:[top]@[]
Extending store: BI@(7:[top]@[]) with DefNonRec(bio/@handle)
Extending store: T@analysis/benchmarks/handlers/unix/#bio/@handle with DefNonRec(bio/@handle)
New result at Step (CEval ExprBasic bio/@handle AI@(216:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) AI@(206:[delim]@[(unix:206,[a1615,a197,a913,top])]) [a212,delim]@[(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(216:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) AI@(206:[delim]@[(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#bio/@handle [(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // handler for the effect `:bio`
pub fun bio/@handle : forall<a,e,b> (hnd : analysis/benchmarks/handlers/unix/bio<e,b>, ret : (res : a) -> e b, action : () -> <analysis/benchmarks/handlers/unix/bio|e> a) -> e b; EndKAddr T@analysis/benchmarks/handlers/unix/#bio/@handle [top]@[]])
New:
N (CApply AI@(216:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) AI@(206:[delim]@[(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#bio/@handle [(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:217 0 @Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
    (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
  })))),AppParam unix:218 1 fn(@res){
  @res;
},AppParam unix:219 2 @action], resolvedArgs = [], parent = LamBody [@action] bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
      (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
    (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
  })))) unix:217:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: @Hnd-bio unix:221:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: @Hnd-bio unix:224:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(224:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with @Hnd-bio
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:222 0 1,AppParam unix:223 1 @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
}))], resolvedArgs = [], parent = AppParam unix:217 0 @Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
    (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
  }))))}
Evaluating: 1 unix:222:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(222:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with int -> 1
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:223 1 @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
}))], resolvedArgs = [BI@(224:[a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:217 0 @Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
    (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
  }))))}
Evaluating: @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
})) unix:223:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: clause-tail2 unix:229:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: clause-tail2 unix:231:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(231:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/clause-tail2
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:227 0 fn(fd, s){
  local-set(buf, (@open((++))((local-get(buf, iev@671)), s)));
}], resolvedArgs = [], parent = AppParam unix:223 1 @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
}))}
Evaluating: fn(fd, s){
  local-set(buf, (@open((++))((local-get(buf, iev@671)), s)));
} unix:227:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(227:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(fd, s){
  local-set(buf, (@open((++))((local-get(buf, iev@671)), s)));
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(231:[a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:223 1 @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
}))}
Extending store: BI@(223:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/clause-tail2([(,BI@(227:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(224:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]),BI@(222:[a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:217 0 @Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
    (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
  }))))}
Extending store: CI@(@cfc 217:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with int -> 1
Extending store: CI@(@fun-write 217:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/clause-tail2([(,BI@(227:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]))])
Extending store: BI@(217:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with analysis/benchmarks/handlers/unix/@Hnd-bio([(@cfc,CI@(@cfc 217:[a212,delim]@[(unix:206,[a1615,a197,a913,top])])),(@fun-write,CI@(@fun-write 217:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:218 1 fn(@res){
  @res;
},AppParam unix:219 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#bio/@handle], parent = LamBody [@action] bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
      (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} unix:218:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(218:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(@res){
  @res;
})
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:219 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#bio/@handle,BI@(217:[a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [@action] bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
      (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action unix:219:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#bio/@handle,BI@(217:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]),BI@(218:[a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [@action] bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
      (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Extending store: B@(hnd:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with analysis/benchmarks/handlers/unix/@Hnd-bio([(@cfc,CI@(@cfc 217:[a212,delim]@[(unix:206,[a1615,a197,a913,top])])),(@fun-write,CI@(@fun-write 217:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]))])
Extending store: B@(ret:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(@res){
  @res;
})
Extending store: B@(action:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  Tuple2(((fn(){
      @mask-builtin((fn(){
        (action1());
      }));
    })()), (local-get(buf, iev@720)));
})
Evaluating: @hhandle(bio/@tag, hnd, ret, action) unix:142:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: @hhandle unix:143:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: @hhandle unix:148:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(148:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/@hhandle
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:144 0 bio/@tag,AppParam unix:145 1 hnd,AppParam unix:146 2 ret,AppParam unix:147 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
Evaluating: bio/@tag unix:144:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: @open(@new-htag)("bio@unix") unix:5:[top]@[]
Evaluating: @new-htag unix:138:[top]@[]
Evaluating: @new-htag unix:140:[top]@[]
Extending store: BI@(140:[top]@[]) with std/core/hnd/@new-htag
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:136 0 "bio@unix"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:bio`
pub val bio/@tag : hnd/htag<analysis/benchmarks/handlers/unix/bio>;}
Evaluating: "bio@unix" unix:136:[top]@[]
Extending store: BI@(136:[top]@[]) with string -> "bio@unix"
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(140:[top]@[])], parent = DefNonRec // runtime tag for the effect `:bio`
pub val bio/@tag : hnd/htag<analysis/benchmarks/handlers/unix/bio>;}
Extending store: BI@(5:[top]@[]) with std/core/hnd/@new-htag([(,BI@(136:[top]@[]))])
Extending store: T@analysis/benchmarks/handlers/unix/#bio/@tag with std/core/hnd/@new-htag([(,BI@(136:[top]@[]))])
New result at Step (CEval AppParam unix:144 0 bio/@tag AI@(144:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) AI@(206:[delim]@[(unix:206,[a1615,a197,a913,top])]) [a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(144:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) AI@(206:[delim]@[(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#bio/@tag [(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // runtime tag for the effect `:bio`
pub val bio/@tag : hnd/htag<analysis/benchmarks/handlers/unix/bio>; EndKAddr T@analysis/benchmarks/handlers/unix/#bio/@tag [top]@[]])
New:
N (CApply AI@(144:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) AI@(206:[delim]@[(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#bio/@tag [(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:145 1 hnd,AppParam unix:146 2 ret,AppParam unix:147 3 action], resolvedArgs = [BI@(148:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
Evaluating: hnd unix:145:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:146 2 ret,AppParam unix:147 3 action], resolvedArgs = [BI@(148:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#bio/@tag], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
Evaluating: ret unix:146:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:147 3 action], resolvedArgs = [BI@(148:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#bio/@tag,B@(hnd:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
Evaluating: action unix:147:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(148:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#bio/@tag,B@(hnd:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),B@(ret:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
OPS analysis/benchmarks/handlers/unix/bio fvs: BEnv (fromList [action1,buf,iev@671,iev@720]):[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])] unix:142
Rebinding: fromList [buf,iev@671] from [a212,delim]@[(unix:206,[a1615,a197,a913,top])] to [a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: B@(buf:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> ""
Extending store: B@(iev@671:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Rebinding: fromList [action1,buf,iev@720] from [delim]@[(unix:206,[a1615,a197,a913,top])] to [a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action1:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
})
Extending store: B@(buf:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> ""
Extending store: B@(iev@720:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Rebinding: fromList [action1,buf,iev@720] from [delim]@[(unix:206,[a1615,a197,a913,top])] to [delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action1:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
})
Extending store: B@(buf:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with string -> ""
Extending store: B@(iev@720:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Evaluating: Tuple2(((fn(){
    @mask-builtin((fn(){
      (action1());
    }));
  })()), (local-get(buf, iev@720))) unix:255:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: Tuple2 unix:256:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: Tuple2 unix:259:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(259:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Tuple2
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:257 0 (fn(){
  @mask-builtin((fn(){
    (action1());
  }));
})(),AppParam unix:258 1 local-get(buf, iev@720)], resolvedArgs = [], parent = LamBody [] Tuple2(((fn(){
    @mask-builtin((fn(){
      (action1());
    }));
  })()), (local-get(buf, iev@720)))}
Evaluating: (fn(){
  @mask-builtin((fn(){
    (action1());
  }));
})() unix:257:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(){
  @mask-builtin((fn(){
    (action1());
  }));
} unix:260:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(260:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppLambda(fn(){
  @mask-builtin((fn(){
    (action1());
  }));
})
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = AppParam unix:257 0 (fn(){
  @mask-builtin((fn(){
    (action1());
  }));
})()}
Rebinding: fromList [action1] from [delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action1:[a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
})
Evaluating: @mask-builtin((fn(){
  (action1());
})) unix:261:[a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(){
  action1();
} unix:263:[a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(263:[a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  action1();
})
Applying FMask
Evaluating: action1() unix:265:[a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: action1 unix:266:[a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [] action1()}
Evaluating: session-manager3(Root, (fn(){
    val _ : ()
          = (@open(su)(Alice));
    (@open(echo)((@open(whoami)())));
  })) unix:917:[a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: session-manager3 unix:918:[a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: session-manager3 unix:921:[a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: forall<a,e> fn(initial-user, action6){
  local-scope((forall<h> fn(){
    val iev@2567 : hdiv<h,analysis/benchmarks/handlers/unix/user,e>
          = @Hnodiv;
    local-var(initial-user, (fn(user){
        ((fn(@action){
          whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
                (@open(user/show)((local-get(user, iev@2567))));
              }))))), (fn(@res){
              @res;
            }), @action);
        })((fn(){
          ((fn(@action){
            su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
                  (local-set(user, u));
                }))))), (fn(@res){
                @res;
              }), @action);
          })((fn(){
            ((fn(){
              @mask-builtin((fn(){
                (action6());
              }));
            })());
          })));
        })));
      }));
  }));
} unix:77:[top]@[]
Extending store: BI@(77:[top]@[]) with DefNonRec(session-manager3)
Extending store: T@analysis/benchmarks/handlers/unix/session-manager3 with DefNonRec(session-manager3)
New result at Step (CEval ExprBasic session-manager3 AI@(918:[a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(255:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) [a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(918:[a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(255:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/session-manager3 [(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec pub fun session-manager3 : forall<a,e> (initial-user : analysis/benchmarks/handlers/unix/user, action6 : () -> <analysis/benchmarks/handlers/unix/su,analysis/benchmarks/handlers/unix/whoami|e> a) -> e a; EndKAddr T@analysis/benchmarks/handlers/unix/session-manager3 [top]@[]])
New:
N (CApply AI@(918:[a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(255:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/session-manager3 [(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:919 0 Root,AppParam unix:920 1 fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
}], resolvedArgs = [], parent = LamBody [] session-manager3(Root, (fn(){
    val _ : ()
          = (@open(su)(Alice));
    (@open(echo)((@open(whoami)())));
  }))}
Evaluating: Root unix:919:[a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(919:[a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:920 1 fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
}], resolvedArgs = [T@analysis/benchmarks/handlers/unix/session-manager3], parent = LamBody [] session-manager3(Root, (fn(){
    val _ : ()
          = (@open(su)(Alice));
    (@open(echo)((@open(whoami)())));
  }))}
Evaluating: fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
} unix:920:[a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(920:[a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/session-manager3,BI@(919:[a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [] session-manager3(Root, (fn(){
    val _ : ()
          = (@open(su)(Alice));
    (@open(echo)((@open(whoami)())));
  }))}
Extending store: B@(initial-user:[a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Extending store: B@(action6:[a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Evaluating: local-scope((forall<h> fn(){
  val iev@2567 : hdiv<h,analysis/benchmarks/handlers/unix/user,e>
        = @Hnodiv;
  local-var(initial-user, (fn(user){
      ((fn(@action){
        whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
              (@open(user/show)((local-get(user, iev@2567))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(@action){
          su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
                (local-set(user, u));
              }))))), (fn(@res){
              @res;
            }), @action);
        })((fn(){
          ((fn(){
            @mask-builtin((fn(){
              (action6());
            }));
          })());
        })));
      })));
    }));
})) unix:824:[a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: local-scope unix:825:[a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: local-scope unix:827:[a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
New result at Step (CEval ExprBasic local-scope AI@(825:[a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(255:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) [a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(825:[a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(255:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) T@std/core/types/local-scope [(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // _Internal_: if local mutation is unobservable, the `:local` effect can be erased by using the `local-scope` function.
// See also: _State in Haskell, by Simon Peyton Jones and John Launchbury_.
pub fun local-scope : forall<a,e> (action : forall<h> () -> <local<h>|e> a) -> e a; EndKAddr T@std/core/types/local-scope [top]@[]])
New:
N (CApply AI@(825:[a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(255:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) T@std/core/types/local-scope [(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:826 0 forall<h> fn(){
  val iev@2567 : hdiv<h,analysis/benchmarks/handlers/unix/user,e>
        = @Hnodiv;
  local-var(initial-user, (fn(user){
      ((fn(@action){
        whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
              (@open(user/show)((local-get(user, iev@2567))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(@action){
          su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
                (local-set(user, u));
              }))))), (fn(@res){
              @res;
            }), @action);
        })((fn(){
          ((fn(){
            @mask-builtin((fn(){
              (action6());
            }));
          })());
        })));
      })));
    }));
}], resolvedArgs = [], parent = LamBody [initial-user,action6] local-scope((forall<h> fn(){
  val iev@2567 : hdiv<h,analysis/benchmarks/handlers/unix/user,e>
        = @Hnodiv;
  local-var(initial-user, (fn(user){
      ((fn(@action){
        whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
              (@open(user/show)((local-get(user, iev@2567))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(@action){
          su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
                (local-set(user, u));
              }))))), (fn(@res){
              @res;
            }), @action);
        })((fn(){
          ((fn(){
            @mask-builtin((fn(){
              (action6());
            }));
          })());
        })));
      })));
    }));
}))}
Evaluating: forall<h> fn(){
  val iev@2567 : hdiv<h,analysis/benchmarks/handlers/unix/user,e>
        = @Hnodiv;
  local-var(initial-user, (fn(user){
      ((fn(@action){
        whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
              (@open(user/show)((local-get(user, iev@2567))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(@action){
          su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
                (local-set(user, u));
              }))))), (fn(@res){
              @res;
            }), @action);
        })((fn(){
          ((fn(){
            @mask-builtin((fn(){
              (action6());
            }));
          })());
        })));
      })));
    }));
} unix:826:[a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(826:[a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(forall<h> fn(){
  val iev@2567 : hdiv<h,analysis/benchmarks/handlers/unix/user,e>
        = @Hnodiv;
  local-var(initial-user, (fn(user){
      ((fn(@action){
        whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
              (@open(user/show)((local-get(user, iev@2567))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(@action){
          su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
                (local-set(user, u));)
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/types/local-scope], parent = LamBody [initial-user,action6] local-scope((forall<h> fn(){
  val iev@2567 : hdiv<h,analysis/benchmarks/handlers/unix/user,e>
        = @Hnodiv;
  local-var(initial-user, (fn(user){
      ((fn(@action){
        whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
              (@open(user/show)((local-get(user, iev@2567))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(@action){
          su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
                (local-set(user, u));
              }))))), (fn(@res){
              @res;
            }), @action);
        })((fn(){
          ((fn(){
            @mask-builtin((fn(){
              (action6());
            }));
          })());
        })));
      })));
    }));
}))}
Extending store: B@(action:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(forall<h> fn(){
  val iev@2567 : hdiv<h,analysis/benchmarks/handlers/unix/user,e>
        = @Hnodiv;
  local-var(initial-user, (fn(user){
      ((fn(@action){
        whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
              (@open(user/show)((local-get(user, iev@2567))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(@action){
          su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
                (local-set(user, u));)
Evaluating: @open(unsafe-no-local-cast)((forall<h> action))() types:1615:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @open(unsafe-no-local-cast)((forall<h> action)) types:1616:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: unsafe-no-local-cast types:1620:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: unsafe-no-local-cast types:1621:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(1621:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/types/unsafe-no-local-cast
Applying FApp {totalArgs = 1, leftArgs = [AppParam types:1618 0 forall<h> action], resolvedArgs = [], parent = AppLambda @open(unsafe-no-local-cast)((forall<h> action))}
Evaluating: forall<h> action types:1618:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: action types:1622:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(1621:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppLambda @open(unsafe-no-local-cast)((forall<h> action))}
Extending store: BI@(1616:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(forall<h> fn(){
  val iev@2567 : hdiv<h,analysis/benchmarks/handlers/unix/user,e>
        = @Hnodiv;
  local-var(initial-user, (fn(user){
      ((fn(@action){
        whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
              (@open(user/show)((local-get(user, iev@2567))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(@action){
          su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
                (local-set(user, u));)
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [action] @open(unsafe-no-local-cast)((forall<h> action))()}
Rebinding: fromList [action6,initial-user] from [a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(initial-user:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Evaluating: val iev@2567 : hdiv<h,analysis/benchmarks/handlers/unix/user,e>
      = @Hnodiv;
local-var(initial-user, (fn(user){
    ((fn(@action){
      whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
            (@open(user/show)((local-get(user, iev@2567))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      ((fn(@action){
        su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
              (local-set(user, u));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(){
          @mask-builtin((fn(){
            (action6());
          }));
        })());
      })));
    })));
  })) unix:828:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @Hnodiv unix:830:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @Hnodiv unix:912:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(912:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = iev@2567, resolved = [], parent = LamBody [] val iev@2567 : hdiv<h,analysis/benchmarks/handlers/unix/user,e>
      = @Hnodiv;
local-var(initial-user, (fn(user){
    ((fn(@action){
      whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
            (@open(user/show)((local-get(user, iev@2567))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      ((fn(@action){
        su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
              (local-set(user, u));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(){
          @mask-builtin((fn(){
            (action6());
          }));
        })());
      })));
    })));
  }))}
Extending store: B@(iev@2567:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Evaluating: local-var(initial-user, (fn(user){
    ((fn(@action){
      whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
            (@open(user/show)((local-get(user, iev@2567))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      ((fn(@action){
        su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
              (local-set(user, u));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(){
          @mask-builtin((fn(){
            (action6());
          }));
        })());
      })));
    })));
  })) unix:831:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: local-var unix:832:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: local-var unix:835:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(835:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/local-var
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:833 0 initial-user,AppParam unix:834 1 fn(user){
  (fn(@action){
    whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
          (@open(user/show)((local-get(user, iev@2567))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
            (local-set(user, u));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      ((fn(){
        @mask-builtin((fn(){
          (action6());
        }));
      })());
    })));
  }));
}], resolvedArgs = [], parent = LetBody local-var(initial-user, (fn(user){
    ((fn(@action){
      whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
            (@open(user/show)((local-get(user, iev@2567))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      ((fn(@action){
        su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
              (local-set(user, u));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(){
          @mask-builtin((fn(){
            (action6());
          }));
        })());
      })));
    })));
  }))}
Evaluating: initial-user unix:833:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:834 1 fn(user){
  (fn(@action){
    whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
          (@open(user/show)((local-get(user, iev@2567))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
            (local-set(user, u));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      ((fn(){
        @mask-builtin((fn(){
          (action6());
        }));
      })());
    })));
  }));
}], resolvedArgs = [BI@(835:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LetBody local-var(initial-user, (fn(user){
    ((fn(@action){
      whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
            (@open(user/show)((local-get(user, iev@2567))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      ((fn(@action){
        su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
              (local-set(user, u));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(){
          @mask-builtin((fn(){
            (action6());
          }));
        })());
      })));
    })));
  }))}
Evaluating: fn(user){
  (fn(@action){
    whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
          (@open(user/show)((local-get(user, iev@2567))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
            (local-set(user, u));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      ((fn(){
        @mask-builtin((fn(){
          (action6());
        }));
      })());
    })));
  }));
} unix:834:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(834:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(user){
  (fn(@action){
    whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
          (@open(user/show)((local-get(user, iev@2567))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(@action){
      su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
            (local-set(user, u));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      ((fn(){
        @mask-builtin((fn(){
          (action6());
        }));
      }))
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(835:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),B@(initial-user:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LetBody local-var(initial-user, (fn(user){
    ((fn(@action){
      whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
            (@open(user/show)((local-get(user, iev@2567))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      ((fn(@action){
        su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
              (local-set(user, u));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        ((fn(){
          @mask-builtin((fn(){
            (action6());
          }));
        })());
      })));
    })));
  }))}
LocalVar: std/core/hnd/local-var std/core/hnd/local-var
Extending store: B@(user:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Rebinding: fromList [action6,iev@2567,user] from [a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(iev@2567:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(user:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Evaluating: (fn(@action){
  whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
        (@open(user/show)((local-get(user, iev@2567))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
          (local-set(user, u));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(){
      @mask-builtin((fn(){
        (action6());
      }));
    })());
  })));
})) unix:837:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(@action){
  whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
        (@open(user/show)((local-get(user, iev@2567))));
      }))))), (fn(@res){
      @res;
    }), @action);
} unix:838:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(838:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppLambda(fn(@action){
  whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
        (@open(user/show)((local-get(user, iev@2567))));
      }))))), (fn(@res){
      @res;
    }), @action);
})
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:839 0 fn(){
  (fn(@action){
    su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
          (local-set(user, u));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(){
      @mask-builtin((fn(){
        (action6());
      }));
    })());
  }));
}], resolvedArgs = [], parent = LamBody [user] (fn(@action){
  whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
        (@open(user/show)((local-get(user, iev@2567))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
          (local-set(user, u));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(){
      @mask-builtin((fn(){
        (action6());
      }));
    })());
  })));
}))}
Evaluating: fn(){
  (fn(@action){
    su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
          (local-set(user, u));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(){
      @mask-builtin((fn(){
        (action6());
      }));
    })());
  }));
} unix:839:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(839:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  (fn(@action){
    su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
          (local-set(user, u));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(){
      @mask-builtin((fn(){
        (action6());
      }));
    })());
  }));
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(838:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [user] (fn(@action){
  whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
        (@open(user/show)((local-get(user, iev@2567))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(@action){
    su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
          (local-set(user, u));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(){
      @mask-builtin((fn(){
        (action6());
      }));
    })());
  })));
}))}
Extending store: B@(@action:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  (fn(@action){
    su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
          (local-set(user, u));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(){
      @mask-builtin((fn(){
        (action6());
      }));
    })());
  }));
})
Rebinding: fromList [iev@2567,user] from [delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(iev@2567:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(user:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Evaluating: whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
      (@open(user/show)((local-get(user, iev@2567))));
    }))))), (fn(@res){
    @res;
  }), @action) unix:840:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: whoami/@handle unix:841:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: whoami/@handle unix:845:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(whoami/@tag, hnd, ret, action);
} unix:49:[top]@[]
Extending store: BI@(49:[top]@[]) with DefNonRec(whoami/@handle)
Extending store: T@analysis/benchmarks/handlers/unix/#whoami/@handle with DefNonRec(whoami/@handle)
New result at Step (CEval ExprBasic whoami/@handle AI@(841:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(831:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(841:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(831:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#whoami/@handle [(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // handler for the effect `:whoami`
pub fun whoami/@handle : forall<a,e,b> (hnd : analysis/benchmarks/handlers/unix/whoami<e,b>, ret : (res : a) -> e b, action : () -> <analysis/benchmarks/handlers/unix/whoami|e> a) -> e b; EndKAddr T@analysis/benchmarks/handlers/unix/#whoami/@handle [top]@[]])
New:
N (CApply AI@(841:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(831:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#whoami/@handle [(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:842 0 @Hnd-whoami(1, (@open(clause-tail0)((fn(){
    (@open(user/show)((local-get(user, iev@2567))));
  })))),AppParam unix:843 1 fn(@res){
  @res;
},AppParam unix:844 2 @action], resolvedArgs = [], parent = LamBody [@action] whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
      (@open(user/show)((local-get(user, iev@2567))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @Hnd-whoami(1, (@open(clause-tail0)((fn(){
    (@open(user/show)((local-get(user, iev@2567))));
  })))) unix:842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @Hnd-whoami unix:846:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @Hnd-whoami unix:849:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(849:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnd-whoami
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:847 0 1,AppParam unix:848 1 @open(clause-tail0)((fn(){
  (@open(user/show)((local-get(user, iev@2567))));
}))], resolvedArgs = [], parent = AppParam unix:842 0 @Hnd-whoami(1, (@open(clause-tail0)((fn(){
    (@open(user/show)((local-get(user, iev@2567))));
  }))))}
Evaluating: 1 unix:847:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(847:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with int -> 1
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:848 1 @open(clause-tail0)((fn(){
  (@open(user/show)((local-get(user, iev@2567))));
}))], resolvedArgs = [BI@(849:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:842 0 @Hnd-whoami(1, (@open(clause-tail0)((fn(){
    (@open(user/show)((local-get(user, iev@2567))));
  }))))}
Evaluating: @open(clause-tail0)((fn(){
  (@open(user/show)((local-get(user, iev@2567))));
})) unix:848:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: clause-tail0 unix:854:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: clause-tail0 unix:856:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(856:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/clause-tail0
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:852 0 fn(){
  @open(user/show)((local-get(user, iev@2567)));
}], resolvedArgs = [], parent = AppParam unix:848 1 @open(clause-tail0)((fn(){
  (@open(user/show)((local-get(user, iev@2567))));
}))}
Evaluating: fn(){
  @open(user/show)((local-get(user, iev@2567)));
} unix:852:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(852:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  @open(user/show)((local-get(user, iev@2567)));
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(856:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:848 1 @open(clause-tail0)((fn(){
  (@open(user/show)((local-get(user, iev@2567))));
}))}
Extending store: BI@(848:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/clause-tail0([(,BI@(852:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(849:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),BI@(847:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:842 0 @Hnd-whoami(1, (@open(clause-tail0)((fn(){
    (@open(user/show)((local-get(user, iev@2567))));
  }))))}
Extending store: CI@(@cfc 842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with int -> 1
Extending store: CI@(@fun-whoami 842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/clause-tail0([(,BI@(852:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]))])
Extending store: BI@(842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with analysis/benchmarks/handlers/unix/@Hnd-whoami([(@cfc,CI@(@cfc 842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])),(@fun-whoami,CI@(@fun-whoami 842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:843 1 fn(@res){
  @res;
},AppParam unix:844 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#whoami/@handle], parent = LamBody [@action] whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
      (@open(user/show)((local-get(user, iev@2567))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} unix:843:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(843:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(@res){
  @res;
})
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:844 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#whoami/@handle,BI@(842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [@action] whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
      (@open(user/show)((local-get(user, iev@2567))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action unix:844:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#whoami/@handle,BI@(842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),BI@(843:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [@action] whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
      (@open(user/show)((local-get(user, iev@2567))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Extending store: B@(hnd:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with analysis/benchmarks/handlers/unix/@Hnd-whoami([(@cfc,CI@(@cfc 842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])),(@fun-whoami,CI@(@fun-whoami 842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]))])
Extending store: B@(ret:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(@res){
  @res;
})
Extending store: B@(action:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  (fn(@action){
    su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
          (local-set(user, u));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    ((fn(){
      @mask-builtin((fn(){
        (action6());
      }));
    })());
  }));
})
Evaluating: @hhandle(whoami/@tag, hnd, ret, action) unix:493:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @hhandle unix:494:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @hhandle unix:499:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(499:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/@hhandle
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:495 0 whoami/@tag,AppParam unix:496 1 hnd,AppParam unix:497 2 ret,AppParam unix:498 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(whoami/@tag, hnd, ret, action)}
Evaluating: whoami/@tag unix:495:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @open(@new-htag)("whoami@unix") unix:47:[top]@[]
Evaluating: @new-htag unix:489:[top]@[]
Evaluating: @new-htag unix:491:[top]@[]
Extending store: BI@(491:[top]@[]) with std/core/hnd/@new-htag
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:487 0 "whoami@unix"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:whoami`
pub val whoami/@tag : hnd/htag<analysis/benchmarks/handlers/unix/whoami>;}
Evaluating: "whoami@unix" unix:487:[top]@[]
Extending store: BI@(487:[top]@[]) with string -> "whoami@unix"
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(491:[top]@[])], parent = DefNonRec // runtime tag for the effect `:whoami`
pub val whoami/@tag : hnd/htag<analysis/benchmarks/handlers/unix/whoami>;}
Extending store: BI@(47:[top]@[]) with std/core/hnd/@new-htag([(,BI@(487:[top]@[]))])
Extending store: T@analysis/benchmarks/handlers/unix/#whoami/@tag with std/core/hnd/@new-htag([(,BI@(487:[top]@[]))])
New result at Step (CEval AppParam unix:495 0 whoami/@tag AI@(495:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(831:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(495:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(831:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#whoami/@tag [(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // runtime tag for the effect `:whoami`
pub val whoami/@tag : hnd/htag<analysis/benchmarks/handlers/unix/whoami>; EndKAddr T@analysis/benchmarks/handlers/unix/#whoami/@tag [top]@[]])
New:
N (CApply AI@(495:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(831:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#whoami/@tag [(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:496 1 hnd,AppParam unix:497 2 ret,AppParam unix:498 3 action], resolvedArgs = [BI@(499:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [hnd,ret,action] @hhandle(whoami/@tag, hnd, ret, action)}
Evaluating: hnd unix:496:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:497 2 ret,AppParam unix:498 3 action], resolvedArgs = [BI@(499:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#whoami/@tag], parent = LamBody [hnd,ret,action] @hhandle(whoami/@tag, hnd, ret, action)}
Evaluating: ret unix:497:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:498 3 action], resolvedArgs = [BI@(499:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#whoami/@tag,B@(hnd:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [hnd,ret,action] @hhandle(whoami/@tag, hnd, ret, action)}
Evaluating: action unix:498:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(499:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#whoami/@tag,B@(hnd:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),B@(ret:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [hnd,ret,action] @hhandle(whoami/@tag, hnd, ret, action)}
OPS analysis/benchmarks/handlers/unix/whoami fvs: BEnv (fromList [action6,iev@2567,user]):[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] unix:493
Rebinding: fromList [iev@2567,user] from [a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(iev@2567:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(user:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Rebinding: fromList [action6,user] from [delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(user:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Rebinding: fromList [action6,user] from [delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(user:[delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Evaluating: (fn(@action){
  su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
        (local-set(user, u));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(){
    @mask-builtin((fn(){
      (action6());
    }));
  })());
})) unix:873:[delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(@action){
  su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
        (local-set(user, u));
      }))))), (fn(@res){
      @res;
    }), @action);
} unix:874:[delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(874:[delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppLambda(fn(@action){
  su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
        (local-set(user, u));
      }))))), (fn(@res){
      @res;
    }), @action);
})
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:875 0 fn(){
  (fn(){
    @mask-builtin((fn(){
      (action6());
    }));
  })();
}], resolvedArgs = [], parent = LamBody [] (fn(@action){
  su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
        (local-set(user, u));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(){
    @mask-builtin((fn(){
      (action6());
    }));
  })());
}))}
Evaluating: fn(){
  (fn(){
    @mask-builtin((fn(){
      (action6());
    }));
  })();
} unix:875:[delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(875:[delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  (fn(){
    @mask-builtin((fn(){
      (action6());
    }));
  })();
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(874:[delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [] (fn(@action){
  su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
        (local-set(user, u));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  ((fn(){
    @mask-builtin((fn(){
      (action6());
    }));
  })());
}))}
Extending store: B@(@action:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  (fn(){
    @mask-builtin((fn(){
      (action6());
    }));
  })();
})
Rebinding: fromList [user] from [delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(user:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Evaluating: su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
      (local-set(user, u));
    }))))), (fn(@res){
    @res;
  }), @action) unix:876:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: su/@handle unix:877:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: su/@handle unix:881:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(su/@tag, hnd, ret, action);
} unix:65:[top]@[]
Extending store: BI@(65:[top]@[]) with DefNonRec(su/@handle)
Extending store: T@analysis/benchmarks/handlers/unix/#su/@handle with DefNonRec(su/@handle)
New result at Step (CEval ExprBasic su/@handle AI@(877:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(873:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(877:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(873:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#su/@handle [(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // handler for the effect `:su`
pub fun su/@handle : forall<a,e,b> (hnd : analysis/benchmarks/handlers/unix/su<e,b>, ret : (res : a) -> e b, action : () -> <analysis/benchmarks/handlers/unix/su|e> a) -> e b; EndKAddr T@analysis/benchmarks/handlers/unix/#su/@handle [top]@[]])
New:
N (CApply AI@(877:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(873:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#su/@handle [(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:878 0 @Hnd-su(1, (@open(clause-tail1)((fn(u){
    (local-set(user, u));
  })))),AppParam unix:879 1 fn(@res){
  @res;
},AppParam unix:880 2 @action], resolvedArgs = [], parent = LamBody [@action] su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
      (local-set(user, u));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @Hnd-su(1, (@open(clause-tail1)((fn(u){
    (local-set(user, u));
  })))) unix:878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @Hnd-su unix:882:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @Hnd-su unix:885:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(885:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnd-su
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:883 0 1,AppParam unix:884 1 @open(clause-tail1)((fn(u){
  (local-set(user, u));
}))], resolvedArgs = [], parent = AppParam unix:878 0 @Hnd-su(1, (@open(clause-tail1)((fn(u){
    (local-set(user, u));
  }))))}
Evaluating: 1 unix:883:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(883:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with int -> 1
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:884 1 @open(clause-tail1)((fn(u){
  (local-set(user, u));
}))], resolvedArgs = [BI@(885:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:878 0 @Hnd-su(1, (@open(clause-tail1)((fn(u){
    (local-set(user, u));
  }))))}
Evaluating: @open(clause-tail1)((fn(u){
  (local-set(user, u));
})) unix:884:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: clause-tail1 unix:890:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: clause-tail1 unix:892:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(892:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/clause-tail1
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:888 0 fn(u){
  local-set(user, u);
}], resolvedArgs = [], parent = AppParam unix:884 1 @open(clause-tail1)((fn(u){
  (local-set(user, u));
}))}
Evaluating: fn(u){
  local-set(user, u);
} unix:888:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(888:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(u){
  local-set(user, u);
})
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(892:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:884 1 @open(clause-tail1)((fn(u){
  (local-set(user, u));
}))}
Extending store: BI@(884:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/clause-tail1([(,BI@(888:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(885:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),BI@(883:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:878 0 @Hnd-su(1, (@open(clause-tail1)((fn(u){
    (local-set(user, u));
  }))))}
Extending store: CI@(@cfc 878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with int -> 1
Extending store: CI@(@ctl-su 878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/clause-tail1([(,BI@(888:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]))])
Extending store: BI@(878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with analysis/benchmarks/handlers/unix/@Hnd-su([(@cfc,CI@(@cfc 878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])),(@ctl-su,CI@(@ctl-su 878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:879 1 fn(@res){
  @res;
},AppParam unix:880 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#su/@handle], parent = LamBody [@action] su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
      (local-set(user, u));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} unix:879:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(879:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(@res){
  @res;
})
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:880 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#su/@handle,BI@(878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [@action] su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
      (local-set(user, u));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action unix:880:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#su/@handle,BI@(878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),BI@(879:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [@action] su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
      (local-set(user, u));
    }))))), (fn(@res){
    @res;
  }), @action)}
Extending store: B@(hnd:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with analysis/benchmarks/handlers/unix/@Hnd-su([(@cfc,CI@(@cfc 878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])),(@ctl-su,CI@(@ctl-su 878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]))])
Extending store: B@(ret:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(@res){
  @res;
})
Extending store: B@(action:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  (fn(){
    @mask-builtin((fn(){
      (action6());
    }));
  })();
})
Evaluating: @hhandle(su/@tag, hnd, ret, action) unix:620:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @hhandle unix:621:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @hhandle unix:626:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(626:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/@hhandle
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:622 0 su/@tag,AppParam unix:623 1 hnd,AppParam unix:624 2 ret,AppParam unix:625 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(su/@tag, hnd, ret, action)}
Evaluating: su/@tag unix:622:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @open(@new-htag)("su@unix") unix:63:[top]@[]
Evaluating: @new-htag unix:616:[top]@[]
Evaluating: @new-htag unix:618:[top]@[]
Extending store: BI@(618:[top]@[]) with std/core/hnd/@new-htag
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:614 0 "su@unix"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:su`
pub val su/@tag : hnd/htag<analysis/benchmarks/handlers/unix/su>;}
Evaluating: "su@unix" unix:614:[top]@[]
Extending store: BI@(614:[top]@[]) with string -> "su@unix"
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(618:[top]@[])], parent = DefNonRec // runtime tag for the effect `:su`
pub val su/@tag : hnd/htag<analysis/benchmarks/handlers/unix/su>;}
Extending store: BI@(63:[top]@[]) with std/core/hnd/@new-htag([(,BI@(614:[top]@[]))])
Extending store: T@analysis/benchmarks/handlers/unix/#su/@tag with std/core/hnd/@new-htag([(,BI@(614:[top]@[]))])
New result at Step (CEval AppParam unix:622 0 su/@tag AI@(622:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(873:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(622:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(873:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#su/@tag [(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // runtime tag for the effect `:su`
pub val su/@tag : hnd/htag<analysis/benchmarks/handlers/unix/su>; EndKAddr T@analysis/benchmarks/handlers/unix/#su/@tag [top]@[]])
New:
N (CApply AI@(622:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(873:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#su/@tag [(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:623 1 hnd,AppParam unix:624 2 ret,AppParam unix:625 3 action], resolvedArgs = [BI@(626:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [hnd,ret,action] @hhandle(su/@tag, hnd, ret, action)}
Evaluating: hnd unix:623:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:624 2 ret,AppParam unix:625 3 action], resolvedArgs = [BI@(626:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#su/@tag], parent = LamBody [hnd,ret,action] @hhandle(su/@tag, hnd, ret, action)}
Evaluating: ret unix:624:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:625 3 action], resolvedArgs = [BI@(626:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#su/@tag,B@(hnd:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [hnd,ret,action] @hhandle(su/@tag, hnd, ret, action)}
Evaluating: action unix:625:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(626:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#su/@tag,B@(hnd:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),B@(ret:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [hnd,ret,action] @hhandle(su/@tag, hnd, ret, action)}
OPS analysis/benchmarks/handlers/unix/su fvs: BEnv (fromList [action6,user]):[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] unix:620
Rebinding: fromList [user] from [a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(user:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Rebinding: fromList [action6] from [delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Rebinding: fromList [action6] from [delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Evaluating: (fn(){
  @mask-builtin((fn(){
    (action6());
  }));
})() unix:903:[delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(){
  @mask-builtin((fn(){
    (action6());
  }));
} unix:904:[delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(904:[delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppLambda(fn(){
  @mask-builtin((fn(){
    (action6());
  }));
})
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [] (fn(){
  @mask-builtin((fn(){
    (action6());
  }));
})()}
Rebinding: fromList [action6] from [delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Evaluating: @mask-builtin((fn(){
  (action6());
})) unix:905:[a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(){
  action6();
} unix:907:[a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(907:[a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  action6();
})
Applying FMask
Evaluating: action6() unix:909:[a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: action6 unix:910:[a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [] action6()}
Evaluating: val _ : ()
      = @open(su)(Alice);
@open(echo)((@open(whoami)())) unix:923:[a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @open(su)(Alice) unix:925:[a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: su unix:941:[a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(u){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> su/@select), u);
} unix:71:[top]@[]
Extending store: BI@(71:[top]@[]) with DefNonRec(su)
Extending store: T@analysis/benchmarks/handlers/unix/su with DefNonRec(su)
New result at Step (CEval AppParam unix:941 0 su AI@(938:[a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(903:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(938:[a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(903:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/su [(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // Call the `ctl su` operation of the effect `:su`
pub fun su : (u : analysis/benchmarks/handlers/unix/user) -> analysis/benchmarks/handlers/unix/su (); EndKAddr T@analysis/benchmarks/handlers/unix/su [top]@[]])
New:
N (CApply AI@(938:[a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(903:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/su [(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:939 0 Alice], resolvedArgs = [], parent = LetDef val _ : ();}
Evaluating: Alice unix:939:[a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(939:[a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Alice
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/su], parent = LetDef val _ : ();}
Extending store: B@(u:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Alice
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> su/@select), u) unix:641:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @perform1 unix:642:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @perform1 unix:646:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(646:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/@perform1
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:643 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam unix:644 1 forall<e,a> su/@select,AppParam unix:645 2 u], resolvedArgs = [], parent = LamBody [u] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> su/@select), u)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) unix:643:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @evv-at unix:650:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @evv-at unix:652:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(652:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:648 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam unix:643 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) unix:648:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @make-ssize_t unix:656:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(656:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:654 0 0], resolvedArgs = [], parent = AppParam unix:648 0 @open(@make-ssize_t)(0)}
Evaluating: 0 unix:654:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(654:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with int -> 0
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(656:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:648 0 @open(@make-ssize_t)(0)}
Extending store: BI@(648:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with int -> 0
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(652:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:643 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Extending store: BI@(643:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/@evv-at([(,BI@(648:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]))])
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:644 1 forall<e,a> su/@select,AppParam unix:645 2 u], resolvedArgs = [BI@(646:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [u] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> su/@select), u)}
Evaluating: forall<e,a> su/@select unix:644:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: su/@select unix:660:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-su(_, (@ctl-su)) : analysis/benchmarks/handlers/unix/su<e,a> )
       -> @ctl-su;
  });
} unix:69:[top]@[]
Extending store: BI@(69:[top]@[]) with DefNonRec(su/@select)
Extending store: T@analysis/benchmarks/handlers/unix/#su/@select with DefNonRec(su/@select)
New result at Step (CEval ExprBasic su/@select AI@(644:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(903:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(644:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(903:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#su/@select [(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // select `su` operation out of effect `:su`
pub fun su/@select : forall<e,a> (^ hnd : analysis/benchmarks/handlers/unix/su<e,a>) -> hnd/clause1<analysis/benchmarks/handlers/unix/user,(),analysis/benchmarks/handlers/unix/su,e,a>; EndKAddr T@analysis/benchmarks/handlers/unix/#su/@select [top]@[]])
New:
N (CApply AI@(644:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(903:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#su/@select [(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:645 2 u], resolvedArgs = [BI@(646:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),BI@(643:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [u] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> su/@select), u)}
Evaluating: u unix:645:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [BI@(646:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),BI@(643:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#su/@select], parent = LamBody [u] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> su/@select), u)}
Extending store: B@(u:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Alice
Evaluating: local-set(user, u) unix:893:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: local-set unix:894:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: local-set unix:897:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(897:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/types/local-set
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:895 0 user,AppParam unix:896 1 u], resolvedArgs = [], parent = LamBody [u] local-set(user, u)}
Evaluating: user unix:895:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:896 1 u], resolvedArgs = [BI@(897:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [u] local-set(user, u)}
Evaluating: u unix:896:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(897:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),B@(user:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [u] local-set(user, u)}
LocalSet: std/core/types/local-set std/core/types/local-set
[Root,Alice]
[B@(user:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),B@(u:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])]
Extending store: B@(user:[a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Alice
Rebinding: fromList [action6,iev@2567] from [delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(iev@2567:[a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: BI@(893:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Unit
Applying FHLink {linkEff = analysis/benchmarks/handlers/unix/whoami, doCtx = unix:893, hCtx = unix:493, linkKnext = AI@(893:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), linkHnd = Handler {ops = B@(hnd:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), ret = Just AppParam unix:843 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,iev@2567,user])}}
Rebinding: fromList [action6,iev@2567,user] from [a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(iev@2567:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(user:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Applying FResume {label = analysis/benchmarks/handlers/unix/su, vaddr = AI@(641:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), rHnd = Handler {ops = B@(hnd:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), ret = Just AppParam unix:879 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,user])}, rCtx = unix:893}
Applying resume continuation unix:893 analysis/benchmarks/handlers/unix/su
Rebinding: fromList [action6,user] from [a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(user:[a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = _, resolved = [], parent = LamBody [] val _ : ()
      = @open(su)(Alice);
@open(echo)((@open(whoami)()))}
Extending store: B@(_:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Unit
Evaluating: @open(echo)((@open(whoami)())) unix:926:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: echo unix:930:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(s){
  @open(write)(stdout, s);
} unix:17:[top]@[]
Extending store: BI@(17:[top]@[]) with DefNonRec(echo)
Extending store: T@analysis/benchmarks/handlers/unix/echo with DefNonRec(echo)
New result at Step (CEval AppParam unix:930 0 echo AI@(927:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(927:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/echo [(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec pub fun echo : (s : string) -> analysis/benchmarks/handlers/unix/bio (); EndKAddr T@analysis/benchmarks/handlers/unix/echo [top]@[]])
New:
N (CApply AI@(927:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/echo [(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:928 0 @open(whoami)()], resolvedArgs = [], parent = LetBody @open(echo)((@open(whoami)()))}
Evaluating: @open(whoami)() unix:928:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: whoami unix:935:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(){
  @perform0((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> whoami/@select));
} unix:55:[top]@[]
Extending store: BI@(55:[top]@[]) with DefNonRec(whoami)
Extending store: T@analysis/benchmarks/handlers/unix/whoami with DefNonRec(whoami)
New result at Step (CEval AppParam unix:935 0 whoami AI@(933:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(933:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/whoami [(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // Call the `fun whoami` operation of the effect `:whoami`
pub fun whoami : () -> analysis/benchmarks/handlers/unix/whoami string; EndKAddr T@analysis/benchmarks/handlers/unix/whoami [top]@[]])
New:
N (CApply AI@(933:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/whoami [(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = AppParam unix:928 0 @open(whoami)()}
Evaluating: @perform0((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> whoami/@select)) unix:514:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @perform0 unix:515:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @perform0 unix:518:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(518:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/@perform0
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:516 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam unix:517 1 forall<e,a> whoami/@select], resolvedArgs = [], parent = LamBody [] @perform0((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> whoami/@select))}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) unix:516:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @evv-at unix:522:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @evv-at unix:524:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(524:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:520 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam unix:516 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) unix:520:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @make-ssize_t unix:528:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(528:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:526 0 0], resolvedArgs = [], parent = AppParam unix:520 0 @open(@make-ssize_t)(0)}
Evaluating: 0 unix:526:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(526:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with int -> 0
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(528:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:520 0 @open(@make-ssize_t)(0)}
Extending store: BI@(520:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with int -> 0
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(524:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:516 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Extending store: BI@(516:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/@evv-at([(,BI@(520:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]))])
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:517 1 forall<e,a> whoami/@select], resolvedArgs = [BI@(518:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [] @perform0((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> whoami/@select))}
Evaluating: forall<e,a> whoami/@select unix:517:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: whoami/@select unix:532:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-whoami(_, (@fun-whoami)) : analysis/benchmarks/handlers/unix/whoami<e,a> )
       -> @fun-whoami;
  });
} unix:53:[top]@[]
Extending store: BI@(53:[top]@[]) with DefNonRec(whoami/@select)
Extending store: T@analysis/benchmarks/handlers/unix/#whoami/@select with DefNonRec(whoami/@select)
New result at Step (CEval ExprBasic whoami/@select AI@(517:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(517:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#whoami/@select [(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // select `whoami` operation out of effect `:whoami`
pub fun whoami/@select : forall<e,a> (^ hnd : analysis/benchmarks/handlers/unix/whoami<e,a>) -> hnd/clause0<string,analysis/benchmarks/handlers/unix/whoami,e,a>; EndKAddr T@analysis/benchmarks/handlers/unix/#whoami/@select [top]@[]])
New:
N (CApply AI@(517:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#whoami/@select [(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(518:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),BI@(516:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [] @perform0((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> whoami/@select))}
Evaluating: @open(user/show)((local-get(user, iev@2567))) unix:857:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: user/show unix:861:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(user){
  match (user) {
    (Root() : analysis/benchmarks/handlers/unix/user )
       -> "root";
    (Alice() : analysis/benchmarks/handlers/unix/user )
       -> "alice";
    (@skip Bob() : analysis/benchmarks/handlers/unix/user )
       -> "bob";
  };
} unix:43:[top]@[]
Extending store: BI@(43:[top]@[]) with DefNonRec(user/show)
Extending store: T@analysis/benchmarks/handlers/unix/#user/show with DefNonRec(user/show)
New result at Step (CEval AppParam unix:861 0 user/show AI@(858:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(858:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#user/show [(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec pub fun user/show : (user : analysis/benchmarks/handlers/unix/user) -> string; EndKAddr T@analysis/benchmarks/handlers/unix/#user/show [top]@[]])
New:
N (CApply AI@(858:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#user/show [(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:859 0 local-get(user, iev@2567)], resolvedArgs = [], parent = LamBody [] @open(user/show)((local-get(user, iev@2567)))}
Evaluating: local-get(user, iev@2567) unix:859:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: local-get unix:864:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: local-get unix:867:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(867:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/types/local-get
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:865 0 user,AppParam unix:866 1 iev@2567], resolvedArgs = [], parent = AppParam unix:859 0 local-get(user, iev@2567)}
Evaluating: user unix:865:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:866 1 iev@2567], resolvedArgs = [BI@(867:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:859 0 local-get(user, iev@2567)}
Evaluating: iev@2567 unix:866:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(867:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),B@(user:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:859 0 local-get(user, iev@2567)}
LocalGet: std/core/types/local-get std/core/types/local-get
B@(user:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#user/show], parent = LamBody [] @open(user/show)((local-get(user, iev@2567)))}
Extending store: B@(user:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Alice
Evaluating: match (user) {
  (Root() : analysis/benchmarks/handlers/unix/user )
     -> "root";
  (Alice() : analysis/benchmarks/handlers/unix/user )
     -> "alice";
  (@skip Bob() : analysis/benchmarks/handlers/unix/user )
     -> "bob";
} unix:472:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: user unix:473:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FScrut {parent = LamBody [user] match (user) {
  (Root() : analysis/benchmarks/handlers/unix/user )
     -> "root";
  (Alice() : analysis/benchmarks/handlers/unix/user )
     -> "alice";
  (@skip Bob() : analysis/benchmarks/handlers/unix/user )
     -> "bob";
}, branches = [CaseBranch 0 (analysis/benchmarks/handlers/unix/Root() : analysis/benchmarks/handlers/unix/user )
   -> "root";,CaseBranch 1 (analysis/benchmarks/handlers/unix/Alice() : analysis/benchmarks/handlers/unix/user )
   -> "alice";,CaseBranch 2 (@skip analysis/benchmarks/handlers/unix/Bob() : analysis/benchmarks/handlers/unix/user )
   -> "bob";]}
Evaluating: "alice" unix:475:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(475:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with string -> "alice"
Applying FResume {label = analysis/benchmarks/handlers/unix/whoami, vaddr = IL@(514:whoami:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), rHnd = Handler {ops = B@(hnd:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), ret = Just AppParam unix:843 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,iev@2567,user])}, rCtx = unix:857}
Applying resume continuation unix:857 analysis/benchmarks/handlers/unix/whoami
Rebinding: fromList [action6,iev@2567,user] from [a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(iev@2567:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(user:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
New result at VStore B@(user:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
SV Root
Not in:
SValue  constrs: (AppParam unix:939 0 Alice,[]) lit: ⊥,⊥,⊥,⊥
New:
SV Root
New result at Step (CApply AI@(473:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) B@(user:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CEval CaseBranch 0 (analysis/benchmarks/handlers/unix/Root() : analysis/benchmarks/handlers/unix/user )
   -> "root"; AI@(472:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval CaseBranch 1 (analysis/benchmarks/handlers/unix/Alice() : analysis/benchmarks/handlers/unix/user )
   -> "alice"; AI@(472:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]])
New:
N (CEval CaseBranch 0 (analysis/benchmarks/handlers/unix/Root() : analysis/benchmarks/handlers/unix/user )
   -> "root"; AI@(472:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(893:[a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Evaluating: "root" unix:474:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(474:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with string -> "root"
Applying FResume {label = analysis/benchmarks/handlers/unix/whoami, vaddr = IL@(514:whoami:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), rHnd = Handler {ops = B@(hnd:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), ret = Just AppParam unix:843 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,iev@2567,user])}, rCtx = unix:857}
Applying resume continuation unix:857 analysis/benchmarks/handlers/unix/whoami
Rebinding: fromList [action6,iev@2567,user] from [a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(iev@2567:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(user:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Applying FHLink {linkEff = analysis/benchmarks/handlers/unix/su, doCtx = unix:514, hCtx = unix:893, linkKnext = AI@(514:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), linkHnd = Handler {ops = B@(hnd:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), ret = Just AppParam unix:879 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,user])}}
Rebinding: fromList [action6,user] from [a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(user:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/echo], parent = LetBody @open(echo)((@open(whoami)()))}
Extending store: B@(s:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with string -> "root"
Evaluating: @open(write)(stdout, s) unix:187:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: write unix:192:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(fd, s){
  @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s);
} unix:13:[top]@[]
Extending store: BI@(13:[top]@[]) with DefNonRec(write)
Extending store: T@analysis/benchmarks/handlers/unix/write with DefNonRec(write)
New result at Step (CEval AppParam unix:192 0 write AI@(188:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(514:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(188:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(514:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/write [(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // Write a string to a file descriptor

// Call the `fun write` operation of the effect `:bio`
pub fun write : (fd : analysis/benchmarks/handlers/unix/filedesc, s : string) -> analysis/benchmarks/handlers/unix/bio (); EndKAddr T@analysis/benchmarks/handlers/unix/write [top]@[]])
New:
N (CApply AI@(188:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(514:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/write [(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:189 0 stdout,AppParam unix:190 1 s], resolvedArgs = [], parent = LamBody [s] @open(write)(stdout, s)}
Evaluating: stdout unix:189:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: 0 unix:15:[top]@[]
Extending store: BI@(15:[top]@[]) with int -> 0
Extending store: T@analysis/benchmarks/handlers/unix/stdout with int -> 0
New result at Step (CEval AppParam unix:189 0 stdout AI@(189:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(514:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(189:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(514:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/stdout [(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec pub val stdout : int; EndKAddr T@analysis/benchmarks/handlers/unix/stdout [top]@[]])
New:
N (CApply AI@(189:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(514:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/stdout [(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:190 1 s], resolvedArgs = [T@analysis/benchmarks/handlers/unix/write], parent = LamBody [s] @open(write)(stdout, s)}
Evaluating: s unix:190:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/write,T@analysis/benchmarks/handlers/unix/stdout], parent = LamBody [s] @open(write)(stdout, s)}
Extending store: B@(fd:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with int -> 0
Extending store: B@(s:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with string -> "root"
Evaluating: @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s) unix:163:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @perform2 unix:164:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @perform2 unix:169:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(169:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/@perform2
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:165 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam unix:166 1 forall<e,a> write/@select,AppParam unix:167 2 fd,AppParam unix:168 3 s], resolvedArgs = [], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) unix:165:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @evv-at unix:173:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @evv-at unix:175:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(175:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/@evv-at
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:171 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam unix:165 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) unix:171:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @make-ssize_t unix:179:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(179:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:177 0 0], resolvedArgs = [], parent = AppParam unix:171 0 @open(@make-ssize_t)(0)}
Evaluating: 0 unix:177:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(177:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with int -> 0
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(179:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:171 0 @open(@make-ssize_t)(0)}
Extending store: BI@(171:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with int -> 0
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(175:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:165 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Extending store: BI@(165:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/hnd/@evv-at([(,BI@(171:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]))])
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:166 1 forall<e,a> write/@select,AppParam unix:167 2 fd,AppParam unix:168 3 s], resolvedArgs = [BI@(169:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: forall<e,a> write/@select unix:166:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: write/@select unix:183:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-bio(_, (@fun-write)) : analysis/benchmarks/handlers/unix/bio<e,a> )
       -> @fun-write;
  });
} unix:11:[top]@[]
Extending store: BI@(11:[top]@[]) with DefNonRec(write/@select)
Extending store: T@analysis/benchmarks/handlers/unix/#write/@select with DefNonRec(write/@select)
New result at Step (CEval ExprBasic write/@select AI@(166:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(514:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) [a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(166:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(514:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#write/@select [(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // select `write` operation out of effect `:bio`
pub fun write/@select : forall<e,a> (^ hnd : analysis/benchmarks/handlers/unix/bio<e,a>) -> hnd/clause2<analysis/benchmarks/handlers/unix/filedesc,string,(),analysis/benchmarks/handlers/unix/bio,e,a>; EndKAddr T@analysis/benchmarks/handlers/unix/#write/@select [top]@[]])
New:
N (CApply AI@(166:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) AI@(514:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) T@analysis/benchmarks/handlers/unix/#write/@select [(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:167 2 fd,AppParam unix:168 3 s], resolvedArgs = [BI@(169:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),BI@(165:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: fd unix:167:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:168 3 s], resolvedArgs = [BI@(169:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),BI@(165:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#write/@select], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: s unix:168:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(169:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),BI@(165:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#write/@select,B@(fd:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Extending store: B@(fd:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with int -> 0
Extending store: B@(s:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> "root"
Evaluating: local-set(buf, (@open((++))((local-get(buf, iev@671)), s))) unix:232:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: local-set unix:233:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: local-set unix:236:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(236:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with std/core/types/local-set
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:234 0 buf,AppParam unix:235 1 @open((++))((local-get(buf, iev@671)), s)], resolvedArgs = [], parent = LamBody [fd,s] local-set(buf, (@open((++))((local-get(buf, iev@671)), s)))}
Evaluating: buf unix:234:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:235 1 @open((++))((local-get(buf, iev@671)), s)], resolvedArgs = [BI@(236:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [fd,s] local-set(buf, (@open((++))((local-get(buf, iev@671)), s)))}
Evaluating: @open((++))((local-get(buf, iev@671)), s) unix:235:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: (++) unix:242:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(x, y){
  @open((@extern-x++))(x, y);
} types:1602:[top]@[]
Extending store: BI@(1602:[top]@[]) with DefNonRec((++))
Extending store: T@std/core/types/(++) with DefNonRec((++))
New result at Step (CEval AppParam unix:242 0 (++) AI@(238:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) AI@(206:[delim]@[(unix:206,[a1615,a197,a913,top])]) [a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])
N (CApply AI@(238:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) AI@(206:[delim]@[(unix:206,[a1615,a197,a913,top])]) T@std/core/types/(++) [(unix:206,[a1615,a197,a913,top])])
Not in:
Next (fromList [CEval DefNonRec // Append two strings
pub fun (++) : (x : string, y : string) -> string; EndKAddr T@std/core/types/(++) [top]@[]])
New:
N (CApply AI@(238:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) AI@(206:[delim]@[(unix:206,[a1615,a197,a913,top])]) T@std/core/types/(++) [(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:239 0 local-get(buf, iev@671),AppParam unix:240 1 s], resolvedArgs = [], parent = AppParam unix:235 1 @open((++))((local-get(buf, iev@671)), s)}
Evaluating: local-get(buf, iev@671) unix:239:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: local-get unix:245:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: local-get unix:248:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(248:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with std/core/types/local-get
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:246 0 buf,AppParam unix:247 1 iev@671], resolvedArgs = [], parent = AppParam unix:239 0 local-get(buf, iev@671)}
Evaluating: buf unix:246:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:247 1 iev@671], resolvedArgs = [BI@(248:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:239 0 local-get(buf, iev@671)}
Evaluating: iev@671 unix:247:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(248:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),B@(buf:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:239 0 local-get(buf, iev@671)}
LocalGet: std/core/types/local-get std/core/types/local-get
B@(buf:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:240 1 s], resolvedArgs = [T@std/core/types/(++)], parent = AppParam unix:235 1 @open((++))((local-get(buf, iev@671)), s)}
Evaluating: s unix:240:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/types/(++),B@(buf:[delim]@[(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:235 1 @open((++))((local-get(buf, iev@671)), s)}
Extending store: B@(x:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> ""
Extending store: B@(y:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> "root"
Evaluating: @open((@extern-x++))(x, y) types:1623:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: (@extern-x++) types:1628:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(1628:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with std/core/types/(@extern-x++)
Applying FApp {totalArgs = 2, leftArgs = [AppParam types:1625 0 x,AppParam types:1626 1 y], resolvedArgs = [], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Evaluating: x types:1625:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam types:1626 1 y], resolvedArgs = [BI@(1628:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Evaluating: y types:1626:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1628:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),B@(x:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Extending store: BI@(1623:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> "root"
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(236:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),B@(buf:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [fd,s] local-set(buf, (@open((++))((local-get(buf, iev@671)), s)))}
LocalSet: std/core/types/local-set std/core/types/local-set
[string -> "",string -> "root"]
[B@(buf:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),BI@(1623:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])]
Extending store: B@(buf:[a232,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> "root"
Rebinding: fromList [action1,iev@671,iev@720] from [delim]@[(unix:206,[a1615,a197,a913,top])] to [a232,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action1:[a232,delim]@[(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
})
Extending store: B@(iev@671:[a232,delim]@[(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(iev@720:[a232,delim]@[(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: BI@(232:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with Unit
Applying FResume {label = analysis/benchmarks/handlers/unix/bio, vaddr = IL@(163:write:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), rHnd = Handler {ops = B@(hnd:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]), ret = Just AppParam unix:218 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action1,buf,iev@671,iev@720])}, rCtx = unix:232}
Applying resume continuation unix:232 analysis/benchmarks/handlers/unix/bio
Rebinding: fromList [action1,buf,iev@671,iev@720] from [a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])] to [a232,a215,a212,delim]@[(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action1:[a232,a215,a212,delim]@[(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
})
Extending store: B@(buf:[a232,a215,a212,delim]@[(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with string -> ""
Extending store: B@(iev@671:[a232,a215,a212,delim]@[(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(iev@720:[a232,a215,a212,delim]@[(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Applying FHLink {linkEff = user, doCtx = unix:163, hCtx = unix:893, linkKnext = IL@(163:write:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), linkHnd = Handler {ops = BI@(834:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), ret = Nothing, henv = BEnv (fromList [action6,iev@2567,user])}}
Rebinding: fromList [action6,iev@2567,user] from [a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a893,delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a893,delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(iev@2567:[a893,delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(user:[a893,delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with Alice
Applying FHLink {linkEff = analysis/benchmarks/handlers/unix/whoami, doCtx = unix:163, hCtx = unix:857, linkKnext = IL@(163:write:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), linkHnd = Handler {ops = B@(hnd:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), ret = Just AppParam unix:843 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,iev@2567,user])}}
Rebinding: fromList [action6,iev@2567,user] from [a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(iev@2567:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(user:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Applying FHLink {linkEff = analysis/benchmarks/handlers/unix/su, doCtx = unix:163, hCtx = unix:893, linkKnext = AI@(163:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), linkHnd = Handler {ops = B@(hnd:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), ret = Just AppParam unix:879 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,user])}}
Rebinding: fromList [action6,user] from [a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(user:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Applying FDollar {vaddr = B@(ret:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])}
Extending store: B@(@res:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with Unit
Evaluating: @res unix:900:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FDollar {vaddr = B@(ret:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])}
Extending store: B@(@res:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with Unit
Evaluating: @res unix:870:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:258 1 local-get(buf, iev@720)], resolvedArgs = [BI@(259:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [] Tuple2(((fn(){
    @mask-builtin((fn(){
      (action1());
    }));
  })()), (local-get(buf, iev@720)))}
Rebinding: fromList [buf,iev@720] from [delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(buf:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with string -> ""
Extending store: B@(iev@720:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Evaluating: local-get(buf, iev@720) unix:258:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: local-get unix:268:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: local-get unix:271:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: BI@(271:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/types/local-get
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:269 0 buf,AppParam unix:270 1 iev@720], resolvedArgs = [], parent = AppParam unix:258 1 local-get(buf, iev@720)}
Evaluating: buf unix:269:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:270 1 iev@720], resolvedArgs = [BI@(271:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:258 1 local-get(buf, iev@720)}
Evaluating: iev@720 unix:270:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(271:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]),B@(buf:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:258 1 local-get(buf, iev@720)}
LocalGet: std/core/types/local-get std/core/types/local-get
B@(buf:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])])
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(259:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]),B@(@res:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [] Tuple2(((fn(){
    @mask-builtin((fn(){
      (action1());
    }));
  })()), (local-get(buf, iev@720)))}
Extending store: CI@(fst 255:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with Unit
Extending store: CI@(snd 255:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with string -> "root"
Extending store: BI@(255:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/types/Tuple2([(fst,CI@(fst 255:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])])),(snd,CI@(snd 255:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]))])
Applying FDollar {vaddr = B@(ret:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])}
Extending store: B@(@res:[a232,a215,a212,delim]@[(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with std/core/types/Tuple2([(fst,CI@(fst 255:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])])),(snd,CI@(snd 255:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]))])
Evaluating: @res unix:252:[a232,a215,a212,delim]@[(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: EndVAddr with std/core/types/Tuple2([(fst,CI@(fst 255:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])])),(snd,CI@(snd 255:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]))])
Extending store: B@(user:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with Alice
New result at VStore B@(user:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])])
SV Alice
Not in:
SValue  constrs: (AppParam unix:919 0 Root,[]) lit: ⊥,⊥,⊥,⊥
New:
SV Alice
Applying FHLink {linkEff = analysis/benchmarks/handlers/unix/su, doCtx = unix:514, hCtx = unix:893, linkKnext = AI@(514:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), linkHnd = Handler {ops = B@(hnd:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), ret = Just AppParam unix:879 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,user])}}
Rebinding: fromList [action6,user] from [a893,a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action6:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  val _ : ()
        = @open(su)(Alice);
  @open(echo)((@open(whoami)()));
})
Extending store: B@(user:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with Root
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/echo], parent = LetBody @open(echo)((@open(whoami)()))}
Extending store: B@(s:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with string -> "alice"
New result at VStore B@(s:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
SV string -> "alice"
Not in:
SValue  lit: ⊥,⊥,⊥,"root"
New:
SV string -> top
Extending store: B@(s:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]) with string -> top
New result at VStore B@(s:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])
SV string -> top
Not in:
SValue  lit: ⊥,⊥,⊥,"root"
New:
SV string -> top
Extending store: B@(s:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> top
New result at VStore B@(s:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])
SV string -> top
Not in:
SValue  lit: ⊥,⊥,⊥,"root"
New:
SV string -> top
Extending store: B@(y:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> top
New result at VStore B@(y:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])
SV string -> top
Not in:
SValue  lit: ⊥,⊥,⊥,"root"
New:
SV string -> top
Extending store: BI@(1623:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> top
New result at VStore BI@(1623:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])
SV string -> top
Not in:
SValue  lit: ⊥,⊥,⊥,"root"
New:
SV string -> top
Extending store: B@(buf:[a232,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> top
New result at VStore B@(buf:[a232,delim]@[(unix:206,[a1615,a197,a913,top])])
SV string -> top
Not in:
SValue  lit: ⊥,⊥,⊥,"root"
New:
SV string -> top
Extending store: CI@(snd 255:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]) with string -> top
New result at VStore CI@(snd 255:[delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])])
SV string -> top
Not in:
SValue  lit: ⊥,⊥,⊥,"root"
New:
SV string -> top
Extending store: B@(action1:[a232,delim]@[(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
})
Extending store: B@(iev@671:[a232,delim]@[(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(iev@720:[a232,delim]@[(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
LocalSet: std/core/types/local-set std/core/types/local-set
[string -> "",string -> top]
[B@(buf:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),BI@(1623:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])]
Extending store: B@(buf:[a232,delim]@[(unix:206,[a1615,a197,a913,top])]) with string -> top
Rebinding: fromList [action1,iev@671,iev@720] from [delim]@[(unix:206,[a1615,a197,a913,top])] to [a232,delim]@[(unix:206,[a1615,a197,a913,top])]
Extending store: B@(action1:[a232,delim]@[(unix:206,[a1615,a197,a913,top])]) with AppParam(fn(){
  session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    }));
})
Extending store: B@(iev@671:[a232,delim]@[(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: B@(iev@720:[a232,delim]@[(unix:206,[a1615,a197,a913,top])]) with @Hnodiv
Extending store: BI@(232:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]) with Unit
Evaluating: Tuple2(0, "hi root, and hi alice") unix:945:[top]@[]
Evaluating: Tuple2 unix:946:[top]@[]
Evaluating: Tuple2 unix:949:[top]@[]
Extending store: BI@(949:[top]@[]) with Tuple2
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:947 0 0,AppParam unix:948 1 "hi root, and hi alice"], resolvedArgs = [], parent = LamBody [] Tuple2(0, "hi root, and hi alice")}
Evaluating: 0 unix:947:[top]@[]
Extending store: BI@(947:[top]@[]) with int -> 0
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:948 1 "hi root, and hi alice"], resolvedArgs = [BI@(949:[top]@[])], parent = LamBody [] Tuple2(0, "hi root, and hi alice")}
Evaluating: "hi root, and hi alice" unix:948:[top]@[]
Extending store: BI@(948:[top]@[]) with string -> "hi root, and hi alice"
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(949:[top]@[]),BI@(947:[top]@[])], parent = LamBody [] Tuple2(0, "hi root, and hi alice")}
Extending store: CI@(fst 945:[top]@[]) with int -> 0
Extending store: CI@(snd 945:[top]@[]) with string -> "hi root, and hi alice"
Extending store: BI@(945:[top]@[]) with std/core/types/Tuple2([(fst,CI@(fst 945:[top]@[])),(snd,CI@(snd 945:[top]@[]))])
Extending store: EndVAddr with std/core/types/Tuple2([(fst,CI@(fst 945:[top]@[])),(snd,CI@(snd 945:[top]@[]))])
d=10,m=10
Result 0 / 1
Result 0.0%, time: 0.081589s
