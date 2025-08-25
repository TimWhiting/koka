koka-3.2.2: unregistering (local file changes: src/Core/FlowAnalysis/Full/DMCFAR/Syntax.hs)
koka> build (lib + exe) with ghc-9.6.6
Preprocessing library for koka-3.2.2..
Building library for koka-3.2.2..
[126 of 143] Compiling Core.FlowAnalysis.Full.DMCFAR.Syntax [Source file changed]
[140 of 143] Compiling Compile.Build [Core.FlowAnalysis.Full.DMCFAR.Syntax changed]
Warning: The following header files listed in the main library's c-sources
will not be used: src/Platform/cpp/Platform/cconsole.h.
Header files should be in the 'include' or 'install-include' stanza.
See https://cabal.readthedocs.io/en/3.10/cabal-package.html#pkg-field-includes
Preprocessing executable 'koka' for koka-3.2.2..
Building executable 'koka' for koka-3.2.2..
[18 of 18] Linking .stack-work/dist/x86_64-linux/ghc-9.6.6/build/koka/koka [Library changed]
koka> copy/register
Installing library in /home/tim/koka/.stack-work/install/x86_64-linux/caa2c2a0c9eec164a22324b7d83105503be009c866f84849897f47c50a8aa47d/9.6.6/lib/x86_64-linux-ghc-9.6.6/koka-3.2.2-8GBEfjISoFBMgz1sr3wgW
Installing executable koka in /home/tim/koka/.stack-work/install/x86_64-linux/caa2c2a0c9eec164a22324b7d83105503be009c866f84849897f47c50a8aa47d/9.6.6/bin
Registering library for koka-3.2.2..
Evaluating: bio((fn(){
  val _ : ()
        = (@open(echo)("hi "));
  (@open(echo)("unix world"));
})) in BEnv (fromList []):[top]@[]
Evaluating: bio in BEnv (fromList []):[top]@[]
Evaluating: bio in BEnv (fromList []):[top]@[]
Evaluating: forall<a,e> fn(action){
  local-scope((forall<h> fn(){
    val iev@681 : hdiv<h,string,e>;
    val iev@734 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
    local-var("", (fn(buf){
        ((fn(@action){
          bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
                (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
              }))))), (fn(@res){
              @res;
            }), @action);
        })((fn(){
          (Tuple2(((fn(){
              @mask-builtin((fn(){
                (action());
              }));
            })()), (@open(print-return)((local-get(buf, iev@734))))));
        })));
      }));
  }));
} in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:393 0 fn(){
  val _ : ()
        = @open(echo)("hi ");
  @open(echo)("unix world");
}], resolvedArgs = [], parent = LamBody [] bio((fn(){
  val _ : ()
        = (@open(echo)("hi "));
  (@open(echo)("unix world"));
}))}
Evaluating: fn(){
  val _ : ()
        = @open(echo)("hi ");
  @open(echo)("unix world");
} in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/bio], parent = LamBody [] bio((fn(){
  val _ : ()
        = (@open(echo)("hi "));
  (@open(echo)("unix world"));
}))}
Evaluating: local-scope((forall<h> fn(){
  val iev@681 : hdiv<h,string,e>;
  val iev@734 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action());
            }));
          })()), (@open(print-return)((local-get(buf, iev@734))))));
      })));
    }));
})) in BEnv (fromList [action]):[a391,top]@[]
Evaluating: local-scope in BEnv (fromList [action]):[a391,top]@[]
Evaluating: local-scope in BEnv (fromList [action]):[a391,top]@[]
Evaluating: forall<a,e> fn(action){
  @open(unsafe-no-local-cast)((forall<h> action))();
} in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:219 0 forall<h> fn(){
  val iev@681 : hdiv<h,string,e>;
  val iev@734 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action());
            }));
          })()), (@open(print-return)((local-get(buf, iev@734))))));
      })));
    }));
}], resolvedArgs = [], parent = LamBody [action] local-scope((forall<h> fn(){
  val iev@681 : hdiv<h,string,e>;
  val iev@734 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action());
            }));
          })()), (@open(print-return)((local-get(buf, iev@734))))));
      })));
    }));
}))}
Evaluating: forall<h> fn(){
  val iev@681 : hdiv<h,string,e>;
  val iev@734 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action());
            }));
          })()), (@open(print-return)((local-get(buf, iev@734))))));
      })));
    }));
} in BEnv (fromList [action]):[a391,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@std/core/types/local-scope], parent = LamBody [action] local-scope((forall<h> fn(){
  val iev@681 : hdiv<h,string,e>;
  val iev@734 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
  local-var("", (fn(buf){
      ((fn(@action){
        bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
              (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (Tuple2(((fn(){
            @mask-builtin((fn(){
              (action());
            }));
          })()), (@open(print-return)((local-get(buf, iev@734))))));
      })));
    }));
}))}
Evaluating: @open(unsafe-no-local-cast)((forall<h> action))() in BEnv (fromList [action]):[a217,a391,top]@[]
Evaluating: @open(unsafe-no-local-cast)((forall<h> action)) in BEnv (fromList [action]):[a217,a391,top]@[]
Evaluating: unsafe-no-local-cast in BEnv (fromList [action]):[a217,a391,top]@[]
Evaluating: unsafe-no-local-cast in BEnv (fromList [action]):[a217,a391,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam types:1776 0 forall<h> action], resolvedArgs = [], parent = AppLambda @open(unsafe-no-local-cast)((forall<h> action))}
Evaluating: forall<h> action in BEnv (fromList [action]):[a217,a391,top]@[]
Evaluating: action in BEnv (fromList [action]):[a217,a391,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(1779:[a217,a391,top]@[])], parent = AppLambda @open(unsafe-no-local-cast)((forall<h> action))}
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [action] @open(unsafe-no-local-cast)((forall<h> action))()}
Evaluating: val iev@681 : hdiv<h,string,e>;
val iev@734 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action());
          }));
        })()), (@open(print-return)((local-get(buf, iev@734))))));
    })));
  })) in BEnv (fromList [action]):[a1773,a217,a391,top]@[]
Evaluating: @Hnodiv in BEnv (fromList [action]):[a1773,a217,a391,top]@[]
Evaluating: @Hnodiv in BEnv (fromList [action]):[a1773,a217,a391,top]@[]
Applying FLet {groupIdx = 0, numGroups = 2, bindingIdx = 0, numBindings = 1, name = iev@681, resolved = [], parent = LamBody [] val iev@681 : hdiv<h,string,e>;
val iev@734 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action());
          }));
        })()), (@open(print-return)((local-get(buf, iev@734))))));
    })));
  }))}
Applying FLet {groupIdx = 1, numGroups = 2, bindingIdx = 0, numBindings = 1, name = iev@734, resolved = [], parent = LamBody [] val iev@681 : hdiv<h,string,e>;
val iev@734 : hdiv<h,string,<analysis/benchmarks/handlers/unix/bio|e>>;
local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action());
          }));
        })()), (@open(print-return)((local-get(buf, iev@734))))));
    })));
  }))}
Evaluating: local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action());
          }));
        })()), (@open(print-return)((local-get(buf, iev@734))))));
    })));
  })) in BEnv (fromList [action,iev@681,iev@734]):[a1773,a217,a391,top]@[]
Evaluating: local-var in BEnv (fromList [action,iev@681,iev@734]):[a1773,a217,a391,top]@[]
Evaluating: local-var in BEnv (fromList [action,iev@681,iev@734]):[a1773,a217,a391,top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:228 0 "",AppParam unix:229 1 fn(buf){
  (fn(@action){
    bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
          (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (Tuple2(((fn(){
        @mask-builtin((fn(){
          (action());
        }));
      })()), (@open(print-return)((local-get(buf, iev@734))))));
  }));
}], resolvedArgs = [], parent = LetBody local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action());
          }));
        })()), (@open(print-return)((local-get(buf, iev@734))))));
    })));
  }))}
Evaluating: "" in BEnv (fromList [action,iev@681,iev@734]):[a1773,a217,a391,top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:229 1 fn(buf){
  (fn(@action){
    bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
          (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (Tuple2(((fn(){
        @mask-builtin((fn(){
          (action());
        }));
      })()), (@open(print-return)((local-get(buf, iev@734))))));
  }));
}], resolvedArgs = [BI@(230:[a1773,a217,a391,top]@[])], parent = LetBody local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action());
          }));
        })()), (@open(print-return)((local-get(buf, iev@734))))));
    })));
  }))}
Evaluating: fn(buf){
  (fn(@action){
    bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
          (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (Tuple2(((fn(){
        @mask-builtin((fn(){
          (action());
        }));
      })()), (@open(print-return)((local-get(buf, iev@734))))));
  }));
} in BEnv (fromList [action,iev@681,iev@734]):[a1773,a217,a391,top]@[]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(230:[a1773,a217,a391,top]@[]),BI@(228:[a1773,a217,a391,top]@[])], parent = LetBody local-var("", (fn(buf){
    ((fn(@action){
      bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
            (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (Tuple2(((fn(){
          @mask-builtin((fn(){
            (action());
          }));
        })()), (@open(print-return)((local-get(buf, iev@734))))));
    })));
  }))}
LocalVar: std/core/hnd/local-var std/core/hnd/local-var
Evaluating: (fn(@action){
  bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
        (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (Tuple2(((fn(){
      @mask-builtin((fn(){
        (action());
      }));
    })()), (@open(print-return)((local-get(buf, iev@734))))));
})) in BEnv (fromList [action,buf,iev@681,iev@734]):[delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: fn(@action){
  bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
        (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
      }))))), (fn(@res){
      @res;
    }), @action);
} in BEnv (fromList [action,buf,iev@681,iev@734]):[delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:234 0 fn(){
  Tuple2(((fn(){
      @mask-builtin((fn(){
        (action());
      }));
    })()), (@open(print-return)((local-get(buf, iev@734)))));
}], resolvedArgs = [], parent = LamBody [buf] (fn(@action){
  bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
        (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (Tuple2(((fn(){
      @mask-builtin((fn(){
        (action());
      }));
    })()), (@open(print-return)((local-get(buf, iev@734))))));
}))}
Evaluating: fn(){
  Tuple2(((fn(){
      @mask-builtin((fn(){
        (action());
      }));
    })()), (@open(print-return)((local-get(buf, iev@734)))));
} in BEnv (fromList [action,buf,iev@681,iev@734]):[delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(233:[delim]@[(unix:226,[a1773,a217,a391,top])])], parent = LamBody [buf] (fn(@action){
  bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
        (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (Tuple2(((fn(){
      @mask-builtin((fn(){
        (action());
      }));
    })()), (@open(print-return)((local-get(buf, iev@734))))));
}))}
Evaluating: bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
      (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
    }))))), (fn(@res){
    @res;
  }), @action) in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: bio/@handle in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: bio/@handle in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(bio/@tag, hnd, ret, action);
} in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:237 0 @Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
    (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
  })))),AppParam unix:238 1 fn(@res){
  @res;
},AppParam unix:239 2 @action], resolvedArgs = [], parent = LamBody [@action] bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
      (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
    (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
  })))) in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: @Hnd-bio in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: @Hnd-bio in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:242 0 1,AppParam unix:243 1 @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
}))], resolvedArgs = [], parent = AppParam unix:237 0 @Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
    (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
  }))))}
Evaluating: 1 in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:243 1 @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
}))], resolvedArgs = [BI@(244:[a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:237 0 @Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
    (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
  }))))}
Evaluating: @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
})) in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: clause-tail2 in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: clause-tail2 in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:247 0 fn(fd, s){
  local-set(buf, (@open((++))((local-get(buf, iev@681)), s)));
}], resolvedArgs = [], parent = AppParam unix:243 1 @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
}))}
Evaluating: fn(fd, s){
  local-set(buf, (@open((++))((local-get(buf, iev@681)), s)));
} in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(251:[a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:243 1 @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
}))}
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(244:[a232,delim]@[(unix:226,[a1773,a217,a391,top])]),BI@(242:[a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:237 0 @Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
    (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
  }))))}
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:238 1 fn(@res){
  @res;
},AppParam unix:239 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#bio/@handle], parent = LamBody [@action] bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
      (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:239 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#bio/@handle,BI@(237:[a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = LamBody [@action] bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
      (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action in BEnv (fromList [@action,buf,iev@681]):[a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#bio/@handle,BI@(237:[a232,delim]@[(unix:226,[a1773,a217,a391,top])]),BI@(238:[a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = LamBody [@action] bio/@handle((@Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
      (local-set(buf, (@open((++))((local-get(buf, iev@681)), s))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @hhandle(bio/@tag, hnd, ret, action) in BEnv (fromList [action,hnd,ret]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: @hhandle in BEnv (fromList [action,hnd,ret]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:152 0 bio/@tag,AppParam unix:153 1 hnd,AppParam unix:154 2 ret,AppParam unix:155 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
Evaluating: bio/@tag in BEnv (fromList [action,hnd,ret]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: @open(@new-htag)("bio@unix") in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Evaluating: @new-htag in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:144 0 "bio@unix"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:bio`
pub val bio/@tag : hnd/htag<analysis/benchmarks/handlers/unix/bio>;}
Evaluating: "bio@unix" in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(148:[top]@[])], parent = DefNonRec // runtime tag for the effect `:bio`
pub val bio/@tag : hnd/htag<analysis/benchmarks/handlers/unix/bio>;}
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:153 1 hnd,AppParam unix:154 2 ret,AppParam unix:155 3 action], resolvedArgs = [BI@(156:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
Evaluating: hnd in BEnv (fromList [action,hnd,ret]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:154 2 ret,AppParam unix:155 3 action], resolvedArgs = [BI@(156:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]),T@analysis/benchmarks/handlers/unix/#bio/@tag], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
Evaluating: ret in BEnv (fromList [action,hnd,ret]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:155 3 action], resolvedArgs = [BI@(156:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]),T@analysis/benchmarks/handlers/unix/#bio/@tag,B@(hnd:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
Evaluating: action in BEnv (fromList [action,hnd,ret]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(156:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]),T@analysis/benchmarks/handlers/unix/#bio/@tag,B@(hnd:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]),B@(ret:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
OPS analysis/benchmarks/handlers/unix/bio fvs: BEnv (fromList [buf,iev@681]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])] unix:150
Evaluating: Tuple2(((fn(){
    @mask-builtin((fn(){
      (action());
    }));
  })()), (@open(print-return)((local-get(buf, iev@734))))) in BEnv (fromList [action,buf,iev@734]):[delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: Tuple2 in BEnv (fromList [action,buf,iev@734]):[delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: Tuple2 in BEnv (fromList [action,buf,iev@734]):[delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:277 0 (fn(){
  @mask-builtin((fn(){
    (action());
  }));
})(),AppParam unix:278 1 @open(print-return)((local-get(buf, iev@734)))], resolvedArgs = [], parent = LamBody [] Tuple2(((fn(){
    @mask-builtin((fn(){
      (action());
    }));
  })()), (@open(print-return)((local-get(buf, iev@734)))))}
Evaluating: (fn(){
  @mask-builtin((fn(){
    (action());
  }));
})() in BEnv (fromList [action,buf,iev@734]):[delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: fn(){
  @mask-builtin((fn(){
    (action());
  }));
} in BEnv (fromList [action,buf,iev@734]):[delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = AppParam unix:277 0 (fn(){
  @mask-builtin((fn(){
    (action());
  }));
})()}
Evaluating: @mask-builtin((fn(){
  (action());
})) in BEnv (fromList [action]):[a277,delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: fn(){
  action();
} in BEnv (fromList [action]):[a277,delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Applying FMask
Evaluating: action() in BEnv (fromList [action]):[a277,delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: action in BEnv (fromList [action]):[a277,delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [] action()}
Evaluating: val _ : ()
      = @open(echo)("hi ");
@open(echo)("unix world") in BEnv (fromList []):[a285,a277,delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: @open(echo)("hi ") in BEnv (fromList []):[a285,a277,delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: echo in BEnv (fromList []):[a285,a277,delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: fn(s){
  @open(write)(stdout, s);
} in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:407 0 "hi "], resolvedArgs = [], parent = LetDef val _ : ();}
Evaluating: "hi " in BEnv (fromList []):[a285,a277,delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/echo], parent = LetDef val _ : ();}
Evaluating: @open(write)(stdout, s) in BEnv (fromList [s]):[a397,a285,a277,delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: write in BEnv (fromList [s]):[a397,a285,a277,delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: fn(fd, s){
  @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s);
} in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:197 0 stdout,AppParam unix:198 1 s], resolvedArgs = [], parent = LamBody [s] @open(write)(stdout, s)}
Evaluating: stdout in BEnv (fromList [s]):[a397,a285,a277,delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: 0 in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:198 1 s], resolvedArgs = [T@analysis/benchmarks/handlers/unix/write], parent = LamBody [s] @open(write)(stdout, s)}
Evaluating: s in BEnv (fromList [s]):[a397,a285,a277,delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/write,T@analysis/benchmarks/handlers/unix/stdout], parent = LamBody [s] @open(write)(stdout, s)}
Evaluating: @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s) in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: @perform2 in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: @perform2 in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:173 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam unix:174 1 forall<e,a> write/@select,AppParam unix:175 2 fd,AppParam unix:176 3 s], resolvedArgs = [], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: @evv-at in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: @evv-at in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:179 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam unix:173 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: @make-ssize_t in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:185 0 0], resolvedArgs = [], parent = AppParam unix:179 0 @open(@make-ssize_t)(0)}
Evaluating: 0 in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(187:[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:179 0 @open(@make-ssize_t)(0)}
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(183:[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:173 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:174 1 forall<e,a> write/@select,AppParam unix:175 2 fd,AppParam unix:176 3 s], resolvedArgs = [BI@(177:[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])])], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: forall<e,a> write/@select in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: write/@select in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-bio(_, (@fun-write)) : analysis/benchmarks/handlers/unix/bio<e,a> )
       -> @fun-write;
  });
} in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:175 2 fd,AppParam unix:176 3 s], resolvedArgs = [BI@(177:[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]),BI@(173:[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])])], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: fd in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:176 3 s], resolvedArgs = [BI@(177:[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]),BI@(173:[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]),T@analysis/benchmarks/handlers/unix/#write/@select], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: s in BEnv (fromList [fd,s]):[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(177:[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]),BI@(173:[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]),T@analysis/benchmarks/handlers/unix/#write/@select,B@(fd:[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])])], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: local-set(buf, (@open((++))((local-get(buf, iev@681)), s))) in BEnv (fromList [buf,iev@681,s]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: local-set in BEnv (fromList [buf,iev@681,s]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: local-set in BEnv (fromList [buf,iev@681,s]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:254 0 buf,AppParam unix:255 1 @open((++))((local-get(buf, iev@681)), s)], resolvedArgs = [], parent = LamBody [fd,s] local-set(buf, (@open((++))((local-get(buf, iev@681)), s)))}
Evaluating: buf in BEnv (fromList [buf,iev@681,s]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:255 1 @open((++))((local-get(buf, iev@681)), s)], resolvedArgs = [BI@(256:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = LamBody [fd,s] local-set(buf, (@open((++))((local-get(buf, iev@681)), s)))}
Evaluating: @open((++))((local-get(buf, iev@681)), s) in BEnv (fromList [buf,iev@681,s]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: (++) in BEnv (fromList [buf,iev@681,s]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: fn(x, y){
  @open((@extern-x++))(x, y);
} in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:259 0 local-get(buf, iev@681),AppParam unix:260 1 s], resolvedArgs = [], parent = AppParam unix:255 1 @open((++))((local-get(buf, iev@681)), s)}
Evaluating: local-get(buf, iev@681) in BEnv (fromList [buf,iev@681,s]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: local-get in BEnv (fromList [buf,iev@681,s]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: local-get in BEnv (fromList [buf,iev@681,s]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:266 0 buf,AppParam unix:267 1 iev@681], resolvedArgs = [], parent = AppParam unix:259 0 local-get(buf, iev@681)}
Evaluating: buf in BEnv (fromList [buf,iev@681,s]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:267 1 iev@681], resolvedArgs = [BI@(268:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:259 0 local-get(buf, iev@681)}
Evaluating: iev@681 in BEnv (fromList [buf,iev@681,s]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(268:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]),B@(buf:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:259 0 local-get(buf, iev@681)}
LocalGet: std/core/types/local-get std/core/types/local-get
B@(buf:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:260 1 s], resolvedArgs = [T@std/core/types/(++)], parent = AppParam unix:255 1 @open((++))((local-get(buf, iev@681)), s)}
Evaluating: s in BEnv (fromList [buf,iev@681,s]):[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/types/(++),B@(buf:[delim]@[(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:255 1 @open((++))((local-get(buf, iev@681)), s)}
Evaluating: @open((@extern-x++))(x, y) in BEnv (fromList [x,y]):[a255,a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Evaluating: (@extern-x++) in BEnv (fromList [x,y]):[a255,a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam types:1783 0 x,AppParam types:1784 1 y], resolvedArgs = [], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Evaluating: x in BEnv (fromList [x,y]):[a255,a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam types:1784 1 y], resolvedArgs = [BI@(1786:[a255,a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Evaluating: y in BEnv (fromList [x,y]):[a255,a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1786:[a255,a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]),B@(x:[a255,a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(256:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]),B@(buf:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])], parent = LamBody [fd,s] local-set(buf, (@open((++))((local-get(buf, iev@681)), s)))}
LocalSet: std/core/types/local-set std/core/types/local-set
[string -> "",string -> "hi "]
[B@(buf:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]),BI@(1781:[a255,a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])]
Applying FResume {label = analysis/benchmarks/handlers/unix/bio, vaddr = AI@(171:[a195,a397,a285,a277]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]), venv = BEnv (fromList [buf,iev@681,s]), rHnd = Handler {ops = B@(hnd:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]), ret = Just AppParam unix:238 1 fn(@res){
  @res;
}, henv = BEnv (fromList [buf,iev@681])}, rCtx = unix:252}
Applying resume continuation unix:252 analysis/benchmarks/handlers/unix/bio
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = _, resolved = [], parent = LamBody [] val _ : ()
      = @open(echo)("hi ");
@open(echo)("unix world")}
Evaluating: @open(echo)("unix world") in BEnv (fromList [_]):[a285,a277,delim]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: echo in BEnv (fromList [_]):[a285,a277,delim]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:400 0 "unix world"], resolvedArgs = [], parent = LetBody @open(echo)("unix world")}
Evaluating: "unix world" in BEnv (fromList [_]):[a285,a277,delim]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/echo], parent = LetBody @open(echo)("unix world")}
Evaluating: @open(write)(stdout, s) in BEnv (fromList [s]):[a398,a285,a277,delim]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: write in BEnv (fromList [s]):[a398,a285,a277,delim]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:197 0 stdout,AppParam unix:198 1 s], resolvedArgs = [], parent = LamBody [s] @open(write)(stdout, s)}
Evaluating: stdout in BEnv (fromList [s]):[a398,a285,a277,delim]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:198 1 s], resolvedArgs = [T@analysis/benchmarks/handlers/unix/write], parent = LamBody [s] @open(write)(stdout, s)}
Evaluating: s in BEnv (fromList [s]):[a398,a285,a277,delim]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/write,T@analysis/benchmarks/handlers/unix/stdout], parent = LamBody [s] @open(write)(stdout, s)}
Evaluating: @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s) in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: @perform2 in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: @perform2 in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:173 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam unix:174 1 forall<e,a> write/@select,AppParam unix:175 2 fd,AppParam unix:176 3 s], resolvedArgs = [], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: @evv-at in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: @evv-at in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:179 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam unix:173 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: @make-ssize_t in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:185 0 0], resolvedArgs = [], parent = AppParam unix:179 0 @open(@make-ssize_t)(0)}
Evaluating: 0 in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(187:[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:179 0 @open(@make-ssize_t)(0)}
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(183:[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:173 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:174 1 forall<e,a> write/@select,AppParam unix:175 2 fd,AppParam unix:176 3 s], resolvedArgs = [BI@(177:[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: forall<e,a> write/@select in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: write/@select in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:175 2 fd,AppParam unix:176 3 s], resolvedArgs = [BI@(177:[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]),BI@(173:[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: fd in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:176 3 s], resolvedArgs = [BI@(177:[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]),BI@(173:[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]),T@analysis/benchmarks/handlers/unix/#write/@select], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: s in BEnv (fromList [fd,s]):[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(177:[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]),BI@(173:[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]),T@analysis/benchmarks/handlers/unix/#write/@select,B@(fd:[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: local-set(buf, (@open((++))((local-get(buf, iev@681)), s))) in BEnv (fromList [buf,iev@681,s]):[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: local-set in BEnv (fromList [buf,iev@681,s]):[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: local-set in BEnv (fromList [buf,iev@681,s]):[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:254 0 buf,AppParam unix:255 1 @open((++))((local-get(buf, iev@681)), s)], resolvedArgs = [], parent = LamBody [fd,s] local-set(buf, (@open((++))((local-get(buf, iev@681)), s)))}
Evaluating: buf in BEnv (fromList [buf,iev@681,s]):[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:255 1 @open((++))((local-get(buf, iev@681)), s)], resolvedArgs = [BI@(256:[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = LamBody [fd,s] local-set(buf, (@open((++))((local-get(buf, iev@681)), s)))}
Evaluating: @open((++))((local-get(buf, iev@681)), s) in BEnv (fromList [buf,iev@681,s]):[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: (++) in BEnv (fromList [buf,iev@681,s]):[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:259 0 local-get(buf, iev@681),AppParam unix:260 1 s], resolvedArgs = [], parent = AppParam unix:255 1 @open((++))((local-get(buf, iev@681)), s)}
Evaluating: local-get(buf, iev@681) in BEnv (fromList [buf,iev@681,s]):[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: local-get in BEnv (fromList [buf,iev@681,s]):[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: local-get in BEnv (fromList [buf,iev@681,s]):[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:266 0 buf,AppParam unix:267 1 iev@681], resolvedArgs = [], parent = AppParam unix:259 0 local-get(buf, iev@681)}
Evaluating: buf in BEnv (fromList [buf,iev@681,s]):[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:267 1 iev@681], resolvedArgs = [BI@(268:[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:259 0 local-get(buf, iev@681)}
Evaluating: iev@681 in BEnv (fromList [buf,iev@681,s]):[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(268:[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]),B@(buf:[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:259 0 local-get(buf, iev@681)}
LocalGet: std/core/types/local-get std/core/types/local-get
B@(buf:[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:260 1 s], resolvedArgs = [T@std/core/types/(++)], parent = AppParam unix:255 1 @open((++))((local-get(buf, iev@681)), s)}
Evaluating: s in BEnv (fromList [buf,iev@681,s]):[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/types/(++),B@(buf:[delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:255 1 @open((++))((local-get(buf, iev@681)), s)}
Evaluating: @open((@extern-x++))(x, y) in BEnv (fromList [x,y]):[a255,a252,a235,a232]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: (@extern-x++) in BEnv (fromList [x,y]):[a255,a252,a235,a232]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam types:1783 0 x,AppParam types:1784 1 y], resolvedArgs = [], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Evaluating: x in BEnv (fromList [x,y]):[a255,a252,a235,a232]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam types:1784 1 y], resolvedArgs = [BI@(1786:[a255,a252,a235,a232]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Evaluating: y in BEnv (fromList [x,y]):[a255,a252,a235,a232]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1786:[a255,a252,a235,a232]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]),B@(x:[a255,a252,a235,a232]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(256:[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]),B@(buf:[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = LamBody [fd,s] local-set(buf, (@open((++))((local-get(buf, iev@681)), s)))}
LocalSet: std/core/types/local-set std/core/types/local-set
[string -> "",string -> top]
[B@(buf:[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]),BI@(1781:[a255,a252,a235,a232]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])]
Applying FResume {label = analysis/benchmarks/handlers/unix/bio, vaddr = AI@(171:[a195,a398,a285,a277]@[(unix:252,[a252,a235,a232,delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]), venv = BEnv (fromList [buf,iev@681,s]), rHnd = Handler {ops = B@(hnd:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]), ret = Just AppParam unix:238 1 fn(@res){
  @res;
}, henv = BEnv (fromList [buf,iev@681])}, rCtx = unix:252}
Applying resume continuation unix:252 analysis/benchmarks/handlers/unix/bio
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:278 1 @open(print-return)((local-get(buf, iev@734)))], resolvedArgs = [BI@(279:[delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])])], parent = LamBody [] Tuple2(((fn(){
    @mask-builtin((fn(){
      (action());
    }));
  })()), (@open(print-return)((local-get(buf, iev@734)))))}
Evaluating: @open(print-return)((local-get(buf, iev@734))) in BEnv (fromList [action,buf,iev@734]):[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: print-return in BEnv (fromList [action,buf,iev@734]):[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: fn(s){
  val _ : ()
        = @open(trace)(s);
  s;
} in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:289 0 local-get(buf, iev@734)], resolvedArgs = [], parent = AppParam unix:278 1 @open(print-return)((local-get(buf, iev@734)))}
Evaluating: local-get(buf, iev@734) in BEnv (fromList [action,buf,iev@734]):[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: local-get in BEnv (fromList [action,buf,iev@734]):[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: local-get in BEnv (fromList [action,buf,iev@734]):[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:295 0 buf,AppParam unix:296 1 iev@734], resolvedArgs = [], parent = AppParam unix:289 0 local-get(buf, iev@734)}
Evaluating: buf in BEnv (fromList [action,buf,iev@734]):[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:296 1 iev@734], resolvedArgs = [BI@(297:[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:289 0 local-get(buf, iev@734)}
Evaluating: iev@734 in BEnv (fromList [action,buf,iev@734]):[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(297:[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]),B@(buf:[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = AppParam unix:289 0 local-get(buf, iev@734)}
LocalGet: std/core/types/local-get std/core/types/local-get
B@(buf:[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])
Applying FHLink {linkEff = analysis/benchmarks/handlers/unix/bio, doCtx = unix:289, hCtx = unix:252, linkKnext = AI@(289:[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]), linkHnd = Handler {ops = B@(hnd:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])]), ret = Just AppParam unix:238 1 fn(@res){
  @res;
}, henv = BEnv (fromList [buf,iev@681])}}
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/print-return], parent = AppParam unix:278 1 @open(print-return)((local-get(buf, iev@734)))}
Evaluating: val _ : ()
      = @open(trace)(s);
s in BEnv (fromList [s]):[a278,delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: @open(trace)(s) in BEnv (fromList [s]):[a278,delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Evaluating: trace in BEnv (fromList [s]):[a278,delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:211 0 s], resolvedArgs = [], parent = LetDef val _ : ();}
Evaluating: s in BEnv (fromList [s]):[a278,delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(213:[a278,delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = LetDef val _ : ();}
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = _, resolved = [], parent = LamBody [s] val _ : ()
      = @open(trace)(s);
s}
Evaluating: s in BEnv (fromList [_,s]):[a278,delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(279:[delim]@[(unix:150,[a235,a232,delim]),(unix:226,[a1773,a217,a391,top])]),BI@(252:[a252,a235,a232,delim]@[(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])], parent = LamBody [] Tuple2(((fn(){
    @mask-builtin((fn(){
      (action());
    }));
  })()), (@open(print-return)((local-get(buf, iev@734)))))}
Applying FDollar {vaddr = B@(ret:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])}
Evaluating: @res in BEnv (fromList [@res]):[a235,a232,delim]@[(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FDollar {vaddr = B@(ret:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])}
Evaluating: @res in BEnv (fromList [@res]):[a235,a232,delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]
Applying FDollar {vaddr = B@(ret:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])}
Applying FDollar {vaddr = B@(ret:[a235,a232,delim]@[(unix:226,[a1773,a217,a391,top])])}
Evaluating: @Hnodiv in BEnv (fromList [action,iev@681]):[a1773,a217,a391,top]@[]
Evaluating: @Hnodiv in BEnv (fromList [action,iev@681]):[a1773,a217,a391,top]@[]
result': ( objs: ["(std/core/types/Tuple2,[(fst,CI@(fst 275:[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])])),(snd,CI@(snd 275:[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]))])"] lit: ⊥,⊥,⊥,⊥,fromList [(CI@(fst 275:[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]), constrs: (Primitive std/core/types/Unit,[]) lit: ⊥,⊥,⊥,⊥),(CI@(snd 275:[delim]@[(unix:252,[a252,a252,a235,a232]),(unix:252,[delim]),(unix:252,[delim]),(unix:226,[a1773,a217,a391,top])]), lit: ⊥,⊥,⊥,⊤)])
Evaluating: Tuple2(Unit, "hi unix world") in BEnv (fromList []):[top]@[]
Evaluating: Tuple2 in BEnv (fromList []):[top]@[]
Evaluating: Tuple2 in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:415 0 Unit,AppParam unix:416 1 "hi unix world"], resolvedArgs = [], parent = LamBody [] Tuple2(Unit, "hi unix world")}
Evaluating: Unit in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:416 1 "hi unix world"], resolvedArgs = [BI@(417:[top]@[])], parent = LamBody [] Tuple2(Unit, "hi unix world")}
Evaluating: "hi unix world" in BEnv (fromList []):[top]@[]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(417:[top]@[]),BI@(415:[top]@[])], parent = LamBody [] Tuple2(Unit, "hi unix world")}
expected': ( objs: ["(std/core/types/Tuple2,[(fst,CI@(fst 413:[top]@[])),(snd,CI@(snd 413:[top]@[]))])"] lit: ⊥,⊥,⊥,⊥,fromList [(CI@(fst 413:[top]@[]), constrs: (AppParam unix:415 0 Unit,[]) lit: ⊥,⊥,⊥,⊥),(CI@(snd 413:[top]@[]), lit: ⊥,⊥,⊥,"hi unix world")])
d=4,m=4
Result 0 / 1
Result 0.0%, time: 0.103349842s
