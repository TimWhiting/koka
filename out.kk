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
                    (resume(a));
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
})) benchmarks:186:[top]@[]
Evaluating: @open(trace)("Example get/set") benchmarks:188:[top]@[]
Evaluating: trace benchmarks:303:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:301 0 "Example get/set"], resolvedArgs = [], parent = LetDef val _ : ();}
Evaluating: "Example get/set" benchmarks:301:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(303:[top]@[])], parent = LetDef val _ : ();}
Applying: [] [BI@(303:[top]@[]),BI@(301:[top]@[])]
Applying function: BI@(303:[top]@[]) std/core/debug/trace
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = _, resolved = [], parent = LamBody [] val _ : ()
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
                    (resume(a));
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
}))}
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
                    (resume(a));
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
})) benchmarks:189:[top]@[]
Evaluating: 2 benchmarks:191:[top]@[]
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = x, resolved = [], parent = LetBody val x : int
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
                    (resume(a));
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
}))}
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
                    (resume(a));
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
})) benchmarks:192:[top]@[]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
        (resume(x));
      }))))), (fn(@res){
      @res;
    }), @action);
} benchmarks:193:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:194 0 fn(){
  (fn(@action){
    set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
          ((fn(@override-action){
            (fn(@action){
              get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                    (resume(a));
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
}], resolvedArgs = [], parent = LetBody (fn(@action){
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
                    (resume(a));
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
}))}
Evaluating: fn(){
  (fn(@action){
    set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
          ((fn(@override-action){
            (fn(@action){
              get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                    (resume(a));
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
} benchmarks:194:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(193:[top]@[])], parent = LetBody (fn(@action){
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
                    (resume(a));
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
}))}
Applying: [] [BI@(193:[top]@[]),BI@(194:[top]@[])]
Applying function: BI@(193:[top]@[]) AppLambda(fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
        (resume(x));
      }))))), (fn(@res){
      @res;
    }), @action);
})
Applying closure: AppLambda fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
        (resume(x));
      }))))), (fn(@res){
      @res;
    }), @action);
}:[a192,top]@[] fvs: fromList [x] args [@action]
AppParam(fn(){
  (fn(@action){
    set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
          ((fn(@override-action){
            (fn(@action){
              get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                    (resume(a));
                  }))))), (fn(@res){
                  @res;
                }), @action);
            })((fn(){
              (@mask-at((@evv-index(get/@tag)), True, @override-action));
            }));
          })((fn(){
            () from BI@(194:[top]@[]) rebinding to B@(@action:[a192,top]@[])
Rebinding: fromList [x] from [top]@[] to [a192,top]@[]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
      (resume(x));
    }))))), (fn(@res){
    @res;
  }), @action) benchmarks:195:[a192,top]@[]
Evaluating: get/@handle benchmarks:196:[a192,top]@[]
Evaluating: get/@handle benchmarks:200:[a192,top]@[]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(get/@tag, hnd, ret, action);
} benchmarks:7:[top]@[]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:197 0 @Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
    (resume(x));
  })))),AppParam benchmarks:198 1 fn(@res){
  @res;
},AppParam benchmarks:199 2 @action], resolvedArgs = [], parent = LamBody [@action] get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
      (resume(x));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
    (resume(x));
  })))) benchmarks:197:[a192,top]@[]
Evaluating: @Hnd-get benchmarks:201:[a192,top]@[]
Evaluating: @Hnd-get benchmarks:204:[a192,top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:202 0 3,AppParam benchmarks:203 1 @open(clause-control1)((fn(_w-l302-c16, resume){
  (resume(x));
}))], resolvedArgs = [], parent = AppParam benchmarks:197 0 @Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
    (resume(x));
  }))))}
Evaluating: 3 benchmarks:202:[a192,top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:203 1 @open(clause-control1)((fn(_w-l302-c16, resume){
  (resume(x));
}))], resolvedArgs = [BI@(204:[a192,top]@[])], parent = AppParam benchmarks:197 0 @Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
    (resume(x));
  }))))}
Evaluating: @open(clause-control1)((fn(_w-l302-c16, resume){
  (resume(x));
})) benchmarks:203:[a192,top]@[]
Evaluating: clause-control1 benchmarks:209:[a192,top]@[]
Evaluating: clause-control1 benchmarks:211:[a192,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:207 0 fn(_w-l302-c16, resume){
  resume(x);
}], resolvedArgs = [], parent = AppParam benchmarks:203 1 @open(clause-control1)((fn(_w-l302-c16, resume){
  (resume(x));
}))}
Evaluating: fn(_w-l302-c16, resume){
  resume(x);
} benchmarks:207:[a192,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(211:[a192,top]@[])], parent = AppParam benchmarks:203 1 @open(clause-control1)((fn(_w-l302-c16, resume){
  (resume(x));
}))}
Applying: [] [BI@(211:[a192,top]@[]),BI@(207:[a192,top]@[])]
Applying function: BI@(211:[a192,top]@[]) std/core/hnd/clause-control1
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(204:[a192,top]@[]),BI@(202:[a192,top]@[])], parent = AppParam benchmarks:197 0 @Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
    (resume(x));
  }))))}
Applying: [] [BI@(204:[a192,top]@[]),BI@(202:[a192,top]@[]),BI@(203:[a192,top]@[])]
Applying function: BI@(204:[a192,top]@[]) @Hnd-get
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:198 1 fn(@res){
  @res;
},AppParam benchmarks:199 2 @action], resolvedArgs = [T@analysis/benchmarks/benchmarks/#get/@handle], parent = LamBody [@action] get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
      (resume(x));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} benchmarks:198:[a192,top]@[]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:199 2 @action], resolvedArgs = [T@analysis/benchmarks/benchmarks/#get/@handle,BI@(197:[a192,top]@[])], parent = LamBody [@action] get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
      (resume(x));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action benchmarks:199:[a192,top]@[]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/benchmarks/#get/@handle,BI@(197:[a192,top]@[]),BI@(198:[a192,top]@[])], parent = LamBody [@action] get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(_w-l302-c16, resume){
      (resume(x));
    }))))), (fn(@res){
    @res;
  }), @action)}
Applying: [] [T@analysis/benchmarks/benchmarks/#get/@handle,BI@(197:[a192,top]@[]),BI@(198:[a192,top]@[]),B@(@action:[a192,top]@[])]
Applying function: T@analysis/benchmarks/benchmarks/#get/@handle DefNonRec(get/@handle)
Applying closure: DefNonRec // handler for the effect `:get`
pub fun get/@handle : forall<a,e,b> (hnd : analysis/benchmarks/benchmarks/get<e,b>, ret : (res : a) -> e b, action : () -> <analysis/benchmarks/benchmarks/get|e> a) -> e b;:[a195,a192,top]@[] fvs: fromList [] args [hnd,ret,action]
analysis/benchmarks/benchmarks/@Hnd-get([(@cfc,CI@(@cfc 197:[a192,top]@[])),(@ctl-get,CI@(@ctl-get 197:[a192,top]@[]))]) from BI@(197:[a192,top]@[]) rebinding to B@(hnd:[a195,a192,top]@[])
AppParam(fn(@res){
  @res;
}) from BI@(198:[a192,top]@[]) rebinding to B@(ret:[a195,a192,top]@[])
AppParam(fn(){
  (fn(@action){
    set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
          ((fn(@override-action){
            (fn(@action){
              get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                    (resume(a));
                  }))))), (fn(@res){
                  @res;
                }), @action);
            })((fn(){
              (@mask-at((@evv-index(get/@tag)), True, @override-action));
            }));
          })((fn(){
            () from B@(@action:[a192,top]@[]) rebinding to B@(action:[a195,a192,top]@[])
Evaluating: @hhandle(get/@tag, hnd, ret, action) benchmarks:44:[a195,a192,top]@[]
Evaluating: @hhandle benchmarks:45:[a195,a192,top]@[]
Evaluating: @hhandle benchmarks:50:[a195,a192,top]@[]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:46 0 get/@tag,AppParam benchmarks:47 1 hnd,AppParam benchmarks:48 2 ret,AppParam benchmarks:49 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Evaluating: get/@tag benchmarks:46:[a195,a192,top]@[]
Evaluating: @open(@new-htag)("get@benchmarks") benchmarks:5:[top]@[]
Evaluating: @new-htag benchmarks:40:[top]@[]
Evaluating: @new-htag benchmarks:42:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:38 0 "get@benchmarks"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:get`
pub val get/@tag : hnd/htag<analysis/benchmarks/benchmarks/get>;}
Evaluating: "get@benchmarks" benchmarks:38:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(42:[top]@[])], parent = DefNonRec // runtime tag for the effect `:get`
pub val get/@tag : hnd/htag<analysis/benchmarks/benchmarks/get>;}
Applying: [] [BI@(42:[top]@[]),BI@(38:[top]@[])]
Applying function: BI@(42:[top]@[]) std/core/hnd/@new-htag
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:47 1 hnd,AppParam benchmarks:48 2 ret,AppParam benchmarks:49 3 action], resolvedArgs = [BI@(50:[a195,a192,top]@[])], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Evaluating: hnd benchmarks:47:[a195,a192,top]@[]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:48 2 ret,AppParam benchmarks:49 3 action], resolvedArgs = [BI@(50:[a195,a192,top]@[]),T@analysis/benchmarks/benchmarks/#get/@tag], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Evaluating: ret benchmarks:48:[a195,a192,top]@[]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:49 3 action], resolvedArgs = [BI@(50:[a195,a192,top]@[]),T@analysis/benchmarks/benchmarks/#get/@tag,B@(hnd:[a195,a192,top]@[])], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Evaluating: action benchmarks:49:[a195,a192,top]@[]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(50:[a195,a192,top]@[]),T@analysis/benchmarks/benchmarks/#get/@tag,B@(hnd:[a195,a192,top]@[]),B@(ret:[a195,a192,top]@[])], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Applying: [] [BI@(50:[a195,a192,top]@[]),T@analysis/benchmarks/benchmarks/#get/@tag,B@(hnd:[a195,a192,top]@[]),B@(ret:[a195,a192,top]@[]),B@(action:[a195,a192,top]@[])]
Applying function: BI@(50:[a195,a192,top]@[]) std/core/hnd/@hhandle
OPS analysis/benchmarks/benchmarks/get fvs: BEnv (fromList [x]):[a195,a192,top]@[] benchmarks:44
Rebinding: fromList [x] from [a192,top]@[] to [a195,a192,top]@[]
Evaluating: (fn(@action){
  set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
        ((fn(@override-action){
          (fn(@action){
            get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                  (resume(a));
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
})) benchmarks:220:[delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: fn(@action){
  set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
        ((fn(@override-action){
          (fn(@action){
            get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                  (resume(a));
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
} benchmarks:221:[delim]@[(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:222 0 fn(){
  @open(countdown)(0);
}], resolvedArgs = [], parent = LamBody [] (fn(@action){
  set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
        ((fn(@override-action){
          (fn(@action){
            get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                  (resume(a));
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
}))}
Evaluating: fn(){
  @open(countdown)(0);
} benchmarks:222:[delim]@[(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(221:[delim]@[(benchmarks:44,[a195,a192,top])])], parent = LamBody [] (fn(@action){
  set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
        ((fn(@override-action){
          (fn(@action){
            get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                  (resume(a));
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
}))}
Applying: [] [BI@(221:[delim]@[(benchmarks:44,[a195,a192,top])]),BI@(222:[delim]@[(benchmarks:44,[a195,a192,top])])]
Applying function: BI@(221:[delim]@[(benchmarks:44,[a195,a192,top])]) AppLambda(fn(@action){
  set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
        ((fn(@override-action){
          (fn(@action){
            get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                  (resume(a));
                }))))), (fn(@res){
                @res;
              }), @action);
          })((fn(){
            (@mask-at((@evv-index(get/@tag)), True, @override-action));
          }));
        })((fn(){
          (resume(Unit));
        })));
      )
Applying closure: AppLambda fn(@action){
  set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
        ((fn(@override-action){
          (fn(@action){
            get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                  (resume(a));
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
}:[a220,delim]@[(benchmarks:44,[a195,a192,top])] fvs: fromList [] args [@action]
AppParam(fn(){
  @open(countdown)(0);
}) from BI@(222:[delim]@[(benchmarks:44,[a195,a192,top])]) rebinding to B@(@action:[a220,delim]@[(benchmarks:44,[a195,a192,top])])
Evaluating: set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
      ((fn(@override-action){
        (fn(@action){
          get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                (resume(a));
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
  }), @action) benchmarks:223:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: set/@handle benchmarks:224:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: set/@handle benchmarks:228:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(set/@tag, hnd, ret, action);
} benchmarks:19:[top]@[]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:225 0 @Hnd-set(3, (@open(clause-control1)((fn(a, resume){
    ((fn(@override-action){
      (fn(@action){
        get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
              (resume(a));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (@mask-at((@evv-index(get/@tag)), True, @override-action));
      }));
    })((fn(){
      (resume(Unit));
    })));
  })))),AppParam benchmarks:226 1 fn(@res){
  @res;
},AppParam benchmarks:227 2 @action], resolvedArgs = [], parent = LamBody [@action] set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
      ((fn(@override-action){
        (fn(@action){
          get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                (resume(a));
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
  }), @action)}
Evaluating: @Hnd-set(3, (@open(clause-control1)((fn(a, resume){
    ((fn(@override-action){
      (fn(@action){
        get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
              (resume(a));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (@mask-at((@evv-index(get/@tag)), True, @override-action));
      }));
    })((fn(){
      (resume(Unit));
    })));
  })))) benchmarks:225:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @Hnd-set benchmarks:229:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @Hnd-set benchmarks:232:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:230 0 3,AppParam benchmarks:231 1 @open(clause-control1)((fn(a, resume){
  ((fn(@override-action){
    (fn(@action){
      get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
            (resume(a));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@mask-at((@evv-index(get/@tag)), True, @override-action));
    }));
  })((fn(){
    (resume(Unit));
  })));
}))], resolvedArgs = [], parent = AppParam benchmarks:225 0 @Hnd-set(3, (@open(clause-control1)((fn(a, resume){
    ((fn(@override-action){
      (fn(@action){
        get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
              (resume(a));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (@mask-at((@evv-index(get/@tag)), True, @override-action));
      }));
    })((fn(){
      (resume(Unit));
    })));
  }))))}
Evaluating: 3 benchmarks:230:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:231 1 @open(clause-control1)((fn(a, resume){
  ((fn(@override-action){
    (fn(@action){
      get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
            (resume(a));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@mask-at((@evv-index(get/@tag)), True, @override-action));
    }));
  })((fn(){
    (resume(Unit));
  })));
}))], resolvedArgs = [BI@(232:[a220,delim]@[(benchmarks:44,[a195,a192,top])])], parent = AppParam benchmarks:225 0 @Hnd-set(3, (@open(clause-control1)((fn(a, resume){
    ((fn(@override-action){
      (fn(@action){
        get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
              (resume(a));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (@mask-at((@evv-index(get/@tag)), True, @override-action));
      }));
    })((fn(){
      (resume(Unit));
    })));
  }))))}
Evaluating: @open(clause-control1)((fn(a, resume){
  ((fn(@override-action){
    (fn(@action){
      get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
            (resume(a));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@mask-at((@evv-index(get/@tag)), True, @override-action));
    }));
  })((fn(){
    (resume(Unit));
  })));
})) benchmarks:231:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: clause-control1 benchmarks:237:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: clause-control1 benchmarks:239:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:235 0 fn(a, resume){
  (fn(@override-action){
    (fn(@action){
      get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
            (resume(a));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@mask-at((@evv-index(get/@tag)), True, @override-action));
    }));
  })((fn(){
    (resume(Unit));
  }));
}], resolvedArgs = [], parent = AppParam benchmarks:231 1 @open(clause-control1)((fn(a, resume){
  ((fn(@override-action){
    (fn(@action){
      get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
            (resume(a));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@mask-at((@evv-index(get/@tag)), True, @override-action));
    }));
  })((fn(){
    (resume(Unit));
  })));
}))}
Evaluating: fn(a, resume){
  (fn(@override-action){
    (fn(@action){
      get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
            (resume(a));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@mask-at((@evv-index(get/@tag)), True, @override-action));
    }));
  })((fn(){
    (resume(Unit));
  }));
} benchmarks:235:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(239:[a220,delim]@[(benchmarks:44,[a195,a192,top])])], parent = AppParam benchmarks:231 1 @open(clause-control1)((fn(a, resume){
  ((fn(@override-action){
    (fn(@action){
      get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
            (resume(a));
          }))))), (fn(@res){
          @res;
        }), @action);
    })((fn(){
      (@mask-at((@evv-index(get/@tag)), True, @override-action));
    }));
  })((fn(){
    (resume(Unit));
  })));
}))}
Applying: [] [BI@(239:[a220,delim]@[(benchmarks:44,[a195,a192,top])]),BI@(235:[a220,delim]@[(benchmarks:44,[a195,a192,top])])]
Applying function: BI@(239:[a220,delim]@[(benchmarks:44,[a195,a192,top])]) std/core/hnd/clause-control1
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(232:[a220,delim]@[(benchmarks:44,[a195,a192,top])]),BI@(230:[a220,delim]@[(benchmarks:44,[a195,a192,top])])], parent = AppParam benchmarks:225 0 @Hnd-set(3, (@open(clause-control1)((fn(a, resume){
    ((fn(@override-action){
      (fn(@action){
        get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
              (resume(a));
            }))))), (fn(@res){
            @res;
          }), @action);
      })((fn(){
        (@mask-at((@evv-index(get/@tag)), True, @override-action));
      }));
    })((fn(){
      (resume(Unit));
    })));
  }))))}
Applying: [] [BI@(232:[a220,delim]@[(benchmarks:44,[a195,a192,top])]),BI@(230:[a220,delim]@[(benchmarks:44,[a195,a192,top])]),BI@(231:[a220,delim]@[(benchmarks:44,[a195,a192,top])])]
Applying function: BI@(232:[a220,delim]@[(benchmarks:44,[a195,a192,top])]) @Hnd-set
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:226 1 fn(@res){
  @res;
},AppParam benchmarks:227 2 @action], resolvedArgs = [T@analysis/benchmarks/benchmarks/#set/@handle], parent = LamBody [@action] set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
      ((fn(@override-action){
        (fn(@action){
          get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                (resume(a));
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
  }), @action)}
Evaluating: fn(@res){
  @res;
} benchmarks:226:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:227 2 @action], resolvedArgs = [T@analysis/benchmarks/benchmarks/#set/@handle,BI@(225:[a220,delim]@[(benchmarks:44,[a195,a192,top])])], parent = LamBody [@action] set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
      ((fn(@override-action){
        (fn(@action){
          get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                (resume(a));
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
  }), @action)}
Evaluating: @action benchmarks:227:[a220,delim]@[(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/benchmarks/#set/@handle,BI@(225:[a220,delim]@[(benchmarks:44,[a195,a192,top])]),BI@(226:[a220,delim]@[(benchmarks:44,[a195,a192,top])])], parent = LamBody [@action] set/@handle((@Hnd-set(3, (@open(clause-control1)((fn(a, resume){
      ((fn(@override-action){
        (fn(@action){
          get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
                (resume(a));
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
  }), @action)}
Applying: [] [T@analysis/benchmarks/benchmarks/#set/@handle,BI@(225:[a220,delim]@[(benchmarks:44,[a195,a192,top])]),BI@(226:[a220,delim]@[(benchmarks:44,[a195,a192,top])]),B@(@action:[a220,delim]@[(benchmarks:44,[a195,a192,top])])]
Applying function: T@analysis/benchmarks/benchmarks/#set/@handle DefNonRec(set/@handle)
Applying closure: DefNonRec // handler for the effect `:set`
pub fun set/@handle : forall<a,e,b> (hnd : analysis/benchmarks/benchmarks/set<e,b>, ret : (res : a) -> e b, action : () -> <analysis/benchmarks/benchmarks/set|e> a) -> e b;:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])] fvs: fromList [] args [hnd,ret,action]
analysis/benchmarks/benchmarks/@Hnd-set([(@cfc,CI@(@cfc 225:[a220,delim]@[(benchmarks:44,[a195,a192,top])])),(@ctl-set,CI@(@ctl-set 225:[a220,delim]@[(benchmarks:44,[a195,a192,top])]))]) from BI@(225:[a220,delim]@[(benchmarks:44,[a195,a192,top])]) rebinding to B@(hnd:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])])
AppParam(fn(@res){
  @res;
}) from BI@(226:[a220,delim]@[(benchmarks:44,[a195,a192,top])]) rebinding to B@(ret:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])])
AppParam(fn(){
  @open(countdown)(0);
}) from B@(@action:[a220,delim]@[(benchmarks:44,[a195,a192,top])]) rebinding to B@(action:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])])
Evaluating: @hhandle(set/@tag, hnd, ret, action) benchmarks:98:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @hhandle benchmarks:99:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @hhandle benchmarks:104:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:100 0 set/@tag,AppParam benchmarks:101 1 hnd,AppParam benchmarks:102 2 ret,AppParam benchmarks:103 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(set/@tag, hnd, ret, action)}
Evaluating: set/@tag benchmarks:100:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Evaluating: @open(@new-htag)("set@benchmarks") benchmarks:17:[top]@[]
Evaluating: @new-htag benchmarks:94:[top]@[]
Evaluating: @new-htag benchmarks:96:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:92 0 "set@benchmarks"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:set`
pub val set/@tag : hnd/htag<analysis/benchmarks/benchmarks/set>;}
Evaluating: "set@benchmarks" benchmarks:92:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(96:[top]@[])], parent = DefNonRec // runtime tag for the effect `:set`
pub val set/@tag : hnd/htag<analysis/benchmarks/benchmarks/set>;}
Applying: [] [BI@(96:[top]@[]),BI@(92:[top]@[])]
Applying function: BI@(96:[top]@[]) std/core/hnd/@new-htag
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:101 1 hnd,AppParam benchmarks:102 2 ret,AppParam benchmarks:103 3 action], resolvedArgs = [BI@(104:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])])], parent = LamBody [hnd,ret,action] @hhandle(set/@tag, hnd, ret, action)}
Evaluating: hnd benchmarks:101:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:102 2 ret,AppParam benchmarks:103 3 action], resolvedArgs = [BI@(104:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]),T@analysis/benchmarks/benchmarks/#set/@tag], parent = LamBody [hnd,ret,action] @hhandle(set/@tag, hnd, ret, action)}
Evaluating: ret benchmarks:102:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:103 3 action], resolvedArgs = [BI@(104:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]),T@analysis/benchmarks/benchmarks/#set/@tag,B@(hnd:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])])], parent = LamBody [hnd,ret,action] @hhandle(set/@tag, hnd, ret, action)}
Evaluating: action benchmarks:103:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(104:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]),T@analysis/benchmarks/benchmarks/#set/@tag,B@(hnd:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]),B@(ret:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])])], parent = LamBody [hnd,ret,action] @hhandle(set/@tag, hnd, ret, action)}
Applying: [] [BI@(104:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]),T@analysis/benchmarks/benchmarks/#set/@tag,B@(hnd:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]),B@(ret:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]),B@(action:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])])]
Applying function: BI@(104:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]) std/core/hnd/@hhandle
OPS analysis/benchmarks/benchmarks/set fvs: BEnv (fromList []):[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])] benchmarks:98
Evaluating: @open(countdown)(0) benchmarks:291:[delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: countdown benchmarks:295:[delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
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
} benchmarks:27:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:293 0 0], resolvedArgs = [], parent = LamBody [] @open(countdown)(0)}
Evaluating: 0 benchmarks:293:[delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/benchmarks/countdown], parent = LamBody [] @open(countdown)(0)}
Applying: [] [T@analysis/benchmarks/benchmarks/countdown,BI@(293:[delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])])]
Applying function: T@analysis/benchmarks/benchmarks/countdown DefRec(countdown)
Applying closure: DefRec pub fun countdown : (@_wildcard-x293_15 : int) -> <div,analysis/benchmarks/benchmarks/get,analysis/benchmarks/benchmarks/set> int;:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])] fvs: fromList [] args [@_wildcard-x293_15]
int -> 0 from BI@(293:[delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]) rebinding to B@(@_wildcard-x293_15:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])])
Evaluating: val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} benchmarks:140:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @open(get)(0) benchmarks:142:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: get benchmarks:182:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i);
} benchmarks:13:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:180 0 0], resolvedArgs = [], parent = LetDef val i : int;}
Evaluating: 0 benchmarks:180:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/benchmarks/get], parent = LetDef val i : int;}
Applying: [] [T@analysis/benchmarks/benchmarks/get,BI@(180:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])])]
Applying function: T@analysis/benchmarks/benchmarks/get DefNonRec(get)
Applying closure: DefNonRec // Call the `ctl get` operation of the effect `:get`
pub fun get : (i : int) -> analysis/benchmarks/benchmarks/get int;:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])] fvs: fromList [] args [i]
int -> 0 from BI@(180:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]) rebinding to B@(i:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])])
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i) benchmarks:65:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @perform1 benchmarks:66:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @perform1 benchmarks:70:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:67 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam benchmarks:68 1 forall<e,a> get/@select,AppParam benchmarks:69 2 i], resolvedArgs = [], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) benchmarks:67:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @evv-at benchmarks:74:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @evv-at benchmarks:76:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:72 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam benchmarks:67 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) benchmarks:72:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: @make-ssize_t benchmarks:80:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:78 0 0], resolvedArgs = [], parent = AppParam benchmarks:72 0 @open(@make-ssize_t)(0)}
Evaluating: 0 benchmarks:78:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(80:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])])], parent = AppParam benchmarks:72 0 @open(@make-ssize_t)(0)}
Applying: [] [BI@(80:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]),BI@(78:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])])]
Applying function: BI@(80:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]) std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(76:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])])], parent = AppParam benchmarks:67 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying: [] [BI@(76:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]),BI@(72:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])])]
Applying function: BI@(76:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]) std/core/hnd/@evv-at
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:68 1 forall<e,a> get/@select,AppParam benchmarks:69 2 i], resolvedArgs = [BI@(70:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])])], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i)}
Evaluating: forall<e,a> get/@select benchmarks:68:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: get/@select benchmarks:84:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-get(_, (@ctl-get)) : analysis/benchmarks/benchmarks/get<e,a> )
       -> @ctl-get;
  });
} benchmarks:11:[top]@[]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:69 2 i], resolvedArgs = [BI@(70:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]),BI@(67:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])])], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i)}
Evaluating: i benchmarks:69:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [BI@(70:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]),BI@(67:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]),T@analysis/benchmarks/benchmarks/#get/@select], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i)}
Applying: [] [BI@(70:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]),BI@(67:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]),T@analysis/benchmarks/benchmarks/#get/@select,B@(i:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])])]
Applying function: BI@(70:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]) std/core/hnd/@perform1
Evaluating: resume(x) benchmarks:212:[a195,a192,top]@[]
Evaluating: resume benchmarks:213:[a195,a192,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:214 0 x], resolvedArgs = [], parent = LamBody [_w-l302-c16,resume] resume(x)}
Evaluating: x benchmarks:214:[a195,a192,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:[a195,a192,top]@[])], parent = LamBody [_w-l302-c16,resume] resume(x)}
Applying: [] [B@(resume:[a195,a192,top]@[]),B@(x:[a195,a192,top]@[])]
Applying function: B@(resume:[a195,a192,top]@[]) Kont(analysis/benchmarks/benchmarks/get,IL@(65:get:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]),[a195,a192,top]@[],Handler {ops = B@(hnd:[a195,a192,top]@[]), ret = Just AppParam benchmarks:198 1 fn(@res){
  @res;
}, henv = BEnv (fromList [x])})
Applying continuation benchmarks:212 rebinding fromList [x]
Rebinding: fromList [x] from [a195,a192,top]@[] to [a212,a195,a192,top]@[]
Applying FHLink {linkEff = analysis/benchmarks/benchmarks/set, doCtx = benchmarks:65, hCtx = benchmarks:98, linkKnext = AI@(65:[a142,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:44,[a195,a192,top])]), linkHnd = Handler {ops = B@(hnd:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])}}
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = i, resolved = [], parent = LamBody [@_wildcard-x293_15] val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
}}
Evaluating: match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} benchmarks:143:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @open((==))(i, 0) benchmarks:144:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: (==) benchmarks:151:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:148 0 i,AppParam benchmarks:149 1 0], resolvedArgs = [], parent = CaseMatch @open((==))(i, 0)}
Evaluating: i benchmarks:148:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:149 1 0], resolvedArgs = [BI@(151:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])], parent = CaseMatch @open((==))(i, 0)}
Evaluating: 0 benchmarks:149:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(151:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),B@(i:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])], parent = CaseMatch @open((==))(i, 0)}
Applying: [] [BI@(151:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),B@(i:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),BI@(149:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(151:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]) std/core/int/(==)
Applying FScrut {parent = LetBody match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> i;,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> val _ : ()
            = std/core/types/@open(analysis/benchmarks/benchmarks/set)((std/core/types/@open(std/core/int/(-))(i, 1)));
  analysis/benchmarks/benchmarks/countdown(0);]}
Evaluating: val _ : ()
      = @open(set)((@open((-))(i, 1)));
countdown(0) benchmarks:146:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @open(set)((@open((-))(i, 1))) benchmarks:158:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: set benchmarks:167:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(i){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i);
} benchmarks:25:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:165 0 @open((-))(i, 1)], resolvedArgs = [], parent = LetDef val _ : ();}
Evaluating: @open((-))(i, 1) benchmarks:165:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: (-) benchmarks:174:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(x, y){
  @open(int-sub)(x, y);
} int:319:[top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:171 0 i,AppParam benchmarks:172 1 1], resolvedArgs = [], parent = AppParam benchmarks:165 0 @open((-))(i, 1)}
Evaluating: i benchmarks:171:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:172 1 1], resolvedArgs = [T@std/core/int/(-)], parent = AppParam benchmarks:165 0 @open((-))(i, 1)}
Evaluating: 1 benchmarks:172:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/(-),B@(i:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])], parent = AppParam benchmarks:165 0 @open((-))(i, 1)}
Applying: [] [T@std/core/int/(-),B@(i:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),BI@(172:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: T@std/core/int/(-) DefNonRec((-))
Applying closure: DefNonRec // Subtract two integers.
pub fip fun (-) : (x : int, y : int) -> int;:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])] fvs: fromList [] args [x,y]
int -> 2 from B@(i:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(x:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])
int -> 1 from BI@(172:[a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(y:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])
Evaluating: @open(int-sub)(x, y) int:382:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: int-sub int:387:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:384 0 x,AppParam int:385 1 y], resolvedArgs = [], parent = LamBody [x,y] @open(int-sub)(x, y)}
Evaluating: x int:384:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:385 1 y], resolvedArgs = [BI@(387:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [x,y] @open(int-sub)(x, y)}
Evaluating: y int:385:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(387:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),B@(x:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [x,y] @open(int-sub)(x, y)}
Applying: [] [BI@(387:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),B@(x:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),B@(y:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(387:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]) std/core/int/int-sub
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/benchmarks/set], parent = LetDef val _ : ();}
Applying: [] [T@analysis/benchmarks/benchmarks/set,BI@(382:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: T@analysis/benchmarks/benchmarks/set DefNonRec(set)
Applying closure: DefNonRec // Call the `ctl set` operation of the effect `:set`
pub fun set : (i : int) -> analysis/benchmarks/benchmarks/set ();:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])] fvs: fromList [] args [i]
int -> 1 from BI@(382:[a165,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(i:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i) benchmarks:119:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @perform1 benchmarks:120:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @perform1 benchmarks:124:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:121 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam benchmarks:122 1 forall<e,a> set/@select,AppParam benchmarks:123 2 i], resolvedArgs = [], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) benchmarks:121:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @evv-at benchmarks:128:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @evv-at benchmarks:130:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:126 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam benchmarks:121 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) benchmarks:126:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @make-ssize_t benchmarks:134:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:132 0 0], resolvedArgs = [], parent = AppParam benchmarks:126 0 @open(@make-ssize_t)(0)}
Evaluating: 0 benchmarks:132:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(134:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])], parent = AppParam benchmarks:126 0 @open(@make-ssize_t)(0)}
Applying: [] [BI@(134:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),BI@(132:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(134:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]) std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(130:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])], parent = AppParam benchmarks:121 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying: [] [BI@(130:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),BI@(126:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(130:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]) std/core/hnd/@evv-at
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:122 1 forall<e,a> set/@select,AppParam benchmarks:123 2 i], resolvedArgs = [BI@(124:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i)}
Evaluating: forall<e,a> set/@select benchmarks:122:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: set/@select benchmarks:138:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-set(_, (@ctl-set)) : analysis/benchmarks/benchmarks/set<e,a> )
       -> @ctl-set;
  });
} benchmarks:23:[top]@[]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:123 2 i], resolvedArgs = [BI@(124:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),BI@(121:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i)}
Evaluating: i benchmarks:123:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [BI@(124:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),BI@(121:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),T@analysis/benchmarks/benchmarks/#set/@select], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i)}
Applying: [] [BI@(124:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),BI@(121:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),T@analysis/benchmarks/benchmarks/#set/@select,B@(i:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(124:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]) std/core/hnd/@perform1
Evaluating: (fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(a));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
})((fn(){
  (resume(Unit));
})) benchmarks:240:[a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(a));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
} benchmarks:241:[a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:242 0 fn(){
  resume(Unit);
}], resolvedArgs = [], parent = LamBody [a,resume] (fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(a));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
})((fn(){
  (resume(Unit));
}))}
Evaluating: fn(){
  resume(Unit);
} benchmarks:242:[a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(241:[a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [a,resume] (fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(a));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
})((fn(){
  (resume(Unit));
}))}
Applying: [] [BI@(241:[a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]),BI@(242:[a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(241:[a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]) AppLambda(fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(a));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
})
Applying closure: AppLambda fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(a));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
}:[a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])] fvs: fromList [a] args [@override-action]
AppParam(fn(){
  resume(Unit);
}) from BI@(242:[a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(@override-action:[a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])])
Rebinding: fromList [a] from [a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])] to [a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(a));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
})) benchmarks:243:[a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(a));
      }))))), (fn(@res){
      @res;
    }), @action);
} benchmarks:244:[a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:245 0 fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
}], resolvedArgs = [], parent = LamBody [@override-action] (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(a));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
}))}
Evaluating: fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
} benchmarks:245:[a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(244:[a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [@override-action] (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(a));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
}))}
Applying: [] [BI@(244:[a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]),BI@(245:[a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(244:[a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]) AppLambda(fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(a));
      }))))), (fn(@res){
      @res;
    }), @action);
})
Applying closure: AppLambda fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(a));
      }))))), (fn(@res){
      @res;
    }), @action);
}:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])] fvs: fromList [a] args [@action]
AppParam(fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
}) from BI@(245:[a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(@action:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])])
Rebinding: fromList [a] from [a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])] to [a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(a));
    }))))), (fn(@res){
    @res;
  }), @action) benchmarks:246:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: get/@handle benchmarks:247:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: get/@handle benchmarks:251:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:248 0 @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(a));
  })))),AppParam benchmarks:249 1 fn(@res){
  @res;
},AppParam benchmarks:250 2 @action], resolvedArgs = [], parent = LamBody [@action] get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(a));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(a));
  })))) benchmarks:248:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @Hnd-get benchmarks:252:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @Hnd-get benchmarks:255:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:253 0 3,AppParam benchmarks:254 1 @open(clause-control1)((fn(b, resume){
  (resume(a));
}))], resolvedArgs = [], parent = AppParam benchmarks:248 0 @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(a));
  }))))}
Evaluating: 3 benchmarks:253:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:254 1 @open(clause-control1)((fn(b, resume){
  (resume(a));
}))], resolvedArgs = [BI@(255:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])])], parent = AppParam benchmarks:248 0 @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(a));
  }))))}
Evaluating: @open(clause-control1)((fn(b, resume){
  (resume(a));
})) benchmarks:254:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: clause-control1 benchmarks:260:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: clause-control1 benchmarks:262:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:258 0 fn(b, resume){
  resume(a);
}], resolvedArgs = [], parent = AppParam benchmarks:254 1 @open(clause-control1)((fn(b, resume){
  (resume(a));
}))}
Evaluating: fn(b, resume){
  resume(a);
} benchmarks:258:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(262:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])])], parent = AppParam benchmarks:254 1 @open(clause-control1)((fn(b, resume){
  (resume(a));
}))}
Applying: [] [BI@(262:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]),BI@(258:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(262:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]) std/core/hnd/clause-control1
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(255:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]),BI@(253:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])])], parent = AppParam benchmarks:248 0 @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(a));
  }))))}
Applying: [] [BI@(255:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]),BI@(253:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]),BI@(254:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(255:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]) @Hnd-get
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:249 1 fn(@res){
  @res;
},AppParam benchmarks:250 2 @action], resolvedArgs = [T@analysis/benchmarks/benchmarks/#get/@handle], parent = LamBody [@action] get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(a));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} benchmarks:249:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:250 2 @action], resolvedArgs = [T@analysis/benchmarks/benchmarks/#get/@handle,BI@(248:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [@action] get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(a));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action benchmarks:250:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/benchmarks/#get/@handle,BI@(248:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]),BI@(249:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [@action] get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(a));
    }))))), (fn(@res){
    @res;
  }), @action)}
Applying: [] [T@analysis/benchmarks/benchmarks/#get/@handle,BI@(248:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]),BI@(249:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]),B@(@action:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])])]
Applying function: T@analysis/benchmarks/benchmarks/#get/@handle DefNonRec(get/@handle)
Applying closure: DefNonRec // handler for the effect `:get`
pub fun get/@handle : forall<a,e,b> (hnd : analysis/benchmarks/benchmarks/get<e,b>, ret : (res : a) -> e b, action : () -> <analysis/benchmarks/benchmarks/get|e> a) -> e b;:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])] fvs: fromList [] args [hnd,ret,action]
analysis/benchmarks/benchmarks/@Hnd-get([(@cfc,CI@(@cfc 248:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])])),(@ctl-get,CI@(@ctl-get 248:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]))]) from BI@(248:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(hnd:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])])
AppParam(fn(@res){
  @res;
}) from BI@(249:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(ret:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])])
AppParam(fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
}) from B@(@action:[a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(action:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])])
Evaluating: @hhandle(get/@tag, hnd, ret, action) benchmarks:44:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @hhandle benchmarks:45:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @hhandle benchmarks:50:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:46 0 get/@tag,AppParam benchmarks:47 1 hnd,AppParam benchmarks:48 2 ret,AppParam benchmarks:49 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Evaluating: get/@tag benchmarks:46:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:47 1 hnd,AppParam benchmarks:48 2 ret,AppParam benchmarks:49 3 action], resolvedArgs = [BI@(50:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Evaluating: hnd benchmarks:47:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:48 2 ret,AppParam benchmarks:49 3 action], resolvedArgs = [BI@(50:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]),T@analysis/benchmarks/benchmarks/#get/@tag], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Evaluating: ret benchmarks:48:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:49 3 action], resolvedArgs = [BI@(50:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]),T@analysis/benchmarks/benchmarks/#get/@tag,B@(hnd:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Evaluating: action benchmarks:49:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(50:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]),T@analysis/benchmarks/benchmarks/#get/@tag,B@(hnd:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]),B@(ret:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Applying: [] [BI@(50:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]),T@analysis/benchmarks/benchmarks/#get/@tag,B@(hnd:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]),B@(ret:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]),B@(action:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(50:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]) std/core/hnd/@hhandle
OPS analysis/benchmarks/benchmarks/get fvs: BEnv (fromList [@override-action,a]):[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])] benchmarks:44
Rebinding: fromList [a] from [a243,a240,a223,a220]@[(benchmarks:212,[a212,a195,a192,top])] to [a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]
Rebinding: fromList [@override-action] from [a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])] to [a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]
Rebinding: fromList [@override-action] from [a240,a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])] to [delim]@[(benchmarks:44,[a246,a243,a240,a223]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @mask-at((@evv-index(get/@tag)), True, @override-action) benchmarks:271:[delim]@[(benchmarks:44,[a246,a243,a240,a223]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @override-action benchmarks:275:[delim]@[(benchmarks:44,[a246,a243,a240,a223]),(benchmarks:212,[a212,a195,a192,top])]
Applying FMask
Rebinding: fromList [resume] from [a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])] to [delim]@[(benchmarks:44,[a246,a243,a240,a223]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: resume(Unit) benchmarks:283:[delim]@[(benchmarks:44,[a246,a243,a240,a223]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: resume benchmarks:284:[delim]@[(benchmarks:44,[a246,a243,a240,a223]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:285 0 Unit], resolvedArgs = [], parent = LamBody [] resume(Unit)}
Evaluating: Unit benchmarks:285:[delim]@[(benchmarks:44,[a246,a243,a240,a223]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:[delim]@[(benchmarks:44,[a246,a243,a240,a223]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [] resume(Unit)}
Applying: [] [B@(resume:[delim]@[(benchmarks:44,[a246,a243,a240,a223]),(benchmarks:212,[a212,a195,a192,top])]),BI@(285:[delim]@[(benchmarks:44,[a246,a243,a240,a223]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: B@(resume:[delim]@[(benchmarks:44,[a246,a243,a240,a223]),(benchmarks:212,[a212,a195,a192,top])]) Kont(analysis/benchmarks/benchmarks/set,AI@(119:[a158,a291,delim]@[(benchmarks:98,[a223,a220,delim]),(benchmarks:212,[a212,a195,a192,top])]),[a223,a220,delim]@[(benchmarks:212,[a212,a195,a192,top])],Handler {ops = B@(hnd:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
Applying continuation benchmarks:283 rebinding fromList []
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = _, resolved = [], parent = CaseBranch 1 (@skip std/core/types/False() : bool )
   -> val _ : ()
            = std/core/types/@open(analysis/benchmarks/benchmarks/set)((std/core/types/@open(std/core/int/(-))(i, 1)));
  analysis/benchmarks/benchmarks/countdown(0);}
Evaluating: countdown(0) benchmarks:159:[a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Evaluating: countdown benchmarks:160:[a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:161 0 0], resolvedArgs = [], parent = LetBody countdown(0)}
Evaluating: 0 benchmarks:161:[a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/benchmarks/countdown], parent = LetBody countdown(0)}
Applying: [] [T@analysis/benchmarks/benchmarks/countdown,BI@(161:[a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])])]
Applying function: T@analysis/benchmarks/benchmarks/countdown DefRec(countdown)
Applying closure: DefRec pub fun countdown : (@_wildcard-x293_15 : int) -> <div,analysis/benchmarks/benchmarks/get,analysis/benchmarks/benchmarks/set> int;:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])] fvs: fromList [] args [@_wildcard-x293_15]
int -> 0 from BI@(161:[a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]) rebinding to B@(@_wildcard-x293_15:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])])
Evaluating: val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} benchmarks:140:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Evaluating: @open(get)(0) benchmarks:142:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Evaluating: get benchmarks:182:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:180 0 0], resolvedArgs = [], parent = LetDef val i : int;}
Evaluating: 0 benchmarks:180:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/benchmarks/get], parent = LetDef val i : int;}
Applying: [] [T@analysis/benchmarks/benchmarks/get,BI@(180:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])])]
Applying function: T@analysis/benchmarks/benchmarks/get DefNonRec(get)
Applying closure: DefNonRec // Call the `ctl get` operation of the effect `:get`
pub fun get : (i : int) -> analysis/benchmarks/benchmarks/get int;:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])] fvs: fromList [] args [i]
int -> 0 from BI@(180:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]) rebinding to B@(i:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])])
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i) benchmarks:65:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Evaluating: @perform1 benchmarks:66:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Evaluating: @perform1 benchmarks:70:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:67 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam benchmarks:68 1 forall<e,a> get/@select,AppParam benchmarks:69 2 i], resolvedArgs = [], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) benchmarks:67:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Evaluating: @evv-at benchmarks:74:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Evaluating: @evv-at benchmarks:76:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:72 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam benchmarks:67 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) benchmarks:72:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Evaluating: @make-ssize_t benchmarks:80:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:78 0 0], resolvedArgs = [], parent = AppParam benchmarks:72 0 @open(@make-ssize_t)(0)}
Evaluating: 0 benchmarks:78:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(80:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])])], parent = AppParam benchmarks:72 0 @open(@make-ssize_t)(0)}
Applying: [] [BI@(80:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]),BI@(78:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])])]
Applying function: BI@(80:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]) std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(76:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])])], parent = AppParam benchmarks:67 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying: [] [BI@(76:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]),BI@(72:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])])]
Applying function: BI@(76:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]) std/core/hnd/@evv-at
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:68 1 forall<e,a> get/@select,AppParam benchmarks:69 2 i], resolvedArgs = [BI@(70:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])])], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i)}
Evaluating: forall<e,a> get/@select benchmarks:68:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Evaluating: get/@select benchmarks:84:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:69 2 i], resolvedArgs = [BI@(70:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]),BI@(67:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])])], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i)}
Evaluating: i benchmarks:69:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [BI@(70:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]),BI@(67:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]),T@analysis/benchmarks/benchmarks/#get/@select], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i)}
Applying: [] [BI@(70:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]),BI@(67:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]),T@analysis/benchmarks/benchmarks/#get/@select,B@(i:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])])]
Applying function: BI@(70:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]) std/core/hnd/@perform1
Evaluating: resume(a) benchmarks:263:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]
Evaluating: resume benchmarks:264:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:265 0 a], resolvedArgs = [], parent = LamBody [b,resume] resume(a)}
Evaluating: a benchmarks:265:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [b,resume] resume(a)}
Applying: [] [B@(resume:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]),B@(a:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])])]
Applying function: B@(resume:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]) Kont(analysis/benchmarks/benchmarks/get,IL@(65:get:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]),[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])],Handler {ops = B@(hnd:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [@override-action,a])})
Applying continuation benchmarks:263 rebinding fromList [@override-action,a]
Rebinding: fromList [@override-action,a] from [a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])] to [a263,a246,a243,a240]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FHLink {linkEff = analysis/benchmarks/benchmarks/set, doCtx = benchmarks:65, hCtx = benchmarks:283, linkKnext = AI@(65:[a142,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a223])]), linkHnd = Handler {ops = B@(hnd:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])}}
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = i, resolved = [], parent = LamBody [@_wildcard-x293_15] val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
}}
Evaluating: match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} benchmarks:143:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: @open((==))(i, 0) benchmarks:144:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: (==) benchmarks:151:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:148 0 i,AppParam benchmarks:149 1 0], resolvedArgs = [], parent = CaseMatch @open((==))(i, 0)}
Evaluating: i benchmarks:148:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:149 1 0], resolvedArgs = [BI@(151:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])], parent = CaseMatch @open((==))(i, 0)}
Evaluating: 0 benchmarks:149:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(151:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),B@(i:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])], parent = CaseMatch @open((==))(i, 0)}
Applying: [] [BI@(151:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),B@(i:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),BI@(149:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])]
Applying function: BI@(151:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]) std/core/int/(==)
Applying FScrut {parent = LetBody match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> i;,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> val _ : ()
            = std/core/types/@open(analysis/benchmarks/benchmarks/set)((std/core/types/@open(std/core/int/(-))(i, 1)));
  analysis/benchmarks/benchmarks/countdown(0);]}
Evaluating: val _ : ()
      = @open(set)((@open((-))(i, 1)));
countdown(0) benchmarks:146:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: @open(set)((@open((-))(i, 1))) benchmarks:158:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: set benchmarks:167:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:165 0 @open((-))(i, 1)], resolvedArgs = [], parent = LetDef val _ : ();}
Evaluating: @open((-))(i, 1) benchmarks:165:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: (-) benchmarks:174:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:171 0 i,AppParam benchmarks:172 1 1], resolvedArgs = [], parent = AppParam benchmarks:165 0 @open((-))(i, 1)}
Evaluating: i benchmarks:171:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:172 1 1], resolvedArgs = [T@std/core/int/(-)], parent = AppParam benchmarks:165 0 @open((-))(i, 1)}
Evaluating: 1 benchmarks:172:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@std/core/int/(-),B@(i:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])], parent = AppParam benchmarks:165 0 @open((-))(i, 1)}
Applying: [] [T@std/core/int/(-),B@(i:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),BI@(172:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])]
Applying function: T@std/core/int/(-) DefNonRec((-))
Applying closure: DefNonRec // Subtract two integers.
pub fip fun (-) : (x : int, y : int) -> int;:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])] fvs: fromList [] args [x,y]
int -> 1 from B@(i:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]) rebinding to B@(x:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])
int -> 1 from BI@(172:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]) rebinding to B@(y:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])
Evaluating: @open(int-sub)(x, y) int:382:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: int-sub int:387:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:384 0 x,AppParam int:385 1 y], resolvedArgs = [], parent = LamBody [x,y] @open(int-sub)(x, y)}
Evaluating: x int:384:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam int:385 1 y], resolvedArgs = [BI@(387:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])], parent = LamBody [x,y] @open(int-sub)(x, y)}
Evaluating: y int:385:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(387:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),B@(x:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])], parent = LamBody [x,y] @open(int-sub)(x, y)}
Applying: [] [BI@(387:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),B@(x:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),B@(y:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])]
Applying function: BI@(387:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]) std/core/int/int-sub
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/benchmarks/set], parent = LetDef val _ : ();}
Applying: [] [T@analysis/benchmarks/benchmarks/set,BI@(382:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])]
Applying function: T@analysis/benchmarks/benchmarks/set DefNonRec(set)
Applying closure: DefNonRec // Call the `ctl set` operation of the effect `:set`
pub fun set : (i : int) -> analysis/benchmarks/benchmarks/set ();:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])] fvs: fromList [] args [i]
int -> 0 from BI@(382:[a165,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]) rebinding to B@(i:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i) benchmarks:119:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: @perform1 benchmarks:120:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: @perform1 benchmarks:124:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:121 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam benchmarks:122 1 forall<e,a> set/@select,AppParam benchmarks:123 2 i], resolvedArgs = [], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) benchmarks:121:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: @evv-at benchmarks:128:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: @evv-at benchmarks:130:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:126 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam benchmarks:121 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) benchmarks:126:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: @make-ssize_t benchmarks:134:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:132 0 0], resolvedArgs = [], parent = AppParam benchmarks:126 0 @open(@make-ssize_t)(0)}
Evaluating: 0 benchmarks:132:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(134:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])], parent = AppParam benchmarks:126 0 @open(@make-ssize_t)(0)}
Applying: [] [BI@(134:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),BI@(132:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])]
Applying function: BI@(134:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]) std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(130:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])], parent = AppParam benchmarks:121 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying: [] [BI@(130:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),BI@(126:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])]
Applying function: BI@(130:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]) std/core/hnd/@evv-at
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:122 1 forall<e,a> set/@select,AppParam benchmarks:123 2 i], resolvedArgs = [BI@(124:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i)}
Evaluating: forall<e,a> set/@select benchmarks:122:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: set/@select benchmarks:138:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:123 2 i], resolvedArgs = [BI@(124:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),BI@(121:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i)}
Evaluating: i benchmarks:123:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [BI@(124:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),BI@(121:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),T@analysis/benchmarks/benchmarks/#set/@select], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> set/@select), i)}
Applying: [] [BI@(124:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),BI@(121:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),T@analysis/benchmarks/benchmarks/#set/@select,B@(i:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])]
Applying function: BI@(124:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]) std/core/hnd/@perform1
Evaluating: (fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(a));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
})((fn(){
  (resume(Unit));
})) benchmarks:240:[a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(a));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
} benchmarks:241:[a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:242 0 fn(){
  resume(Unit);
}], resolvedArgs = [], parent = LamBody [a,resume] (fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(a));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
})((fn(){
  (resume(Unit));
}))}
Evaluating: fn(){
  resume(Unit);
} benchmarks:242:[a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(241:[a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [a,resume] (fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(a));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
})((fn(){
  (resume(Unit));
}))}
Applying: [] [BI@(241:[a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),BI@(242:[a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(241:[a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]) AppLambda(fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(a));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
})
Applying closure: AppLambda fn(@override-action){
  (fn(@action){
    get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
          (resume(a));
        }))))), (fn(@res){
        @res;
      }), @action);
  })((fn(){
    (@mask-at((@evv-index(get/@tag)), True, @override-action));
  }));
}:[a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])] fvs: fromList [a] args [@override-action]
AppParam(fn(){
  resume(Unit);
}) from BI@(242:[a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(@override-action:[a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])
Rebinding: fromList [a] from [a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])] to [a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(a));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
})) benchmarks:243:[a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(a));
      }))))), (fn(@res){
      @res;
    }), @action);
} benchmarks:244:[a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:245 0 fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
}], resolvedArgs = [], parent = LamBody [@override-action] (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(a));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
}))}
Evaluating: fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
} benchmarks:245:[a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(244:[a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [@override-action] (fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(a));
      }))))), (fn(@res){
      @res;
    }), @action);
})((fn(){
  (@mask-at((@evv-index(get/@tag)), True, @override-action));
}))}
Applying: [] [BI@(244:[a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),BI@(245:[a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(244:[a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]) AppLambda(fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(a));
      }))))), (fn(@res){
      @res;
    }), @action);
})
Applying closure: AppLambda fn(@action){
  get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
        (resume(a));
      }))))), (fn(@res){
      @res;
    }), @action);
}:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])] fvs: fromList [a] args [@action]
AppParam(fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
}) from BI@(245:[a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(@action:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])
Rebinding: fromList [a] from [a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])] to [a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(a));
    }))))), (fn(@res){
    @res;
  }), @action) benchmarks:246:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: get/@handle benchmarks:247:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: get/@handle benchmarks:251:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:248 0 @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(a));
  })))),AppParam benchmarks:249 1 fn(@res){
  @res;
},AppParam benchmarks:250 2 @action], resolvedArgs = [], parent = LamBody [@action] get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(a));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(a));
  })))) benchmarks:248:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @Hnd-get benchmarks:252:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @Hnd-get benchmarks:255:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:253 0 3,AppParam benchmarks:254 1 @open(clause-control1)((fn(b, resume){
  (resume(a));
}))], resolvedArgs = [], parent = AppParam benchmarks:248 0 @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(a));
  }))))}
Evaluating: 3 benchmarks:253:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:254 1 @open(clause-control1)((fn(b, resume){
  (resume(a));
}))], resolvedArgs = [BI@(255:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])], parent = AppParam benchmarks:248 0 @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(a));
  }))))}
Evaluating: @open(clause-control1)((fn(b, resume){
  (resume(a));
})) benchmarks:254:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: clause-control1 benchmarks:260:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: clause-control1 benchmarks:262:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:258 0 fn(b, resume){
  resume(a);
}], resolvedArgs = [], parent = AppParam benchmarks:254 1 @open(clause-control1)((fn(b, resume){
  (resume(a));
}))}
Evaluating: fn(b, resume){
  resume(a);
} benchmarks:258:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(262:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])], parent = AppParam benchmarks:254 1 @open(clause-control1)((fn(b, resume){
  (resume(a));
}))}
Applying: [] [BI@(262:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),BI@(258:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(262:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]) std/core/hnd/clause-control1
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(255:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),BI@(253:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])], parent = AppParam benchmarks:248 0 @Hnd-get(3, (@open(clause-control1)((fn(b, resume){
    (resume(a));
  }))))}
Applying: [] [BI@(255:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),BI@(253:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),BI@(254:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(255:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]) @Hnd-get
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:249 1 fn(@res){
  @res;
},AppParam benchmarks:250 2 @action], resolvedArgs = [T@analysis/benchmarks/benchmarks/#get/@handle], parent = LamBody [@action] get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(a));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} benchmarks:249:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:250 2 @action], resolvedArgs = [T@analysis/benchmarks/benchmarks/#get/@handle,BI@(248:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [@action] get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(a));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action benchmarks:250:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/benchmarks/#get/@handle,BI@(248:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),BI@(249:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [@action] get/@handle((@Hnd-get(3, (@open(clause-control1)((fn(b, resume){
      (resume(a));
    }))))), (fn(@res){
    @res;
  }), @action)}
Applying: [] [T@analysis/benchmarks/benchmarks/#get/@handle,BI@(248:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),BI@(249:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),B@(@action:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: T@analysis/benchmarks/benchmarks/#get/@handle DefNonRec(get/@handle)
Applying closure: DefNonRec // handler for the effect `:get`
pub fun get/@handle : forall<a,e,b> (hnd : analysis/benchmarks/benchmarks/get<e,b>, ret : (res : a) -> e b, action : () -> <analysis/benchmarks/benchmarks/get|e> a) -> e b;:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])] fvs: fromList [] args [hnd,ret,action]
analysis/benchmarks/benchmarks/@Hnd-get([(@cfc,CI@(@cfc 248:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])),(@ctl-get,CI@(@ctl-get 248:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]))]) from BI@(248:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(hnd:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])
AppParam(fn(@res){
  @res;
}) from BI@(249:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(ret:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])
AppParam(fn(){
  @mask-at((@evv-index(get/@tag)), True, @override-action);
}) from B@(@action:[a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]) rebinding to B@(action:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])
Evaluating: @hhandle(get/@tag, hnd, ret, action) benchmarks:44:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @hhandle benchmarks:45:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: @hhandle benchmarks:50:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:46 0 get/@tag,AppParam benchmarks:47 1 hnd,AppParam benchmarks:48 2 ret,AppParam benchmarks:49 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Evaluating: get/@tag benchmarks:46:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:47 1 hnd,AppParam benchmarks:48 2 ret,AppParam benchmarks:49 3 action], resolvedArgs = [BI@(50:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Evaluating: hnd benchmarks:47:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:48 2 ret,AppParam benchmarks:49 3 action], resolvedArgs = [BI@(50:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),T@analysis/benchmarks/benchmarks/#get/@tag], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Evaluating: ret benchmarks:48:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam benchmarks:49 3 action], resolvedArgs = [BI@(50:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),T@analysis/benchmarks/benchmarks/#get/@tag,B@(hnd:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Evaluating: action benchmarks:49:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(50:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),T@analysis/benchmarks/benchmarks/#get/@tag,B@(hnd:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),B@(ret:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [hnd,ret,action] @hhandle(get/@tag, hnd, ret, action)}
Applying: [] [BI@(50:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),T@analysis/benchmarks/benchmarks/#get/@tag,B@(hnd:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),B@(ret:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),B@(action:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: BI@(50:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]) std/core/hnd/@hhandle
OPS analysis/benchmarks/benchmarks/get fvs: BEnv (fromList [@override-action,a]):[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])] benchmarks:44
Rebinding: fromList [a] from [a243,a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])] to [a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Rebinding: fromList [@override-action] from [a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])] to [a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Rebinding: fromList [@override-action] from [a240,a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])] to [delim]@[(benchmarks:44,[a246,a243,a240,a283]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: @mask-at((@evv-index(get/@tag)), True, @override-action) benchmarks:271:[delim]@[(benchmarks:44,[a246,a243,a240,a283]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: @override-action benchmarks:275:[delim]@[(benchmarks:44,[a246,a243,a240,a283]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FMask
Rebinding: fromList [resume] from [a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])] to [delim]@[(benchmarks:44,[a246,a243,a240,a283]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: resume(Unit) benchmarks:283:[delim]@[(benchmarks:44,[a246,a243,a240,a283]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: resume benchmarks:284:[delim]@[(benchmarks:44,[a246,a243,a240,a283]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:285 0 Unit], resolvedArgs = [], parent = LamBody [] resume(Unit)}
Evaluating: Unit benchmarks:285:[delim]@[(benchmarks:44,[a246,a243,a240,a283]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:[delim]@[(benchmarks:44,[a246,a243,a240,a283]),(benchmarks:263,[a263,a246,a243,a240])])], parent = LamBody [] resume(Unit)}
Applying: [] [B@(resume:[delim]@[(benchmarks:44,[a246,a243,a240,a283]),(benchmarks:263,[a263,a246,a243,a240])]),BI@(285:[delim]@[(benchmarks:44,[a246,a243,a240,a283]),(benchmarks:263,[a263,a246,a243,a240])])]
Applying function: B@(resume:[delim]@[(benchmarks:44,[a246,a243,a240,a283]),(benchmarks:263,[a263,a246,a243,a240])]) Kont(analysis/benchmarks/benchmarks/set,AI@(119:[a158,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),[a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])],Handler {ops = B@(hnd:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])})
Applying continuation benchmarks:283 rebinding fromList []
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = _, resolved = [], parent = CaseBranch 1 (@skip std/core/types/False() : bool )
   -> val _ : ()
            = std/core/types/@open(analysis/benchmarks/benchmarks/set)((std/core/types/@open(std/core/int/(-))(i, 1)));
  analysis/benchmarks/benchmarks/countdown(0);}
Evaluating: countdown(0) benchmarks:159:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Evaluating: countdown benchmarks:160:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:161 0 0], resolvedArgs = [], parent = LetBody countdown(0)}
Evaluating: 0 benchmarks:161:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/benchmarks/countdown], parent = LetBody countdown(0)}
Applying: [] [T@analysis/benchmarks/benchmarks/countdown,BI@(161:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])])]
Applying function: T@analysis/benchmarks/benchmarks/countdown DefRec(countdown)
Applying closure: DefRec pub fun countdown : (@_wildcard-x293_15 : int) -> <div,analysis/benchmarks/benchmarks/get,analysis/benchmarks/benchmarks/set> int;:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])] fvs: fromList [] args [@_wildcard-x293_15]
int -> 0 from BI@(161:[a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]) rebinding to B@(@_wildcard-x293_15:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])])
Evaluating: val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} benchmarks:140:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Evaluating: @open(get)(0) benchmarks:142:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Evaluating: get benchmarks:182:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:180 0 0], resolvedArgs = [], parent = LetDef val i : int;}
Evaluating: 0 benchmarks:180:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/benchmarks/get], parent = LetDef val i : int;}
Applying: [] [T@analysis/benchmarks/benchmarks/get,BI@(180:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])])]
Applying function: T@analysis/benchmarks/benchmarks/get DefNonRec(get)
Applying closure: DefNonRec // Call the `ctl get` operation of the effect `:get`
pub fun get : (i : int) -> analysis/benchmarks/benchmarks/get int;:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])] fvs: fromList [] args [i]
int -> 0 from BI@(180:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]) rebinding to B@(i:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])])
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i) benchmarks:65:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Evaluating: @perform1 benchmarks:66:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Evaluating: @perform1 benchmarks:70:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:67 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam benchmarks:68 1 forall<e,a> get/@select,AppParam benchmarks:69 2 i], resolvedArgs = [], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) benchmarks:67:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Evaluating: @evv-at benchmarks:74:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Evaluating: @evv-at benchmarks:76:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:72 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam benchmarks:67 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) benchmarks:72:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Evaluating: @make-ssize_t benchmarks:80:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:78 0 0], resolvedArgs = [], parent = AppParam benchmarks:72 0 @open(@make-ssize_t)(0)}
Evaluating: 0 benchmarks:78:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(80:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])])], parent = AppParam benchmarks:72 0 @open(@make-ssize_t)(0)}
Applying: [] [BI@(80:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]),BI@(78:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])])]
Applying function: BI@(80:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]) std/core/types/@make-ssize_t
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(76:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])])], parent = AppParam benchmarks:67 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying: [] [BI@(76:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]),BI@(72:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])])]
Applying function: BI@(76:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]) std/core/hnd/@evv-at
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:68 1 forall<e,a> get/@select,AppParam benchmarks:69 2 i], resolvedArgs = [BI@(70:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])])], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i)}
Evaluating: forall<e,a> get/@select benchmarks:68:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Evaluating: get/@select benchmarks:84:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam benchmarks:69 2 i], resolvedArgs = [BI@(70:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]),BI@(67:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])])], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i)}
Evaluating: i benchmarks:69:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [BI@(70:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]),BI@(67:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]),T@analysis/benchmarks/benchmarks/#get/@select], parent = LamBody [i] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> get/@select), i)}
Applying: [] [BI@(70:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]),BI@(67:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]),T@analysis/benchmarks/benchmarks/#get/@select,B@(i:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])])]
Applying function: BI@(70:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]) std/core/hnd/@perform1
Evaluating: resume(a) benchmarks:263:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Evaluating: resume benchmarks:264:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam benchmarks:265 0 a], resolvedArgs = [], parent = LamBody [b,resume] resume(a)}
Evaluating: a benchmarks:265:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [B@(resume:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])], parent = LamBody [b,resume] resume(a)}
Applying: [] [B@(resume:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]),B@(a:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])]
Applying function: B@(resume:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]) Kont(analysis/benchmarks/benchmarks/get,IL@(65:get:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]),[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])],Handler {ops = B@(hnd:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]), ret = Just AppParam benchmarks:249 1 fn(@res){
  @res;
}, henv = BEnv (fromList [@override-action,a])})
Applying continuation benchmarks:263 rebinding fromList [@override-action,a]
Rebinding: fromList [@override-action,a] from [a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])] to [a263,a246,a243,a240]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FHLink {linkEff = analysis/benchmarks/benchmarks/set, doCtx = benchmarks:65, hCtx = benchmarks:283, linkKnext = AI@(65:[a142,a159,a159,a291]@[(benchmarks:283,[a283,delim]),(benchmarks:44,[a246,a243,a240,a283])]), linkHnd = Handler {ops = B@(hnd:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])]), ret = Just AppParam benchmarks:226 1 fn(@res){
  @res;
}, henv = BEnv (fromList [])}}
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = i, resolved = [], parent = LamBody [@_wildcard-x293_15] val i : int
      = @open(get)(0);
match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
}}
Evaluating: match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
} benchmarks:143:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: @open((==))(i, 0) benchmarks:144:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Evaluating: (==) benchmarks:151:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:148 0 i,AppParam benchmarks:149 1 0], resolvedArgs = [], parent = CaseMatch @open((==))(i, 0)}
Evaluating: i benchmarks:148:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam benchmarks:149 1 0], resolvedArgs = [BI@(151:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])], parent = CaseMatch @open((==))(i, 0)}
Evaluating: 0 benchmarks:149:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(151:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),B@(i:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])], parent = CaseMatch @open((==))(i, 0)}
Applying: [] [BI@(151:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),B@(i:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]),BI@(149:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])])]
Applying function: BI@(151:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]) std/core/int/(==)
Applying FScrut {parent = LetBody match ((@open((==))(i, 0))) {
  (True() : bool )
     -> i;
  (@skip False() : bool )
     -> val _ : ()
              = @open(set)((@open((-))(i, 1)));
    countdown(0);
}, branches = [CaseBranch 0 (std/core/types/True() : bool )
   -> i;,CaseBranch 1 (@skip std/core/types/False() : bool )
   -> val _ : ()
            = std/core/types/@open(analysis/benchmarks/benchmarks/set)((std/core/types/@open(std/core/int/(-))(i, 1)));
  analysis/benchmarks/benchmarks/countdown(0);]}
Evaluating: i benchmarks:145:[a159,a159,a291,delim]@[(benchmarks:283,[a283,delim]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FDollar {vaddr = B@(ret:[a223,a220,delim]@[(benchmarks:44,[a195,a192,top])])}
Evaluating: @res benchmarks:288:[a283,delim]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:263,[a263,a246,a243,a240])]
Applying FDollar {vaddr = B@(ret:[a246,a243,a240,a283]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])])}
Evaluating: @res benchmarks:268:[a263,a246,a243,a240]@[(benchmarks:263,[a263,a246,a243,a240]),(benchmarks:212,[a212,a195,a192,top])]
Applying FDollar {vaddr = B@(ret:[a246,a243,a240,a223]@[(benchmarks:212,[a212,a195,a192,top])])}
Evaluating: @res benchmarks:268:[a263,a246,a243,a240]@[(benchmarks:212,[a212,a195,a192,top])]
Applying FDollar {vaddr = B@(ret:[a195,a192,top]@[])}
Evaluating: @res benchmarks:217:[a212,a195,a192,top]@[]
Evaluating: 0 benchmarks:307:[top]@[]
d=2,m=4
Result 1 / 1
Result 100.0%, time: 0.152728029s
