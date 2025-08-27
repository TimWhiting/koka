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
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/bio], parent = LamBody [] bio((fn(){
  (session-manager3(Root, (fn(){
      val _ : ()
            = (@open(su)(Alice));
      (@open(echo)((@open(whoami)())));
    })));
}))}
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
Evaluating: @open(unsafe-no-local-cast)((forall<h> action))() types:1615:[a197,a913,top]@[]
Evaluating: @open(unsafe-no-local-cast)((forall<h> action)) types:1616:[a197,a913,top]@[]
Evaluating: unsafe-no-local-cast types:1620:[a197,a913,top]@[]
Evaluating: unsafe-no-local-cast types:1621:[a197,a913,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam types:1618 0 forall<h> action], resolvedArgs = [], parent = AppLambda @open(unsafe-no-local-cast)((forall<h> action))}
Evaluating: forall<h> action types:1618:[a197,a913,top]@[]
Evaluating: action types:1622:[a197,a913,top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(1621:[a197,a913,top]@[])], parent = AppLambda @open(unsafe-no-local-cast)((forall<h> action))}
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [action] @open(unsafe-no-local-cast)((forall<h> action))()}
Rebinding: fromList [action1] from [a913,top]@[] to [a1615,a197,a913,top]@[]
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
Evaluating: @Hnodiv unix:203:[a1615,a197,a913,top]@[]
Evaluating: @Hnodiv unix:275:[a1615,a197,a913,top]@[]
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
Rebinding: fromList [action1,buf,iev@671,iev@720] from [a1615,a197,a913,top]@[] to [delim]@[(unix:206,[a1615,a197,a913,top])]
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
Rebinding: fromList [buf,iev@671] from [delim]@[(unix:206,[a1615,a197,a913,top])] to [a212,delim]@[(unix:206,[a1615,a197,a913,top])]
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
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:222 0 1,AppParam unix:223 1 @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
}))], resolvedArgs = [], parent = AppParam unix:217 0 @Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
    (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
  }))))}
Evaluating: 1 unix:222:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
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
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:227 0 fn(fd, s){
  local-set(buf, (@open((++))((local-get(buf, iev@671)), s)));
}], resolvedArgs = [], parent = AppParam unix:223 1 @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
}))}
Evaluating: fn(fd, s){
  local-set(buf, (@open((++))((local-get(buf, iev@671)), s)));
} unix:227:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(231:[a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:223 1 @open(clause-tail2)((fn(fd, s){
  (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
}))}
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(224:[a212,delim]@[(unix:206,[a1615,a197,a913,top])]),BI@(222:[a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = AppParam unix:217 0 @Hnd-bio(1, (@open(clause-tail2)((fn(fd, s){
    (local-set(buf, (@open((++))((local-get(buf, iev@671)), s))));
  }))))}
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
Evaluating: @hhandle(bio/@tag, hnd, ret, action) unix:142:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: @hhandle unix:143:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: @hhandle unix:148:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:144 0 bio/@tag,AppParam unix:145 1 hnd,AppParam unix:146 2 ret,AppParam unix:147 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
Evaluating: bio/@tag unix:144:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: @open(@new-htag)("bio@unix") unix:5:[top]@[]
Evaluating: @new-htag unix:138:[top]@[]
Evaluating: @new-htag unix:140:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:136 0 "bio@unix"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:bio`
pub val bio/@tag : hnd/htag<analysis/benchmarks/handlers/unix/bio>;}
Evaluating: "bio@unix" unix:136:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(140:[top]@[])], parent = DefNonRec // runtime tag for the effect `:bio`
pub val bio/@tag : hnd/htag<analysis/benchmarks/handlers/unix/bio>;}
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:145 1 hnd,AppParam unix:146 2 ret,AppParam unix:147 3 action], resolvedArgs = [BI@(148:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
Evaluating: hnd unix:145:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:146 2 ret,AppParam unix:147 3 action], resolvedArgs = [BI@(148:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#bio/@tag], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
Evaluating: ret unix:146:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:147 3 action], resolvedArgs = [BI@(148:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#bio/@tag,B@(hnd:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
Evaluating: action unix:147:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(148:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),T@analysis/benchmarks/handlers/unix/#bio/@tag,B@(hnd:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),B@(ret:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [hnd,ret,action] @hhandle(bio/@tag, hnd, ret, action)}
OPS analysis/benchmarks/handlers/unix/bio fvs: BEnv (fromList [action1,buf,iev@671,iev@720]):[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])] unix:142
Rebinding: fromList [buf,iev@671] from [a212,delim]@[(unix:206,[a1615,a197,a913,top])] to [a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Rebinding: fromList [action1,buf,iev@720] from [delim]@[(unix:206,[a1615,a197,a913,top])] to [a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Rebinding: fromList [action1,buf,iev@720] from [delim]@[(unix:206,[a1615,a197,a913,top])] to [delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: Tuple2(((fn(){
    @mask-builtin((fn(){
      (action1());
    }));
  })()), (local-get(buf, iev@720))) unix:255:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: Tuple2 unix:256:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: Tuple2 unix:259:[delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
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
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = AppParam unix:257 0 (fn(){
  @mask-builtin((fn(){
    (action1());
  }));
})()}
Rebinding: fromList [action1] from [delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @mask-builtin((fn(){
  (action1());
})) unix:261:[a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(){
  action1();
} unix:263:[a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
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
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/session-manager3,BI@(919:[a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = LamBody [] session-manager3(Root, (fn(){
    val _ : ()
          = (@open(su)(Alice));
    (@open(echo)((@open(whoami)())));
  }))}
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
Evaluating: @open(unsafe-no-local-cast)((forall<h> action))() types:1615:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: @open(unsafe-no-local-cast)((forall<h> action)) types:1616:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: unsafe-no-local-cast types:1620:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: unsafe-no-local-cast types:1621:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam types:1618 0 forall<h> action], resolvedArgs = [], parent = AppLambda @open(unsafe-no-local-cast)((forall<h> action))}
Evaluating: forall<h> action types:1618:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Evaluating: action types:1622:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(1621:[a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])])], parent = AppLambda @open(unsafe-no-local-cast)((forall<h> action))}
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [action] @open(unsafe-no-local-cast)((forall<h> action))()}
Rebinding: fromList [action6,initial-user] from [a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]
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
Rebinding: fromList [action6,iev@2567,user] from [a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])] to [delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
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
})) unix:837:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Evaluating: fn(@action){
  whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
        (@open(user/show)((local-get(user, iev@2567))));
      }))))), (fn(@res){
      @res;
    }), @action);
} unix:838:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
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
} unix:839:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(838:[delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])])], parent = LamBody [user] (fn(@action){
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
Rebinding: fromList [iev@2567,user] from [delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])] to [a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Evaluating: whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
      (@open(user/show)((local-get(user, iev@2567))));
    }))))), (fn(@res){
    @res;
  }), @action) unix:840:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Evaluating: whoami/@handle unix:841:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Evaluating: whoami/@handle unix:845:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(whoami/@tag, hnd, ret, action);
} unix:49:[top]@[]
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
  })))) unix:842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Evaluating: @Hnd-whoami unix:846:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Evaluating: @Hnd-whoami unix:849:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:847 0 1,AppParam unix:848 1 @open(clause-tail0)((fn(){
  (@open(user/show)((local-get(user, iev@2567))));
}))], resolvedArgs = [], parent = AppParam unix:842 0 @Hnd-whoami(1, (@open(clause-tail0)((fn(){
    (@open(user/show)((local-get(user, iev@2567))));
  }))))}
Evaluating: 1 unix:847:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:848 1 @open(clause-tail0)((fn(){
  (@open(user/show)((local-get(user, iev@2567))));
}))], resolvedArgs = [BI@(849:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])])], parent = AppParam unix:842 0 @Hnd-whoami(1, (@open(clause-tail0)((fn(){
    (@open(user/show)((local-get(user, iev@2567))));
  }))))}
Evaluating: @open(clause-tail0)((fn(){
  (@open(user/show)((local-get(user, iev@2567))));
})) unix:848:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Evaluating: clause-tail0 unix:854:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Evaluating: clause-tail0 unix:856:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:852 0 fn(){
  @open(user/show)((local-get(user, iev@2567)));
}], resolvedArgs = [], parent = AppParam unix:848 1 @open(clause-tail0)((fn(){
  (@open(user/show)((local-get(user, iev@2567))));
}))}
Evaluating: fn(){
  @open(user/show)((local-get(user, iev@2567)));
} unix:852:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(856:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])])], parent = AppParam unix:848 1 @open(clause-tail0)((fn(){
  (@open(user/show)((local-get(user, iev@2567))));
}))}
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(849:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]),BI@(847:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])])], parent = AppParam unix:842 0 @Hnd-whoami(1, (@open(clause-tail0)((fn(){
    (@open(user/show)((local-get(user, iev@2567))));
  }))))}
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:843 1 fn(@res){
  @res;
},AppParam unix:844 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#whoami/@handle], parent = LamBody [@action] whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
      (@open(user/show)((local-get(user, iev@2567))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} unix:843:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:844 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#whoami/@handle,BI@(842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])])], parent = LamBody [@action] whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
      (@open(user/show)((local-get(user, iev@2567))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action unix:844:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#whoami/@handle,BI@(842:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]),BI@(843:[a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])])], parent = LamBody [@action] whoami/@handle((@Hnd-whoami(1, (@open(clause-tail0)((fn(){
      (@open(user/show)((local-get(user, iev@2567))));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @hhandle(whoami/@tag, hnd, ret, action) unix:493:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Evaluating: @hhandle unix:494:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Evaluating: @hhandle unix:499:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:495 0 whoami/@tag,AppParam unix:496 1 hnd,AppParam unix:497 2 ret,AppParam unix:498 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(whoami/@tag, hnd, ret, action)}
Evaluating: whoami/@tag unix:495:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Evaluating: @open(@new-htag)("whoami@unix") unix:47:[top]@[]
Evaluating: @new-htag unix:489:[top]@[]
Evaluating: @new-htag unix:491:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:487 0 "whoami@unix"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:whoami`
pub val whoami/@tag : hnd/htag<analysis/benchmarks/handlers/unix/whoami>;}
Evaluating: "whoami@unix" unix:487:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(491:[top]@[])], parent = DefNonRec // runtime tag for the effect `:whoami`
pub val whoami/@tag : hnd/htag<analysis/benchmarks/handlers/unix/whoami>;}
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:496 1 hnd,AppParam unix:497 2 ret,AppParam unix:498 3 action], resolvedArgs = [BI@(499:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])])], parent = LamBody [hnd,ret,action] @hhandle(whoami/@tag, hnd, ret, action)}
Evaluating: hnd unix:496:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:497 2 ret,AppParam unix:498 3 action], resolvedArgs = [BI@(499:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]),T@analysis/benchmarks/handlers/unix/#whoami/@tag], parent = LamBody [hnd,ret,action] @hhandle(whoami/@tag, hnd, ret, action)}
Evaluating: ret unix:497:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:498 3 action], resolvedArgs = [BI@(499:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]),T@analysis/benchmarks/handlers/unix/#whoami/@tag,B@(hnd:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])])], parent = LamBody [hnd,ret,action] @hhandle(whoami/@tag, hnd, ret, action)}
Evaluating: action unix:498:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(499:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]),T@analysis/benchmarks/handlers/unix/#whoami/@tag,B@(hnd:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]),B@(ret:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])])], parent = LamBody [hnd,ret,action] @hhandle(whoami/@tag, hnd, ret, action)}
OPS analysis/benchmarks/handlers/unix/whoami fvs: BEnv (fromList [action6,iev@2567,user]):[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])] unix:493
Rebinding: fromList [iev@2567,user] from [a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])] to [a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Rebinding: fromList [action6,user] from [delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])] to [a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]
Rebinding: fromList [action6,user] from [delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])] to [delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
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
})) unix:873:[delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: fn(@action){
  su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
        (local-set(user, u));
      }))))), (fn(@res){
      @res;
    }), @action);
} unix:874:[delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
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
} unix:875:[delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(874:[delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = LamBody [] (fn(@action){
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
Rebinding: fromList [user] from [delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])] to [a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
      (local-set(user, u));
    }))))), (fn(@res){
    @res;
  }), @action) unix:876:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: su/@handle unix:877:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: su/@handle unix:881:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: forall<a,e,b> fn(hnd, ret, action){
  @hhandle(su/@tag, hnd, ret, action);
} unix:65:[top]@[]
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
  })))) unix:878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: @Hnd-su unix:882:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: @Hnd-su unix:885:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:883 0 1,AppParam unix:884 1 @open(clause-tail1)((fn(u){
  (local-set(user, u));
}))], resolvedArgs = [], parent = AppParam unix:878 0 @Hnd-su(1, (@open(clause-tail1)((fn(u){
    (local-set(user, u));
  }))))}
Evaluating: 1 unix:883:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:884 1 @open(clause-tail1)((fn(u){
  (local-set(user, u));
}))], resolvedArgs = [BI@(885:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = AppParam unix:878 0 @Hnd-su(1, (@open(clause-tail1)((fn(u){
    (local-set(user, u));
  }))))}
Evaluating: @open(clause-tail1)((fn(u){
  (local-set(user, u));
})) unix:884:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: clause-tail1 unix:890:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: clause-tail1 unix:892:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:888 0 fn(u){
  local-set(user, u);
}], resolvedArgs = [], parent = AppParam unix:884 1 @open(clause-tail1)((fn(u){
  (local-set(user, u));
}))}
Evaluating: fn(u){
  local-set(user, u);
} unix:888:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(892:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = AppParam unix:884 1 @open(clause-tail1)((fn(u){
  (local-set(user, u));
}))}
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(885:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]),BI@(883:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = AppParam unix:878 0 @Hnd-su(1, (@open(clause-tail1)((fn(u){
    (local-set(user, u));
  }))))}
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:879 1 fn(@res){
  @res;
},AppParam unix:880 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#su/@handle], parent = LamBody [@action] su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
      (local-set(user, u));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: fn(@res){
  @res;
} unix:879:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:880 2 @action], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#su/@handle,BI@(878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = LamBody [@action] su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
      (local-set(user, u));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @action unix:880:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#su/@handle,BI@(878:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]),BI@(879:[a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = LamBody [@action] su/@handle((@Hnd-su(1, (@open(clause-tail1)((fn(u){
      (local-set(user, u));
    }))))), (fn(@res){
    @res;
  }), @action)}
Evaluating: @hhandle(su/@tag, hnd, ret, action) unix:620:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: @hhandle unix:621:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: @hhandle unix:626:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:622 0 su/@tag,AppParam unix:623 1 hnd,AppParam unix:624 2 ret,AppParam unix:625 3 action], resolvedArgs = [], parent = LamBody [hnd,ret,action] @hhandle(su/@tag, hnd, ret, action)}
Evaluating: su/@tag unix:622:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: @open(@new-htag)("su@unix") unix:63:[top]@[]
Evaluating: @new-htag unix:616:[top]@[]
Evaluating: @new-htag unix:618:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:614 0 "su@unix"], resolvedArgs = [], parent = DefNonRec // runtime tag for the effect `:su`
pub val su/@tag : hnd/htag<analysis/benchmarks/handlers/unix/su>;}
Evaluating: "su@unix" unix:614:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(618:[top]@[])], parent = DefNonRec // runtime tag for the effect `:su`
pub val su/@tag : hnd/htag<analysis/benchmarks/handlers/unix/su>;}
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:623 1 hnd,AppParam unix:624 2 ret,AppParam unix:625 3 action], resolvedArgs = [BI@(626:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = LamBody [hnd,ret,action] @hhandle(su/@tag, hnd, ret, action)}
Evaluating: hnd unix:623:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:624 2 ret,AppParam unix:625 3 action], resolvedArgs = [BI@(626:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]),T@analysis/benchmarks/handlers/unix/#su/@tag], parent = LamBody [hnd,ret,action] @hhandle(su/@tag, hnd, ret, action)}
Evaluating: ret unix:624:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:625 3 action], resolvedArgs = [BI@(626:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]),T@analysis/benchmarks/handlers/unix/#su/@tag,B@(hnd:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = LamBody [hnd,ret,action] @hhandle(su/@tag, hnd, ret, action)}
Evaluating: action unix:625:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(626:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]),T@analysis/benchmarks/handlers/unix/#su/@tag,B@(hnd:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]),B@(ret:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = LamBody [hnd,ret,action] @hhandle(su/@tag, hnd, ret, action)}
OPS analysis/benchmarks/handlers/unix/su fvs: BEnv (fromList [action6,user]):[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])] unix:620
Rebinding: fromList [user] from [a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])] to [a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Rebinding: fromList [action6] from [delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])] to [a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Rebinding: fromList [action6] from [delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])] to [delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: (fn(){
  @mask-builtin((fn(){
    (action6());
  }));
})() unix:903:[delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: fn(){
  @mask-builtin((fn(){
    (action6());
  }));
} unix:904:[delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [] (fn(){
  @mask-builtin((fn(){
    (action6());
  }));
})()}
Rebinding: fromList [action6] from [delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])] to [a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: @mask-builtin((fn(){
  (action6());
})) unix:905:[a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: fn(){
  action6();
} unix:907:[a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Applying FMask
Evaluating: action6() unix:909:[a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: action6 unix:910:[a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = LamBody [] action6()}
Evaluating: val _ : ()
      = @open(su)(Alice);
@open(echo)((@open(whoami)())) unix:923:[a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: @open(su)(Alice) unix:925:[a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: su unix:941:[a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: fn(u){
  @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> su/@select), u);
} unix:71:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:939 0 Alice], resolvedArgs = [], parent = LetDef val _ : ();}
Evaluating: Alice unix:939:[a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/su], parent = LetDef val _ : ();}
Evaluating: @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> su/@select), u) unix:641:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: @perform1 unix:642:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: @perform1 unix:646:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:643 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam unix:644 1 forall<e,a> su/@select,AppParam unix:645 2 u], resolvedArgs = [], parent = LamBody [u] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> su/@select), u)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) unix:643:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: @evv-at unix:650:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: @evv-at unix:652:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:648 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam unix:643 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) unix:648:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: @make-ssize_t unix:656:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:654 0 0], resolvedArgs = [], parent = AppParam unix:648 0 @open(@make-ssize_t)(0)}
Evaluating: 0 unix:654:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(656:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])])], parent = AppParam unix:648 0 @open(@make-ssize_t)(0)}
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(652:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])])], parent = AppParam unix:643 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:644 1 forall<e,a> su/@select,AppParam unix:645 2 u], resolvedArgs = [BI@(646:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])])], parent = LamBody [u] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> su/@select), u)}
Evaluating: forall<e,a> su/@select unix:644:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: su/@select unix:660:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-su(_, (@ctl-su)) : analysis/benchmarks/handlers/unix/su<e,a> )
       -> @ctl-su;
  });
} unix:69:[top]@[]
Applying FApp {totalArgs = 3, leftArgs = [AppParam unix:645 2 u], resolvedArgs = [BI@(646:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]),BI@(643:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])])], parent = LamBody [u] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> su/@select), u)}
Evaluating: u unix:645:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]
Applying FApp {totalArgs = 3, leftArgs = [], resolvedArgs = [BI@(646:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]),BI@(643:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]),T@analysis/benchmarks/handlers/unix/#su/@select], parent = LamBody [u] @perform1((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> su/@select), u)}
Evaluating: local-set(user, u) unix:893:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: local-set unix:894:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: local-set unix:897:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:895 0 user,AppParam unix:896 1 u], resolvedArgs = [], parent = LamBody [u] local-set(user, u)}
Evaluating: user unix:895:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:896 1 u], resolvedArgs = [BI@(897:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = LamBody [u] local-set(user, u)}
Evaluating: u unix:896:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(897:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]),B@(user:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = LamBody [u] local-set(user, u)}
LocalSet: std/core/types/local-set std/core/types/local-set
[Root,Alice]
[B@(user:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]),B@(u:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])]
Applying FHLink {linkEff = analysis/benchmarks/handlers/unix/whoami, doCtx = unix:893, hCtx = unix:831, linkKnext = AI@(893:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]), linkHnd = Handler {ops = B@(hnd:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]), ret = Just AppParam unix:843 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,iev@2567,user])}}
Rebinding: fromList [action6,iev@2567,user] from [a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])] to [a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FResume {label = analysis/benchmarks/handlers/unix/su, vaddr = AI@(641:[a925,a909,a903,delim]@[(unix:620,[a876,a873,delim]),(unix:493,[a840,a837,delim])]), rHnd = Handler {ops = B@(hnd:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]), ret = Just AppParam unix:879 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,user])}, rCtx = unix:893}
Rebinding: fromList [action6,user] from [a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])] to [a893,a876,a873,delim]@[(unix:831,[a840,a837,delim]),(unix:893,[a893,delim])]
Applying FLet {groupIdx = 0, numGroups = 1, bindingIdx = 0, numBindings = 1, name = _, resolved = [], parent = LamBody [] val _ : ()
      = @open(su)(Alice);
@open(echo)((@open(whoami)()))}
Evaluating: @open(echo)((@open(whoami)())) unix:926:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Evaluating: echo unix:930:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Evaluating: fn(s){
  @open(write)(stdout, s);
} unix:17:[top]@[]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:928 0 @open(whoami)()], resolvedArgs = [], parent = LetBody @open(echo)((@open(whoami)()))}
Evaluating: @open(whoami)() unix:928:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Evaluating: whoami unix:935:[a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Evaluating: fn(){
  @perform0((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> whoami/@select));
} unix:55:[top]@[]
Applying FApp {totalArgs = 0, leftArgs = [], resolvedArgs = [], parent = AppParam unix:928 0 @open(whoami)()}
Evaluating: @perform0((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> whoami/@select)) unix:514:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Evaluating: @perform0 unix:515:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Evaluating: @perform0 unix:518:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:516 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam unix:517 1 forall<e,a> whoami/@select], resolvedArgs = [], parent = LamBody [] @perform0((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> whoami/@select))}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) unix:516:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Evaluating: @evv-at unix:522:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Evaluating: @evv-at unix:524:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:520 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam unix:516 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) unix:520:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Evaluating: @make-ssize_t unix:528:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:526 0 0], resolvedArgs = [], parent = AppParam unix:520 0 @open(@make-ssize_t)(0)}
Evaluating: 0 unix:526:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(528:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])])], parent = AppParam unix:520 0 @open(@make-ssize_t)(0)}
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(524:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])])], parent = AppParam unix:516 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:517 1 forall<e,a> whoami/@select], resolvedArgs = [BI@(518:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])])], parent = LamBody [] @perform0((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> whoami/@select))}
Evaluating: forall<e,a> whoami/@select unix:517:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Evaluating: whoami/@select unix:532:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-whoami(_, (@fun-whoami)) : analysis/benchmarks/handlers/unix/whoami<e,a> )
       -> @fun-whoami;
  });
} unix:53:[top]@[]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(518:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]),BI@(516:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])])], parent = LamBody [] @perform0((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> whoami/@select))}
Evaluating: @open(user/show)((local-get(user, iev@2567))) unix:857:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: user/show unix:861:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
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
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:859 0 local-get(user, iev@2567)], resolvedArgs = [], parent = LamBody [] @open(user/show)((local-get(user, iev@2567)))}
Evaluating: local-get(user, iev@2567) unix:859:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: local-get unix:864:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: local-get unix:867:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:865 0 user,AppParam unix:866 1 iev@2567], resolvedArgs = [], parent = AppParam unix:859 0 local-get(user, iev@2567)}
Evaluating: user unix:865:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:866 1 iev@2567], resolvedArgs = [BI@(867:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = AppParam unix:859 0 local-get(user, iev@2567)}
Evaluating: iev@2567 unix:866:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(867:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]),B@(user:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])], parent = AppParam unix:859 0 local-get(user, iev@2567)}
LocalGet: std/core/types/local-get std/core/types/local-get
B@(user:[a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])])
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/#user/show], parent = LamBody [] @open(user/show)((local-get(user, iev@2567)))}
Evaluating: match (user) {
  (Root() : analysis/benchmarks/handlers/unix/user )
     -> "root";
  (Alice() : analysis/benchmarks/handlers/unix/user )
     -> "alice";
  (@skip Bob() : analysis/benchmarks/handlers/unix/user )
     -> "bob";
} unix:472:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: user unix:473:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
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
Evaluating: "alice" unix:475:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FResume {label = analysis/benchmarks/handlers/unix/whoami, vaddr = IL@(514:whoami:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]), rHnd = Handler {ops = B@(hnd:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]), ret = Just AppParam unix:843 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,iev@2567,user])}, rCtx = unix:857}
Rebinding: fromList [action6,iev@2567,user] from [a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])] to [a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Evaluating: "root" unix:474:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FResume {label = analysis/benchmarks/handlers/unix/whoami, vaddr = IL@(514:whoami:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]), rHnd = Handler {ops = B@(hnd:[a840,a837,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])]), ret = Just AppParam unix:843 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,iev@2567,user])}, rCtx = unix:857}
Rebinding: fromList [action6,iev@2567,user] from [a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])] to [a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]
Applying FHLink {linkEff = analysis/benchmarks/handlers/unix/su, doCtx = unix:514, hCtx = unix:893, linkKnext = AI@(514:[a928,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:831,[a840,a837,delim])]), linkHnd = Handler {ops = B@(hnd:[a876,a873,delim]@[(unix:493,[a840,a837,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]), ret = Just AppParam unix:879 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action6,user])}}
Rebinding: fromList [action6,user] from [a893,a876,a873,delim]@[(unix:831,[a840,a837,delim]),(unix:893,[a893,delim])] to [a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/echo], parent = LetBody @open(echo)((@open(whoami)()))}
Evaluating: @open(write)(stdout, s) unix:187:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Evaluating: write unix:192:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Evaluating: fn(fd, s){
  @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s);
} unix:13:[top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:189 0 stdout,AppParam unix:190 1 s], resolvedArgs = [], parent = LamBody [s] @open(write)(stdout, s)}
Evaluating: stdout unix:189:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Evaluating: 0 unix:15:[top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:190 1 s], resolvedArgs = [T@analysis/benchmarks/handlers/unix/write], parent = LamBody [s] @open(write)(stdout, s)}
Evaluating: s unix:190:[a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [T@analysis/benchmarks/handlers/unix/write,T@analysis/benchmarks/handlers/unix/stdout], parent = LamBody [s] @open(write)(stdout, s)}
Evaluating: @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s) unix:163:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Evaluating: @perform2 unix:164:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Evaluating: @perform2 unix:169:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:165 0 @open(@evv-at)((@open(@make-ssize_t)(0))),AppParam unix:166 1 forall<e,a> write/@select,AppParam unix:167 2 fd,AppParam unix:168 3 s], resolvedArgs = [], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: @open(@evv-at)((@open(@make-ssize_t)(0))) unix:165:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Evaluating: @evv-at unix:173:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Evaluating: @evv-at unix:175:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:171 0 @open(@make-ssize_t)(0)], resolvedArgs = [], parent = AppParam unix:165 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Evaluating: @open(@make-ssize_t)(0) unix:171:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Evaluating: @make-ssize_t unix:179:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Applying FApp {totalArgs = 1, leftArgs = [AppParam unix:177 0 0], resolvedArgs = [], parent = AppParam unix:171 0 @open(@make-ssize_t)(0)}
Evaluating: 0 unix:177:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(179:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])])], parent = AppParam unix:171 0 @open(@make-ssize_t)(0)}
Applying FApp {totalArgs = 1, leftArgs = [], resolvedArgs = [BI@(175:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])])], parent = AppParam unix:165 0 @open(@evv-at)((@open(@make-ssize_t)(0)))}
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:166 1 forall<e,a> write/@select,AppParam unix:167 2 fd,AppParam unix:168 3 s], resolvedArgs = [BI@(169:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])])], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: forall<e,a> write/@select unix:166:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Evaluating: write/@select unix:183:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Evaluating: forall<e,a> fn(hnd){
  (match (hnd) {
    (@skip @Hnd-bio(_, (@fun-write)) : analysis/benchmarks/handlers/unix/bio<e,a> )
       -> @fun-write;
  });
} unix:11:[top]@[]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:167 2 fd,AppParam unix:168 3 s], resolvedArgs = [BI@(169:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]),BI@(165:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])])], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: fd unix:167:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Applying FApp {totalArgs = 4, leftArgs = [AppParam unix:168 3 s], resolvedArgs = [BI@(169:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]),BI@(165:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]),T@analysis/benchmarks/handlers/unix/#write/@select], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: s unix:168:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]
Applying FApp {totalArgs = 4, leftArgs = [], resolvedArgs = [BI@(169:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]),BI@(165:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])]),T@analysis/benchmarks/handlers/unix/#write/@select,B@(fd:[a187,a926,a909,a903,delim]@[(unix:893,[a893,a876,a873,delim]),(unix:857,[a857,a840,a837,delim])])], parent = LamBody [fd,s] @perform2((@open(@evv-at)((@open(@make-ssize_t)(0)))), (forall<e,a> write/@select), fd, s)}
Evaluating: local-set(buf, (@open((++))((local-get(buf, iev@671)), s))) unix:232:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: local-set unix:233:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: local-set unix:236:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:234 0 buf,AppParam unix:235 1 @open((++))((local-get(buf, iev@671)), s)], resolvedArgs = [], parent = LamBody [fd,s] local-set(buf, (@open((++))((local-get(buf, iev@671)), s)))}
Evaluating: buf unix:234:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:235 1 @open((++))((local-get(buf, iev@671)), s)], resolvedArgs = [BI@(236:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [fd,s] local-set(buf, (@open((++))((local-get(buf, iev@671)), s)))}
Evaluating: @open((++))((local-get(buf, iev@671)), s) unix:235:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: (++) unix:242:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: fn(x, y){
  @open((@extern-x++))(x, y);
} types:1602:[top]@[]
Applying FApp {totalArgs = 2, leftArgs = [AppParam unix:239 0 local-get(buf, iev@671),AppParam unix:240 1 s], resolvedArgs = [], parent = AppParam unix:235 1 @open((++))((local-get(buf, iev@671)), s)}
Evaluating: local-get(buf, iev@671) unix:239:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: local-get unix:245:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: local-get unix:248:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
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
Evaluating: @open((@extern-x++))(x, y) types:1623:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Evaluating: (@extern-x++) types:1628:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam types:1625 0 x,AppParam types:1626 1 y], resolvedArgs = [], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Evaluating: x types:1625:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [AppParam types:1626 1 y], resolvedArgs = [BI@(1628:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Evaluating: y types:1626:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(1628:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),B@(x:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [x,y] @open((@extern-x++))(x, y)}
Applying FApp {totalArgs = 2, leftArgs = [], resolvedArgs = [BI@(236:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),B@(buf:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])], parent = LamBody [fd,s] local-set(buf, (@open((++))((local-get(buf, iev@671)), s)))}
LocalSet: std/core/types/local-set std/core/types/local-set
[string -> "",string -> "root"]
[B@(buf:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]),BI@(1623:[a235,a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])])]
Applying FResume {label = analysis/benchmarks/handlers/unix/bio, vaddr = IL@(163:write:[a857,a840,a837,delim]@[(unix:893,[a893,delim]),(unix:831,[a1615,a824,a917,a265,a257,delim])]), rHnd = Handler {ops = B@(hnd:[a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])]), ret = Just AppParam unix:218 1 fn(@res){
  @res;
}, henv = BEnv (fromList [action1,buf,iev@671,iev@720])}, rCtx = unix:232}
Rebinding: fromList [action1,buf,iev@671,iev@720] from [a215,a212,delim]@[(unix:206,[a1615,a197,a913,top])] to [a232,a215,a212,delim]@[(unix:232,[a232,delim]),(unix:206,[a1615,a197,a913,top])]
Applying FHLink {linkEff = user, doCtx = unix:163, hCtx = unix:893, linkKnext = IL@(163:write:[a893,a876,a873,delim]@[(unix:857,[a857,a840,a837,delim]),(unix:893,[a893,delim])]), linkHnd = Handler {ops = BI@(834:[a1615,a824,a917,a265,a257,delim]@[(unix:142,[a215,a212,delim]),(unix:206,[a1615,a197,a913,top])]), ret = Nothing, henv = BEnv (fromList [action6,iev@2567,user])}}
Rebinding: fromList [action6,iev@2567,user] from [a893,delim]@[(unix:831,[a1615,a824,a917,a265,a257,delim]),(unix:142,[a215,a212,delim])] to [a893,delim]@[(unix:232,[a232,a215,a212,delim]),(unix:232,[a232,delim])]
Failed to compile analysis/benchmarks/handlers/unix.kk
