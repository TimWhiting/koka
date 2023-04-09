[DefRec [Def {defBinder = ValueBinder {binderName = show, binderType = (), binderExpr = 
  Ann (Lam [ValueBinder {binderName = .this, binderType = Nothing, binderExpr = Nothing, binderNameRange = (4,
            1), binderRange = (4,
            1)
          },
  ValueBinder {binderName = show11, binderType = Nothing, binderExpr = Nothing, binderNameRange = (4,
            1), binderRange = (4,
            1)
          }
        ] 
  (Case (Var .this False (4,
        1)) [Branch {branchPattern = PatCon samples/basic/generated/One 
  [(Nothing,PatVar (ValueBinder {binderName = o1, binderType = Nothing, binderExpr = PatWild (5,
                3), binderNameRange = (5,
                3), binderRange = (5,
                3)
              })),
  (Nothing,PatVar (ValueBinder {binderName = o2, binderType = Nothing, binderExpr = PatWild (5,
                3), binderNameRange = (5,
                3), binderRange = (5,
                3)
              }))
            ] 
  (5,
            3) (5,
            3), branchGuards = [Guard {guardTest = Var std/core/types/True False (1,
                0), guardExpr = App (Var (++) False (5,
                3)) 
  [(Nothing,Lit (LitString "One(" (5,
                  3))),(Nothing,App (Var (++) False (5,
                  3)) [(Nothing,App (Var (++) False (5,
                    3)) [(Nothing,Lit (LitString "o1: " (5,
                      3))),
  (Nothing,App (Var show False (5,
                      3)) [(Nothing,Var o1 False (5,
                        3)),(Nothing,Var show11 False (5,
                        3))
                      ] (5,
                      3))
                    ] (5,
                    3)),(Nothing,App (Var (++) False (5,
                    3)) 
  [(Nothing,Lit (LitString ", " (5,
                      3))),(Nothing,App (Var (++) False (5,
                      3)) [(Nothing,App (Var (++) False (5,
                        3)) [(Nothing,Lit (LitString "o2: " (5,
                          3))),
  (Nothing,App (Var show False (5,
                          3)) [(Nothing,Var o2 False (5,
                            3)),(Nothing,Var show11 False (5,
                            3))
                          ] (5,
                          3))
                        ] (5,
                        3)),(Nothing,Lit (LitString ")" (5,
                        3)))
                      ] (5,
                      3))
                    ] 
  (5,
                    3))
                  ] (5,
                  3))
                ] (5,
                3)
              }
            ]
          }
        ] (4,
        1)) (4,
        1)) (TForall [TypeVar {typevarId = 11, typevarKind = KCon V, typevarFlavour = Bound
          },TypeVar {typevarId = 1, typevarKind = KCon E, 
  typevarFlavour = Bound
          }
        ] [] (TFun [(.this,TApp (TCon (TypeCon {typeconName = samples/basic/generated/one, typeconKind = KApp (KApp (KCon (->)) (KCon V)) (KCon V)
          })) 
  [TVar (TypeVar {typevarId = 11, typevarKind = KCon V, typevarFlavour = Bound
            })
          ]),(show11,TFun [(.tshow11,TVar (TypeVar {typevarId = 11, typevarKind = KCon V, typevarFlavour = Bound
            }))
          ]
   (TVar (TypeVar {typevarId = 1, typevarKind = KCon E, typevarFlavour = Bound
          })) (TCon (TypeCon {typeconName = std/core/types/string, typeconKind = KCon V
          })))
        ]
    (TVar (TypeVar {typevarId = 1, typevarKind = KCon E, typevarFlavour = Bound
        })) (TCon (TypeCon {typeconName = std/core/types/string, typeconKind = KCon V
        })))) (4,
        1),
     binderNameRange = (4,
        1), binderRange = (4,
        1)
      }, defRange = (4,
      1), defVis = Public, defSort = fun, defInline = inline, 
     defDoc = "// Automatically generated. Shows a string representation of the `one` type.\n"
    }
  ],
     
DefRec [Def {defBinder = ValueBinder {binderName = show, binderType = (), binderExpr = 
  Ann (Lam [ValueBinder {binderName = .this, binderType = Nothing, binderExpr = Nothing, binderNameRange = (7,
            1), binderRange = (7,
            1)
          },
  ValueBinder {binderName = show12, binderType = Nothing, binderExpr = Nothing, binderNameRange = (7,
            1), binderRange = (7,
            1)
          }
        ] 
  (Case (Var .this False (7,
        1)) [Branch {branchPattern = PatCon samples/basic/generated/Int 
  [(Nothing,PatVar (ValueBinder {binderName = i, binderType = Nothing, binderExpr = PatWild (8,
                3), binderNameRange = (8,
                3), binderRange = (8,
                3)
              })),
(Nothing,PatVar (ValueBinder {binderName = t, binderType = Nothing, binderExpr = PatWild (8,
                3), binderNameRange = (8,
                3), binderRange = (8,
                3)
              }))
            ] (8,
            3) (8,
            3), 
branchGuards = [Guard {guardTest = Var std/core/types/True False (1,
                0), 
guardExpr = App (Var (++) False (8,
                3)) [(Nothing,Lit (LitString "Int(" (8,
                  3))),(Nothing,App (Var (++) False (8,
                  3))
 [(Nothing,App (Var (++) False (8,
                    3)) [(Nothing,Lit (LitString "i: " (8,
                      3))),(Nothing,App (Var show False (8,
                      3)) 
 [(Nothing,Var i False (8,
                        3))
                      ] (8,
                      3))
                    ] (8,
                    3)),(Nothing,App (Var (++) False (8,
                    3)) [(Nothing,Lit (LitString ", " (8,
                      3))),(Nothing,App (Var (++) False (8,
                      3)) 
 [(Nothing,App (Var (++) False (8,
                        3)) [(Nothing,Lit (LitString "t: " (8,
                          3))),(Nothing,App (Var show12 False (8,
                          3)) [(Nothing,Var t False (8,
                            3))
                          ] (8,
                          3))
                        ] (8,
                        3)),
 (Nothing,Lit (LitString ")" (8,
                        3)))
                      ] (8,
                      3))
                    ] (8,
                    3))
                  ] (8,
                  3))
                ] (8,
                3)
              }
            ]
          },
Branch {branchPattern = PatCon samples/basic/generated/Other3 [(Nothing,PatVar (ValueBinder {binderName = o, binderType = Nothing, binderExpr = PatWild (13,
                3),
 binderNameRange = (13,
                3), binderRange = (13,
                3)
              }))
            ] (13,
            3) (13,
            3), branchGuards = [Guard {guardTest = Var std/core/types/True False (1,
                0), 
 guardExpr = App (Var (++) False (13,
                3)) [(Nothing,Lit (LitString "Other3(" (13,
                  3))),(Nothing,App (Var (++) False (13,
                  3)) [(Nothing,App (Var (++) False (13,
                    3))
  [(Nothing,Lit (LitString "o: " (13,
                      3))),(Nothing,App (Var show False (13,
                      3)) [(Nothing,Var o False (13,
                        3)),(Nothing,Var show12 False (13,
                        3))
                      ] (13,
                      3))
                    ] (13,
                    3)),
  (Nothing,Lit (LitString ")" (13,
                    3)))
                  ] (13,
                  3))
                ] (13,
                3)
              }
            ]
          }
        ] (7,
        1)) (7,
        1)) (TForall [TypeVar {typevarId = 12, typevarKind = KCon V, typevarFlavour = Bound
          },
  TypeVar {typevarId = 1, typevarKind = KCon E, typevarFlavour = Bound
          }
        ] [] (TFun [(.this,TApp (TCon (TypeCon {typeconName = samples/basic/generated/other, typeconKind =
     KApp (KApp (KCon (->)) (KCon V)) (KCon V)
          })) [TVar (TypeVar {typevarId = 12, typevarKind = KCon V, typevarFlavour = Bound
            })
          ]),(show12,TFun
      [(.tshow12,TVar (TypeVar {typevarId = 12, typevarKind = KCon V, typevarFlavour = Bound
            }))
          ] (TVar (TypeVar {typevarId = 1, typevarKind = KCon E, typevarFlavour = Bound
          })) 
      (TCon (TypeCon {typeconName = std/core/types/string, typeconKind = KCon V
          })))
        ] (TVar (TypeVar {typevarId = 1, typevarKind = KCon E, typevarFlavour = Bound
        })) 
      (TCon (TypeCon {typeconName = std/core/types/string, typeconKind = KCon V
        })))) (7,
        1), binderNameRange = (7,
        1), binderRange = (7,
        1)
      }, defRange = (7,
      1), defVis = Public, defSort = fun, defInline = inline, defDoc = "// Automatically generated. Shows a string representation of the `other` type.\n"
    }
  ]
]