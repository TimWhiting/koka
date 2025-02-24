------------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Resolve operator expressions according to their fixity.
-}
-----------------------------------------------------------------------------

module Static.FixityResolve( fixityResolve
                           , Fixities, findFixity, fixitiesEmpty, fixitiesCompose
                           , fixitiesNew
                           , resolve
                           )
                           where

-- import Lib.Trace
import Control.Applicative
import Control.Monad
import qualified Common.NameMap as M
import Lib.PPrint
import Common.Failure( failure )
import Common.NamePrim( nameOpExpr )
import Common.Name
import Common.ColorScheme( ColorScheme )
import Common.Error
import Common.Range
import Common.Syntax
import Syntax.Syntax

fixityResolve :: ColorScheme -> Fixities -> UserProgram -> Error b (UserProgram,Fixities)
fixityResolve cscheme fixMap (Program source modName nameRange tdgroups defs importdefs externals fixdefs doc)
  = let fixMap1 = fixitiesCompose fixMap (extractFixMap fixdefs)
    in  do defs1 <- runFixM fixMap1 (resolveDefs defs)
           tdgroups1 <- runFixM fixMap1 (resolveTypeDefs tdgroups)  -- for lazy constructors
           return (Program source modName nameRange tdgroups1 defs1 importdefs externals fixdefs doc,fixMap1)

extractFixMap :: [FixDef] -> Fixities
extractFixMap fixDefs
  = fixitiesNew (concatMap extractFix fixDefs)
  where
    extractFix (FixDef name fixity range vis)
      = [(name,fixity)]


{--------------------------------------------------------------------------
  Resolve lazy constructor definitions
--------------------------------------------------------------------------}
resolveTypeDefs :: TypeDefGroups UserType UserKind -> FixM (TypeDefGroups UserType UserKind)
resolveTypeDefs tdefs
  = mapM resolveTypeDefGroup tdefs

resolveTypeDefGroup (TypeDefRec tdefs)
  = do defs' <- mapM resolveTypeDef tdefs
       return (TypeDefRec defs')
resolveTypeDefGroup (TypeDefNonRec tdef)
  = resolveTypeDef tdef >>= return . TypeDefNonRec


resolveTypeDef :: UserTypeDef -> FixM UserTypeDef
resolveTypeDef tdef@(DataType{ typeDefConstrs = constrs })
  = do constrs' <- mapM resolveConstr constrs
       return (tdef{ typeDefConstrs = constrs' })
resolveTypeDef tdef
  = return tdef

resolveConstr :: UserUserCon -> FixM UserUserCon
resolveConstr con@(UserCon{userConLazy = Just (fip,expr) })
  = do expr' <- resolveExpr expr
       return (con{ userConLazy = Just(fip,expr') })
resolveConstr con
  = return con


{--------------------------------------------------------------------------
  Rewrite syntax tree
--------------------------------------------------------------------------}
resolveDefs :: DefGroups UserType -> FixM (DefGroups UserType)
resolveDefs defs
  = mapM resolveDefGroup defs

resolveDefGroup (DefRec defs)
  = do defs' <- mapM resolveDef defs
       return (DefRec defs')
resolveDefGroup (DefNonRec def)
  = resolveDef def >>= return . DefNonRec

resolveDef def
  = do binder' <- resolveBinder (defBinder def)
       return def{ defBinder = binder'}

resolveBinder binder
  = do expr' <- resolveExpr (binderExpr binder)
       return (binder{ binderExpr = expr' })

resolveBinderMaybe binder
  = do mbExpr <- case (binderExpr binder) of
                   Just expr -> resolveExpr expr >>= return . Just
                   Nothing   -> return Nothing
       return (binder{ binderExpr = mbExpr })

resolveExpr :: UserExpr -> FixM UserExpr
resolveExpr expr
  = case expr of
      Lam    binds expr rng  -> do binds' <- mapM resolveBinderMaybe binds
                                   expr' <- resolveExpr expr
                                   return (Lam binds' expr' rng)
      Let    defs expr range -> do defs' <- resolveDefGroup defs
                                   expr' <- resolveExpr expr
                                   return (Let defs' expr' range)
      Bind   def expr range  -> do def' <- resolveDef def
                                   expr' <- resolveExpr expr
                                   return (Bind def' expr' range)
      App    fun nargs range -> do fun' <- resolveExpr fun
                                   let (names,args) = unzip nargs
                                   args' <- mapM resolveExpr args
                                   let nargs' = zip names args'
                                   case fun of
                                     Var name _ _ | name == nameOpExpr
                                       -> resolve args'
                                     _ -> return (App fun' nargs' range)
      Var    name isOp range -> return expr
      Lit    lit             -> return expr
      Ann    expr tp range   -> do expr' <- resolveExpr expr
                                   return (Ann expr' tp range)
      Case   expr brs lazy range  -> do expr' <- resolveExpr expr
                                        brs'   <- mapM resolveBranch brs
                                        return (Case expr' brs' lazy range)
      Parens expr name pre range -> do expr' <- resolveExpr expr
                                       return (Parens expr' name pre range)
      Handler shallow scoped override allowMask eff pars reinit ret final ops hrng rng
                             -> do ret' <- resolveExprMaybe ret
                                   reinit' <- resolveExprMaybe reinit
                                   final' <- resolveExprMaybe final
                                   ops' <- mapM resolveHandlerBranch ops
                                   return (Handler shallow scoped override allowMask eff pars reinit' ret' final' ops' hrng rng)
      Inject tp expr b range -> do expr' <- resolveExpr expr
                                   return (Inject tp expr' b range)

resolveExprMaybe Nothing  = return Nothing
resolveExprMaybe (Just x) = do x' <- resolveExpr x
                               return (Just x')

isJust (Just _) = True
isJust Nothing  = False

resolveBranch (Branch pattern guards)
  = do guards' <- mapM resolveGuard guards
       return (Branch pattern guards')

resolveGuard (Guard test expr)
  = do test' <- resolveExpr test
       expr' <- resolveExpr expr
       return (Guard test' expr')

resolveHandlerBranch hb@(HandlerBranch{ hbranchExpr=expr })
  = do expr'   <- resolveExpr expr
       return hb{ hbranchExpr = expr' }

{--------------------------------------------------------------------------
  Fixity map for all operators
--------------------------------------------------------------------------}
type Fixities = M.NameMap Fixity

fixitiesEmpty :: Fixities
fixitiesEmpty
  = M.empty

findFixity :: Fixities -> Name -> Fixity
findFixity fixities name
  = case M.lookup name fixities of
      Just (fix) -> fix
      Nothing    -> FixInfix 50 AssocNone


fixitiesCompose :: Fixities -> Fixities -> Fixities
fixitiesCompose fix1 fix2
  = M.unionWith compose fix2 fix1
  where
    compose f1 f2
      = case (f1,f2) of
          (_, FixInfix _ _) -> f2
          (FixInfix  _ _,_) -> f1
          _                 -> f2

fixitiesNew :: [(Name,Fixity)] -> Fixities
fixitiesNew fs
  = M.fromList [(name,f) | (name,f@(FixInfix _ _)) <- fs]

-- The fixity monad collects error messages and passes a fixity map
data FixM a = FixM (Fixities -> Res a)
data Res a  = Res !a ![(Range,Doc)]

runFixM :: Fixities -> FixM a -> Error b a
runFixM fixities (FixM f)
  = case f fixities of
      Res x errors -> if null errors then return x else errorMsgs [errorMessageKind ErrStatic rng doc | (rng,doc) <- errors]

instance Functor FixM where
  fmap  = liftM

instance Applicative FixM where
  pure x  = FixM (\fixmap -> Res x [])
  (<*>)   = ap

instance Monad FixM where
  -- return = pure
  (FixM fm) >>= f   = FixM (\fixmap -> case fm fixmap of
                                         Res x errs1 -> case f x of
                                                          FixM fm' -> case fm' fixmap of
                                                                        Res y errs2 -> Res y (errs1 ++ errs2))
getFixities :: FixM Fixities
getFixities
  = FixM (\fm -> Res fm [])

emitError :: Range -> Doc -> FixM ()
emitError range doc
  = FixM (\fm -> Res () [(range,doc)])

{--------------------------------------------------------------------------
  Resolve fixities:
  The algorithm is written a bit long to enable easy extension
  to prefix, postfix, and distfix operators.
--------------------------------------------------------------------------}

data Op             = Op UserExpr Fixity

data Term           = Term UserExpr
                    | Oper Op

type ExprStack      = [UserExpr]
type OpStack        = [Op]

resolve :: [UserExpr] -> FixM UserExpr
resolve exprs
  = do fixMap <- getFixities
       let terms = map (toTerm fixMap) exprs
       resolveTerms [] [] terms


-- Find out if this is an operator
toTerm :: Fixities -> UserExpr -> Term
toTerm fixities expr
  = case expr of
      Var name True _ -> Oper (Op expr (findFixity fixities name))
      _               -> Term expr


-- The real resolve algorithm uses Dijkstra's strategy with two stacks
resolveTerms :: ExprStack -> OpStack -> [Term] -> FixM UserExpr

-- final term computed
resolveTerms [x] [] []
  = return x

-- cleanup stage, apply all ops
resolveTerms xs ops@(op:_) []
  = apply xs ops []

-- always push terms
resolveTerms xs ops (Term t:tt)
  = resolveTerms (t:xs) ops tt


-- prefix operator
resolveTerms xs ops (Oper t@(Op (Var name _ _) FixPrefix):tt)
  = push xs ops tt t

-- postfix operator
resolveTerms xs ops ts@(Oper t@(Op op FixPostfix):tt)
  = push xs ops tt t

-- infix operator
resolveTerms xs ops ts@(Oper t@(Op op (FixInfix prec assoc)):tt)
    | prec > precCtx   = push xs ops tt t
    | prec < precCtx   = apply xs ops ts
    | prec == precCtx  = do{ checkAmbigious ops t
                           ; let (Op op fix) = t
                           ; if (assoc == AssocRight)
                              then push xs ops tt t
                              else apply xs ops ts
                           }
    where
      prec      = precedenceOp t
      precCtx   | null ops  = 0
                | otherwise = precedenceOp (head ops)


resolveTerms [] [] []
    = failure "Static.FixityResolve.resolveTerms: no term: fix parser"
resolveTerms xs ops ts
    = failure "Static.FixityResolve.resolveTerms: fixity resolver error"


precedenceOp (Op op fix)            = precedence fix
precedence (FixInfix prec assoc)    = prec
precedence (FixPrefix )             = 102
precedence (FixPostfix )            = 101



checkAmbigious (Op opCtx fixCtx@(FixInfix _ assocCtx):ops) (Op op fix@(FixInfix _ assoc))
    | assocCtx == AssocNone || assocCtx /= assoc
    = ambigious fixCtx fix op
checkAmbigious ops t
    = return ()

ambigious :: Fixity -> Fixity -> UserExpr -> FixM ()
ambigious fixCtx fix op
    = emitError (getRange op)
                (text "Ambigious" <+> ppFixity fix <+> text "operator" <+> opText <.> text "in a"
                  <+> ppFixity fixCtx <+> text "context" <->
                 text " hint: add parenthesis around the sub-expression to disambiguate")
    where
      opText  = case op of
                  Var name _ _  -> pretty name <.> space
                  _             -> Lib.PPrint.empty

ppFixity (FixInfix prec assoc)
  = case assoc of
      AssocNone  -> text "non-associative"
      AssocRight -> text "right-associative"
      AssocLeft  -> text "left-associative"
ppFixity (FixPrefix)
  = text "prefix"
ppFixity (FixPostfix)
  = text "postfix"

-----------------------------------------------------------
-- Helper operations: push & apply
-----------------------------------------------------------
push xs ops ts t@(Op op fix)
    = resolveTerms xs (t:ops) ts

apply xs (Op op FixPostfix:ops) ts
    = do{ ys <- applyUnaryOp op xs
        ; resolveTerms ys ops ts
        }

apply xs (Op op FixPrefix:ops) ts
    = do{ ys <- applyUnaryOp op xs
        ; resolveTerms ys ops ts
        }

apply xs (Op op (FixInfix _ _):ops) ts
    = do{ ys <- applyInfixOp op xs
        ; resolveTerms ys ops ts
        }
apply xs ops ts
    = failure "Static.FixityResolve.apply: fixity resolver failure"

applyUnaryOp op (t:ts)
  = return ((App op [(Nothing, t)] (combineRanged op t)):ts)

applyUnaryOp op ts
  = do{ emitError (getRange op)
          (text "Unary operator has not enough arguments")
      ; return ts
      }

applyInfixOp op (t1:t2:ts)
    = return ((makeApp op t2 t1 (combineRanged t1 t2)):ts)
applyInfixOp op ts
    = do{ emitError (getRange op)
                    (text "Infix operator has not enough arguments")
        ; return ts
        }

makeApp op e1 e2 r
    = App op [(Nothing,e1),(Nothing,e2)] r
