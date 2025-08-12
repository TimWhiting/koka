5c5
< module Core.FlowAnalysis.Full.DMCFAR.DMCFA where
---
> module Core.FlowAnalysis.Full.DMCFA.DMCFA where
13,15c13,15
< import Core.FlowAnalysis.Full.DMCFAR.AbstractValue
< import Core.FlowAnalysis.Full.DMCFAR.Monad
< import Core.FlowAnalysis.Full.DMCFAR.Primitives
---
> import Core.FlowAnalysis.Full.DMCFA.AbstractValue
> import Core.FlowAnalysis.Full.DMCFA.Monad
> import Core.FlowAnalysis.Full.DMCFA.Primitives
48,49c48
<         -- trace ("Value not found in store :" ++ show addr)
<         error ("Value not found in store: " ++ show addr)
---
>         trace ("Value not found in store :" ++ show addr)
53,54c52,53
<       Step (CEval expr kaddr mkaddr ctx) -> do
<         drive $ doEval expr kaddr mkaddr ctx
---
>       Step (CEval expr venv kaddr mkaddr ctx) -> do
>         drive $ doEval expr venv kaddr mkaddr ctx
74d72
< store :: HasCallStack => Addr -> FixAAMR r s e AChange
84c82
< eval expr kaddr mkaddr ctx = return $ N (CEval expr kaddr mkaddr ctx)
---
> eval expr venv kaddr mkaddr ctx = return $ N (CEval expr venv kaddr mkaddr ctx)
88,90c86,88
< allocConst :: CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
< allocConst ctx expr v = do
<   let addr = BindImplicitAddr ctx (contextId expr)
---
> allocConst :: VEnv -> CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
> allocConst env ctx expr v = do
>   let addr = BindImplicitAddr ctx (limitEnv env (fvs expr)) (contextId expr)
94,96c92,94
< allocFrame frame kaddr ctx u = do
<   let addr = ImplicitAddr ctx u
<   extendKStore addr (KNext frame ctx kaddr)
---
> allocFrame frame kaddr ctx env u = do
>   let addr = ImplicitAddr ctx env u
>   extendKStore addr (KNext frame (static ctx) kaddr)
104,114c102,104
< doEval :: HasCallStack => ExprContext -> Addr -> Addr -> CombinedCtx -> FixAAMR r s e FixChange
< doEval expr kaddr mkaddr ctx =
<   let open = case exprOfCtx expr of
<         App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen -> True
<         _ -> False 
<       process x = if not open then do 
<                     -- analysisLog ("Evaluating: " ++ showCtxExpr expr ++ " in " ++ show ctx) 
<                     x
<                   else x 
<   in 
<   process $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
---
> doEval :: HasCallStack => ExprContext -> VEnv -> Addr -> Addr -> CombinedCtx -> FixAAMR r s e FixChange
> doEval expr venv kaddr mkaddr ctx =
>   -- trace ("Evaluating: " ++ show expr ++ " in " ++ show (M.toList venv)) $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
119c109
<       eval f kaddr mkaddr ctx
---
>       eval f venv kaddr mkaddr ctx
125c115
<       eval f k' mkaddr ctx
---
>       eval f venv k' mkaddr ctx
131c121
<       eval f k' mkaddr ctx
---
>       eval f venv k' mkaddr ctx
138c128
<       addr <- allocConst ctx expr constr
---
>       addr <- allocConst venv ctx expr constr
142c132
<         addr <- allocConst ctx expr (AChangePrim name expr)
---
>         addr <- allocConst venv ctx expr (AChangePrim name expr)
146,160c136,150
<       else if qualifier (getName name) == nameNil then do
<         -- trace ("Found variable: " ++ show name ++ " at " ++ show name) $ return ()
<         apply kaddr mkaddr (BindingAddr ctx name) (dynamic ctx)
<       else do
<         res <- bindExternal name
<         case res of -- TODO: Evaluate top bindings and store them somewhere, don't re-evaluate based on kaddrs
<           Just expr -> do
<             -- trace ("Evaluating external: " ++ show name) $ return ()
<             extendMKStore (TopAddr name) MKEnd
<             c <- startCombinedCtx
<             each [eval expr EndKAddr (TopAddr name) c,
<                   apply kaddr mkaddr (BindingAddr c name) (dynamic ctx)]
<           Nothing -> do
<             -- trace ("Found variable: " ++ show name ++ " at " ++ show name) $ return ()
<             apply kaddr mkaddr (BindingAddr ctx name) (dynamic ctx)
---
>       else case lookupEnv name venv of
>         Just addr ->
>           -- trace ("Found variable: " ++ show name ++ " at " ++ show addr) $ do
>           apply kaddr mkaddr addr (dynamic ctx)
>         Nothing -> do
>           -- trace ("Evaluating external: " ++ show name) $ return ()
>           res <- bindExternal name
>           case res of -- TODO: Evaluate top bindings and store them somewhere, don't re-evaluate based on kaddrs
>             Just expr -> do
>               extendMKStore (TopAddr name) MKEnd
>               c <- startCombinedCtx
>               each [eval expr M.empty EndKAddr (TopAddr name) c,
>                     apply kaddr mkaddr (BindingAddr c name) (dynamic ctx)]
>             Nothing -> do
>               trace ("Variable not found: " ++ show name) doBottom
162c152
<       addr <- allocConst ctx expr (injLit l)
---
>       addr <- allocConst venv ctx expr (injLit l)
165c155
<       addr <- allocConst ctx expr (AChangeClos expr ctx)
---
>       addr <- allocConst venv ctx expr (AChangeClos expr venv)
173c163
<       -- let newEnv = foldl (\acc x -> M.insert (defTName x) ctx acc) venv (defsOf defGroup)
---
>       let newEnv = foldl (\acc x -> M.insert (defTName x) ctx acc) venv (defsOf defGroup)
175,177c165,167
<       -- trace ("Let binding: " ++ show defName ++ " in " ++ show ctx) $ return ()
<       k' <- addFrame (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr) (contextId bind)
<       eval bind k' mkaddr ctx
---
>       -- trace ("Let binding: " ++ show defName ++ " in " ++ show newEnv) $ return ()
>       k' <- addFrame (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr newEnv) (contextId bind)
>       eval bind (limitEnv newEnv (S.insert defName (fvs bind)) ) k' mkaddr ctx
181c171
<       eval e kaddr mkaddr ctx
---
>       eval e venv kaddr mkaddr ctx
183c173
<       addr <- allocConst ctx expr (AChangeClos expr ctx)
---
>       addr <- allocConst venv ctx expr (AChangeClos expr venv)
190c180
<       eval e kaddr mkaddr ctx
---
>       eval e venv kaddr mkaddr ctx
194,195c184,185
<       k' <- addFrame (FScrut expr branches) (contextId s)
<       eval s k' mkaddr ctx
---
>       k' <- addFrame (FScrut expr branches venv) (contextId s)
>       eval s (limitEnv venv (fvs s)) k' mkaddr ctx
198c188
<   where addFrame f u = allocFrame f kaddr ctx u
---
>   where addFrame f u = allocFrame f kaddr ctx venv u
202,203c192,193
<           k' <- addFrame (FApp (length args) argExprs [] expr) (contextId f)
<           eval f k' mkaddr ctx
---
>           k' <- addFrame (FApp (length args) argExprs [] expr venv) (contextId f)
>           eval f (limitEnv venv (fvs f)) k' mkaddr ctx
205,213c195,202
< rebindAll :: HasCallStack => S.Set TName -> CombinedCtx -> CombinedCtx -> FixAAMR r s e ()
< rebindAll fvs oldCtx newCtx = do
<   if oldCtx == newCtx || S.null fvs then return ()
<   else do
<     -- trace ("Rebinding: " ++ show fvs ++ " from " ++ show oldCtx ++ " to " ++ show newCtx) $ return ()
<     let bindings = S.toList fvs
<     mapM_ (\tname -> do
<       v <- store (BindingAddr oldCtx tname)
<       extendStore (BindingAddr newCtx tname) v) bindings
---
> mEnvOf :: AChange -> FixAAMR r s e VEnv
> mEnvOf (AChangeClos _ env) = return env
> mEnvOf (AChangeKont _ _ env _) = return env
> mEnvOf (AChangeObj _ args) = do
>   objs <- mapM (store . snd) args
>   envs <- mapM mEnvOf objs
>   return $ M.unions envs
> mEnvOf _ = return M.empty
231,233c220
<             let TopAddr tname = mkaddr
<             -- trace ("Applying top value: " ++ show addr ++ " with " ++ show topV) $ return ()
<             -- let [(tname, ctx)] = M.toList env
---
>             let TopAddr name  = mkaddr
235c222,223
<             extendStore (BindingAddr c tname) topV
---
>             -- trace ("Applying top value: " ++ show addr ++ " with " ++ show topV) $ return ()
>             extendStore (BindingAddr c name) topV
237c225
<         MKHandle _ knext mknext _ dynctx ->
---
>         MKHandle _ knext mknext _ _ dynctx ->
240,241c228,229
<       let newctx = CombinedCtx (kfvs ctx) (static ctx) dynctx
<           addFrame f u = allocFrame f knext newctx u in
---
>       let newctx = CombinedCtx ctx dynctx
>           addFrame f venv u = allocFrame f knext newctx venv u in
248,251c236,237
<               let nCtx = replaceFvs newctx (fvs e)
<               rebindAll (kfvs ctx) ctx nCtx
<               eval bod knext mkaddr nCtx
<         FApp n args res u -> do
---
>               eval bod env knext mkaddr newctx
>         FApp n args res u venv -> do
260c246
<                   AChangeClos cexpr cctx -> do
---
>                   AChangeClos cexpr cenv -> do
264c250,251
<                     let newCtx = CombinedCtx (fvs cexpr) (take m $ CallApp (contextId u) : static newctx) (dynamic newctx)
---
>                     let newCtx = CombinedCtx (take m $ CallApp (contextId u) : static newctx) (dynamic newctx)
>                     let newEnv = foldl (\acc x -> M.insert x newCtx acc) cenv args
268c255
<                       extendStore (BindingAddr newCtx a) val) args arguments
---
>                       extendStore (fromJust $ lookupEnv a newEnv) val) args arguments
270c257
<                     let ia = ImplicitAddr newCtx (contextId body)
---
>                     let ia = ImplicitAddr newCtx newEnv (contextId body)
272,273c259
<                     rebindAll (fvs cexpr) cctx newCtx
<                     eval body ia mkaddr newCtx
---
>                     eval body (limitEnv newEnv (fvs body)) ia mkaddr newCtx
276c262
<                     let addr = BindImplicitAddr newctx (contextId u)
---
>                     let addr = BindImplicitAddr newctx venv (contextId u)
279c265
<                       doHandlerPrimitive name n addr knext mkaddr arguments args ctx newctx u
---
>                       doHandlerPrimitive name n addr knext mkaddr arguments args venv newctx u
281c267
<                       res <- doPrimitive n args
---
>                       res <- doPrimitive n args venv
288c274
<                     let addr = BindImplicitAddr newctx (contextId u)
---
>                     let addr = BindImplicitAddr newctx venv (contextId u)
291c277
<                   AChangeKont label kx hctx hnd@(Handler _ _ hfvs) -> do
---
>                   AChangeKont label kx henv hnd -> do
294c280
<                     let newCtx = CombinedCtx (kfvs ctx) (take m $ CallApp (contextId u) : static newctx) (dynamic newctx)
---
>                     let newCtx = CombinedCtx (take m $ CallApp (contextId u) : static newctx) (dynamic newctx)
296,298c282,283
<                         mk' = ImplicitAddr newCtx (contextId u)
<                     rebindAll hfvs hctx newCtx
<                     extendMKStore mk' (MKHandle label knext mkaddr hnd newCtx)
---
>                         mk' = ImplicitAddr newCtx venv (contextId u)
>                     extendMKStore mk' (MKHandle label knext mkaddr hnd venv newCtx)
303,307c288,291
<               k' <- addFrame (FApp n rest (res ++ [addr]) u) (contextId next)
<               rebindAll (kfvs ctx) ctx newctx
<               eval next k' mkaddr newctx
<         FLet groupIdx numGroups bindingIdx numBindings name resolved u -> do
<           -- trace "Applying Let" $ return ()
---
>               k' <- addFrame (FApp n rest (res ++ [addr]) u (limitEnv venv (fvsl rest))) venv (contextId next)
>               eval next (limitEnv venv (fvs next)) k' mkaddr newctx
>         FLet groupIdx numGroups bindingIdx numBindings name resolved u venv -> do
>           -- trace ("Applying Let") $ return ()
309,312c293,294
<           -- trace ("Binding " ++ show name ++ " to " ++ show val ++ " in " ++ show newctx ) $ return ()
<           extendStore (BindingAddr newctx name) val
<           let newFvs = S.insert name (kfvs ctx)
<           let newCtx = replaceFvs newctx newFvs
---
>           -- trace ("Binding " ++ show name ++ " to " ++ show val ++ " in " ++ show venv ) $ return ()
>           extendStore (fromJust $ lookupEnv name venv) val
316,317c298
<             rebindAll (kfvs ctx) ctx newCtx
<             eval body knext mkaddr newctx
---
>             eval body (limitEnv venv (fvs body)) knext mkaddr newctx
320,324c301,303
<             k' <- addFrame (nextLetFrame frame newctx) (contextId next)
<             let allNextFvs = letFvs groupIdx bindingIdx u
<             rebindAll (kfvs ctx) ctx newCtx
<             eval next k' mkaddr newCtx
<         FScrut parent branches -> do
---
>             k' <- addFrame (nextLetFrame frame newctx) venv (contextId next)
>             eval next venv k' mkaddr newctx
>         FScrut parent branches env -> do
329a309
>                     let newEnv = foldl (\acc tname -> M.insert tname newctx acc) env (M.keys bindings)
331c311
<                       extend (BindingAddr newctx tname)
---
>                       extend (fromJust $ lookupEnv tname newEnv)
333,334c313
<                     rebindAll (kfvs ctx) ctx newctx
<                     eval expr knext mkaddr newctx
---
>                     eval expr (limitEnv newEnv (fvs expr)) knext mkaddr newctx
338,340c317,319
<         FHLink eff perform k' h -> do
<           let ia = ImplicitAddr newctx perform
<           extendMKStore ia (MKHandle eff knext mkaddr h newctx)
---
>         FHLink eff perform k' h henv -> do
>           let ia = ImplicitAddr newctx henv perform
>           extendMKStore ia (MKHandle eff knext mkaddr h henv newctx)
349c328
<     MKHandle eff mkKNext mknext h@(Handler hnd ret hfvs) mkCtx -> do
---
>     MKHandle eff mkKNext mknext h@(Handler hnd ret) henv mkCtx -> do
367a347
>             let newEnv = foldl (\acc x -> M.insert x mkCtx acc) openv params
370,371c350,351
<             extendStore (BindingAddr mkCtx (last params)) (AChangeKont name kaddr mkCtx h)
<             eval bod mkKNext mknext mkCtx
---
>             extendStore (BindingAddr mkCtx (last params)) (AChangeKont name kaddr henv h)
>             eval bod (limitEnv newEnv (fvs bod)) mkKNext mknext mkCtx
373,374c353,354
<         let k' = ImplicitLAddr ctx (contextId performExpr)
<         extendKStore k' (KNext (FHLink eff (contextId performExpr) kaddr h) ctx mkKNext)
---
>         let k' = ImplicitLAddr ctx henv (contextId performExpr)
>         extendKStore k' (KNext (FHLink eff (contextId performExpr) kaddr h henv) (static ctx) mkKNext)
381,386c361,367
<   case mk of
<     MKHandle nm k' mknext h ctx | getName varName == nm -> do
<       apply knext mkaddr (BindingAddr ctx varName) (dynamic ctx)
<     MKHandle nm k' mknext h ctx -> do
<       let kx = ImplicitLAddr ctx (contextId u)
<       extendKStore kx (KNext (FHLink nm (contextId u) knext h) ctx k')
---
>   case mk of 
>     MKHandle nm k' mknext h venv ctx | getName varName == nm -> do 
>       let Just varAddr = lookupEnv varName venv
>       apply knext mkaddr varAddr (dynamic ctx)
>     MKHandle nm k' mknext h venv ctx -> do 
>       let kx = ImplicitLAddr ctx venv (contextId u)
>       extendKStore kx (KNext (FHLink nm (contextId u) knext h venv) (static ctx) k')
392,394c373,375
<   case mk of
<     MKHandle nm k' mknext h ctx | getName varName == nm -> do
<       d <- dLimit
---
>   case mk of 
>     MKHandle nm k' mknext h venv ctx | getName varName == nm -> do 
>       let env = M.delete varName venv
396,399c377,382
<       let newctx = CombinedCtx (kfvs ctx) (delimCtx m ctx) (take d $ (contextId u, static ctx):dynamic ctx)
<       extendStore (BindingAddr newctx varName) val
<       let mk' = ImplicitAddr newctx (contextId u)
<       extendMKStore mk' (MKHandle nm k' mknext h newctx)
---
>       d <- dLimit
>       let newctx = CombinedCtx (delimCtx m ctx) (take d $ (contextId u, static ctx):dynamic ctx)
>       let newEnv = M.insert varName newctx env
>       extendStore (fromJust $ lookupEnv varName newEnv) val
>       let mk' = ImplicitAddr newctx newEnv (contextId u)
>       extendMKStore mk' (MKHandle nm k' mknext h newEnv newctx)
402,404c385,387
<     MKHandle nm k' mknext h ctx -> do
<       let kx = ImplicitLAddr ctx (contextId u)
<       extendKStore kx (KNext (FHLink nm (contextId u) knext h) ctx k')
---
>     MKHandle nm k' mknext h venv ctx -> do
>       let kx = ImplicitLAddr ctx venv (contextId u)
>       extendKStore kx (KNext (FHLink nm (contextId u) knext h venv) (static ctx) k')
413,422c396,397
< fvsVal :: AChange ->FixAAMR r s e (S.Set TName)
< fvsVal (AChangeClos e _) = return $ fvs e
< fvsVal (AChangeObj _ args) = do
<   args' <- mapM (store . snd) args
<   fvss <- mapM fvsVal args'
<   return $ S.unions fvss
< fvsVal _ = return S.empty
< 
< doHandlerPrimitive :: HasCallStack => TName -> Name -> Addr -> Addr -> Addr -> [Addr] -> [AChange] -> CombinedCtx -> CombinedCtx -> ExprContext -> FixAAMR r s e FixChange
< doHandlerPrimitive name n addr knext mkaddr arguments args ctxOld ctx u | isClauseName n || n == nameHTag || n == nameEvvAt = do
---
> doHandlerPrimitive :: HasCallStack => TName -> Name -> Addr -> Addr -> Addr -> [Addr] -> [AChange] -> VEnv -> CombinedCtx -> ExprContext -> FixAAMR r s e FixChange
> doHandlerPrimitive name n addr knext mkaddr arguments args venv ctx u | isClauseName n || n == nameHTag || n == nameEvvAt = do
425c400
< doHandlerPrimitive name n addr knext mkaddr arguments args ctxOld ctx u | isNamePerform n = do
---
> doHandlerPrimitive name n addr knext mkaddr arguments args venv ctx u | isNamePerform n = do
434c409
< doHandlerPrimitive name n addr knext mkaddr arguments args ctxOld ctx u | n == nameLocalGet = do
---
> doHandlerPrimitive name n addr knext mkaddr arguments args venv ctx u | n == nameLocalGet = do
439c414
<   else do
---
>   else do 
441c416
< doHandlerPrimitive name n addr knext mkaddr arguments args ctxOld ctx u | n == nameLocalSet = do
---
> doHandlerPrimitive name n addr knext mkaddr arguments args venv ctx u | n == nameLocalSet = do
451c426
< doHandlerPrimitive name n addr knext mkaddr arguments args ctxOld ctx u | n == nameHandle = do
---
> doHandlerPrimitive name n addr knext mkaddr arguments args venv ctx u | n == nameHandle = do
458,459c433,435
<   -- trace ("OPS " ++ show ctx) $ return ()
<   let newctx = CombinedCtx (kfvs ctx) (delimCtx m ctx) (take d $ (contextId u, static ctx):dynamic ctx)
---
>   henv <- mEnvOf hnd
>   -- trace ("OPS " ++ show henv) $ return ()
>   let newctx = CombinedCtx (delimCtx m ctx) (take d $ (contextId u, static ctx):dynamic ctx)
461,466c437,442
<   let mk' = ImplicitAddr newctx (contextId u)
<   rebindAll (kfvs ctxOld) ctxOld newctx
<   extendMKStore mk' (MKHandle label knext mkaddr (Handler (arguments !! 1) (Just ret) (kfvs ctxOld)) newctx)
<   -- trace ("Applying handle: " ++ show label ++ " with env " ++ show newctx) $ return ()
<   eval bod EndKAddr mk' newctx
< doHandlerPrimitive name n addr knext mkaddr arguments args ctxOld ctx u | n == nameLocalVar = do
---
>   -- MKHandle { eff :: Name, mkKNext:: Addr, mknext:: Addr, hnd :: ExprContext, henv :: VEnv, mkCtx:: CombinedCtx }
>   let mk' = ImplicitAddr newctx venv (contextId u)
>   extendMKStore mk' (MKHandle label knext mkaddr (Handler (arguments !! 1) (Just ret)) (M.unions [retenv, henv]) newctx)
>   -- trace ("Applying handle: " ++ show label ++ " with env " ++ show venv) $ return ()
>   eval bod (limitEnv bodyenv (fvs body)) EndKAddr mk' newctx
> doHandlerPrimitive name n addr knext mkaddr arguments args venv ctx u | n == nameLocalVar = do
472c448
<         let newEnv = M.insert varName ctx
---
>         let newEnv = M.insert varName ctx env
474c450
<         extendStore (BindingAddr ctx varName) (head args)
---
>         extendStore (fromJust $ lookupEnv varName newEnv) (head args)
477,480c453,456
<         let newctx = CombinedCtx (kfvs ctx) (delimCtx m ctx) (take d $ (contextId u, static ctx):dynamic ctx)
<         let mk' = ImplicitAddr newctx (contextId u)
<         extendMKStore mk' (MKHandle (getName varName) knext mkaddr (Handler (arguments !! 1) Nothing (S.singleton varName)) newctx)
<         eval bod EndKAddr mk' newctx
---
>         let newctx = CombinedCtx (delimCtx m ctx) (take d $ (contextId u, static ctx):dynamic ctx)
>         let mk' = ImplicitAddr newctx venv (contextId u)
>         extendMKStore mk' (MKHandle (getName varName) knext mkaddr (Handler (arguments !! 1) Nothing) newEnv newctx)
>         eval bod newEnv EndKAddr mk' newctx
484a461
>         let newEnv = M.insert varName ctx env
486,487c463,464
<         extendStore (BindingAddr ctx varName) (head args)
<         eval bod knext mkaddr ctx
---
>         extendStore (fromJust $ lookupEnv varName newEnv) (head args)
>         eval bod newEnv knext mkaddr ctx
