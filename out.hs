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
<       Step (CEval expr env kaddr mkaddr ctx) -> do
<         drive $ doEval expr env kaddr mkaddr ctx
---
>       Step (CEval expr venv kaddr mkaddr ctx) -> do
>         drive $ doEval expr venv kaddr mkaddr ctx
61c60
< extendStore :: HasCallStack => Addr -> AChange -> FixAAMR r e s ()
---
> extendStore :: Addr -> AChange -> FixAAMR r e s ()
71,74c70
<   -- case v of 
<   --   MKHandle{} ->
<   --     trace ("Extending MKStore: " ++ show addr ++ " with " ++ show v) $ return ()
<   --   _ -> return ()
---
>   -- trace ("Extending MKStore: " ++ show addr ++ " with " ++ show v) $ return ()
77d72
< store :: HasCallStack => Addr -> FixAAMR r s e AChange
87c82
< eval expr env kaddr mkaddr ctx = return $ N (CEval expr env kaddr mkaddr ctx)
---
> eval expr venv kaddr mkaddr ctx = return $ N (CEval expr venv kaddr mkaddr ctx)
91,93c86,88
< allocConst :: CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
< allocConst ctx expr v = do
<   let addr = BindImplicitAddr ctx (contextId expr)
---
> allocConst :: VEnv -> CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
> allocConst env ctx expr v = do
>   let addr = BindImplicitAddr ctx (limitEnv env (fvs expr)) (contextId expr)
98,99c93,94
<   let addr = ImplicitAddr ctx u
<   extendKStore addr (KNext frame ctx env kaddr)
---
>   let addr = ImplicitAddr ctx env u
>   extendKStore addr (KNext frame (static ctx) kaddr)
107,117c102,104
< doEval :: HasCallStack => ExprContext -> BEnv -> Addr -> Addr -> CombinedCtx -> FixAAMR r s e FixChange
< doEval expr env kaddr mkaddr ctx =
<   let open = case exprOfCtx expr of
<         App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen -> True
<         _ -> False
<       process x = if not open then do
<                     analysisLog ("Evaluating: " ++ showCtxExpr expr ++ " in " ++ show env ++ ":" ++ show ctx)
<                     x
<                   else x
<   in
<   process $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
---
> doEval :: HasCallStack => ExprContext -> VEnv -> Addr -> Addr -> CombinedCtx -> FixAAMR r s e FixChange
> doEval expr venv kaddr mkaddr ctx =
>   -- trace ("Evaluating: " ++ show expr ++ " in " ++ show (M.toList venv)) $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
122c109
<       eval f env kaddr mkaddr ctx
---
>       eval f venv kaddr mkaddr ctx
127,128c114,115
<       k' <- addFrame FMask env (contextId f)
<       eval f env k' mkaddr ctx
---
>       k' <- addFrame FMask (contextId f)
>       eval f venv k' mkaddr ctx
133,134c120,121
<       k' <- addFrame FMask env (contextId f)
<       eval f env k' mkaddr ctx
---
>       k' <- addFrame FMask (contextId f)
>       eval f venv k' mkaddr ctx
141c128
<       addr <- allocConst ctx expr constr
---
>       addr <- allocConst venv ctx expr constr
145c132
<         addr <- allocConst ctx expr (AChangePrim name expr)
---
>         addr <- allocConst venv ctx expr (AChangePrim name expr)
149,163c136,150
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
<             each [eval expr (BEnv S.empty) EndKAddr (TopAddr name) c,
<                   apply kaddr mkaddr (TopAddr name) (dynamic ctx)]
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
165c152
<       addr <- allocConst ctx expr (injLit l)
---
>       addr <- allocConst venv ctx expr (injLit l)
168c155
<       addr <- allocConst ctx expr (AChangeClos expr ctx)
---
>       addr <- allocConst venv ctx expr (AChangeClos expr venv)
176c163
<       -- let newEnv = foldl (\acc x -> M.insert (defTName x) ctx acc) venv (defsOf defGroup)
---
>       let newEnv = foldl (\acc x -> M.insert (defTName x) ctx acc) venv (defsOf defGroup)
178,180c165,167
<       -- trace ("Let binding: " ++ show defName ++ " in " ++ show ctx) $ return ()
<       k' <- addFrame (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr) env (contextId bind)
<       eval bind env k' mkaddr ctx
---
>       -- trace ("Let binding: " ++ show defName ++ " in " ++ show newEnv) $ return ()
>       k' <- addFrame (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr newEnv) (contextId bind)
>       eval bind (limitEnv newEnv (S.insert defName (fvs bind)) ) k' mkaddr ctx
184c171
<       eval e env kaddr mkaddr ctx
---
>       eval e venv kaddr mkaddr ctx
186c173
<       addr <- allocConst ctx expr (AChangeClos expr ctx)
---
>       addr <- allocConst venv ctx expr (AChangeClos expr venv)
193c180
<       eval e env kaddr mkaddr ctx
---
>       eval e venv kaddr mkaddr ctx
197,198c184,185
<       k' <- addFrame (FScrut expr branches) env (contextId s)
<       eval s env k' mkaddr ctx
---
>       k' <- addFrame (FScrut expr branches venv) (contextId s)
>       eval s (limitEnv venv (fvs s)) k' mkaddr ctx
201c188
<   where addFrame f u = allocFrame f kaddr ctx u
---
>   where addFrame f u = allocFrame f kaddr ctx venv u
205,206c192,193
<           k' <- addFrame (FApp (length args) argExprs [] expr) env (contextId f)
<           eval f env k' mkaddr ctx
---
>           k' <- addFrame (FApp (length args) argExprs [] expr venv) (contextId f)
>           eval f (limitEnv venv (fvs f)) k' mkaddr ctx
208,216c195,202
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
219a206
>   -- trace ("Applying: " ++ show addr ++ " with " ++ show kaddr ++ " " ++ show mkaddr) $ return ()
221,222d207
<   trace ("Applying: " ++ show addr ++ " with " ++ show kaddr ++ " " ++ show mkaddr ++ ":" ++ show dynctx ++ "\n" ++ show k ) $ return ()
< 
231d215
<             -- trace ("Done! " ++ show mkaddr) $ return ()
236,238c220
<             let TopAddr tname = mkaddr
<             -- trace ("Applying top value: " ++ show addr ++ " with " ++ show topV) $ return ()
<             -- let [(tname, ctx)] = M.toList env
---
>             let TopAddr name  = mkaddr
240c222,223
<             extendStore (TopAddr tname) topV
---
>             -- trace ("Applying top value: " ++ show addr ++ " with " ++ show topV) $ return ()
>             extendStore (BindingAddr c name) topV
242c225
<         MKHandle _ knext mknext _ dynctx ->
---
>         MKHandle _ knext mknext _ _ dynctx ->
244,246c227,229
<     KNext frame ctx env knext ->
<       let newctx = CombinedCtx (static ctx) dynctx
<           addFrame f u = allocFrame f knext newctx u in
---
>     KNext frame ctx knext ->
>       let newctx = CombinedCtx ctx dynctx
>           addFrame f venv u = allocFrame f knext newctx venv u in
251c234
<             AChangeClos e cctx -> do
---
>             AChangeClos e env -> do
253,257c236,237
<               let env' = BEnv $ fvs e
<               -- trace ("FMask " ++ show env' ++ " ctx " ++ show ctx ++ " cctx " ++ show cctx ++ " newctx " ++ show newctx) $ return ()
<               rebindAll (bvars env') cctx newctx
<               eval bod env' knext mkaddr newctx
<         FApp n args res u -> do
---
>               eval bod env knext mkaddr newctx
>         FApp n args res u venv -> do
266c246
<                   AChangeClos cexpr cctx -> do
---
>                   AChangeClos cexpr cenv -> do
270d249
<                     let env' = BEnv $ fvs body
272c251,252
<                     -- trace ("Applying closure: " ++ show cexpr ++ " with " ++ show env' ++ ":" ++ show newCtx) $ return ()
---
>                     let newEnv = foldl (\acc x -> M.insert x newCtx acc) cenv args
>                     -- trace ("Applying closure: " ++ show cexpr ++ " with " ++ show args) $ return ()
275c255
<                       extendStore (BindingAddr newCtx a) val) args arguments
---
>                       extendStore (fromJust $ lookupEnv a newEnv) val) args arguments
277c257
<                     let ia = ImplicitAddr newCtx (contextId body)
---
>                     let ia = ImplicitAddr newCtx newEnv (contextId body)
279,280c259
<                     rebindAll (fvs cexpr) cctx newCtx
<                     eval body env' ia mkaddr newCtx
---
>                     eval body (limitEnv newEnv (fvs body)) ia mkaddr newCtx
283c262
<                     let addr = BindImplicitAddr newctx (contextId u)
---
>                     let addr = BindImplicitAddr newctx venv (contextId u)
286c265
<                       doHandlerPrimitive name n addr knext mkaddr arguments args newctx u
---
>                       doHandlerPrimitive name n addr knext mkaddr arguments args venv newctx u
288c267
<                       res <- doPrimitive n args
---
>                       res <- doPrimitive n args venv
295c274
<                     let addr = BindImplicitAddr newctx (contextId u)
---
>                     let addr = BindImplicitAddr newctx venv (contextId u)
298c277
<                   AChangeKont label kx hctx hnd@(Handler _ _ henv) -> do
---
>                   AChangeKont label kx henv hnd -> do
303,307c282,283
<                         mk' = ImplicitAddr newCtx (contextId u)
<                     trace ("Applying continuation " ++ show (contextId u) ++ " rebinding " ++ show henv ) $ return () -- ++ "for\n" ++ 
<                     --        show res ++ "\n" ++ show kaddr ++ "\n" ++ show mkaddr ++ "\n" ++ show addr ++ "\n" ++ show dynctx) $ return ()
<                     rebindAll (bvars henv) hctx newCtx
<                     extendMKStore mk' (MKHandle label knext mkaddr hnd newCtx)
---
>                         mk' = ImplicitAddr newCtx venv (contextId u)
>                     extendMKStore mk' (MKHandle label knext mkaddr hnd venv newCtx)
312,317c288,291
<               k' <- addFrame (FApp n rest (res ++ [addr]) u) env (contextId next)
<               rebindAll (bvars env) ctx newctx
<               eval next env k' mkaddr newctx
<         FLet groupIdx numGroups bindingIdx numBindings name resolved u -> do
<           -- trace "Applying Let" $ return ()
<           rebindAll (bvars env) ctx newctx
---
>               k' <- addFrame (FApp n rest (res ++ [addr]) u (limitEnv venv (fvsl rest))) venv (contextId next)
>               eval next (limitEnv venv (fvs next)) k' mkaddr newctx
>         FLet groupIdx numGroups bindingIdx numBindings name resolved u venv -> do
>           -- trace ("Applying Let") $ return ()
319,321c293,294
<           extendStore (BindingAddr newctx name) val
<           let env' = BEnv $ S.insert name (bvars env)
<           -- trace ("Binding " ++ show name ++ " to " ++ show val ++ " in " ++ show newCtx ++ " old: " ++ show ctx ) $ return ()
---
>           -- trace ("Binding " ++ show name ++ " to " ++ show val ++ " in " ++ show venv ) $ return ()
>           extendStore (fromJust $ lookupEnv name venv) val
325c298
<             eval body env' knext mkaddr newctx
---
>             eval body (limitEnv venv (fvs body)) knext mkaddr newctx
328,330c301,303
<             k' <- addFrame (nextLetFrame frame newctx) env' (contextId next)
<             eval next env' k' mkaddr newctx
<         FScrut parent branches -> do
---
>             k' <- addFrame (nextLetFrame frame newctx) venv (contextId next)
>             eval next venv k' mkaddr newctx
>         FScrut parent branches env -> do
336c309
<                     let env' = BEnv $ S.union (bv (branchPatterns branch)) (bvars env)
---
>                     let newEnv = foldl (\acc tname -> M.insert tname newctx acc) env (M.keys bindings)
338c311
<                       extend (BindingAddr newctx tname)
---
>                       extend (fromJust $ lookupEnv tname newEnv)
340,341c313
<                     rebindAll (bvars env) ctx newctx
<                     eval expr env' knext mkaddr newctx
---
>                     eval expr (limitEnv newEnv (fvs expr)) knext mkaddr newctx
345,348c317,319
<         FHLink eff perform k' h -> do
<           trace ("Link restore " ++ show kaddr ++ " " ++ show newctx) $ return ()
<           let ia = ImplicitAddr newctx perform
<           extendMKStore ia (MKHandle eff knext mkaddr h newctx)
---
>         FHLink eff perform k' h henv -> do
>           let ia = ImplicitAddr newctx henv perform
>           extendMKStore ia (MKHandle eff knext mkaddr h henv newctx)
357c328
<     MKHandle eff mkKNext mknext h@(Handler hnd ret henv) mkCtx -> do
---
>     MKHandle eff mkKNext mknext h@(Handler hnd ret) henv mkCtx -> do
359d329
<         trace ("Matched " ++ show mkCtx) $ return ()
374c344
<             AChangeClos op _ <- store (snd opAddr)
---
>             AChangeClos op openv <- store (snd opAddr)
377,378c347
<             let opEnv = BEnv $ fvs bod
<             -- let opCtx = mkCtx -- {kfvs = S.union (S.fromList params) (kfvs mkCtx)}
---
>             let newEnv = foldl (\acc x -> M.insert x mkCtx acc) openv params
381,383c350,351
<             -- rebindAll (fvs op) mkCtx opCtx
<             extendStore (BindingAddr mkCtx (last params)) (AChangeKont name kaddr mkCtx h)
<             eval bod opEnv mkKNext mknext mkCtx
---
>             extendStore (BindingAddr mkCtx (last params)) (AChangeKont name kaddr henv h)
>             eval bod (limitEnv newEnv (fvs bod)) mkKNext mknext mkCtx
385,387c353,354
<         let k' = ImplicitLAddr ctx opName (contextId performExpr)
<         trace ("Link create " ++ show k' ++ " " ++ show ctx) $ return ()
<         extendKStore k' (KNext (FHLink eff (contextId performExpr) kaddr h) mkCtx henv mkKNext)
---
>         let k' = ImplicitLAddr ctx henv (contextId performExpr)
>         extendKStore k' (KNext (FHLink eff (contextId performExpr) kaddr h henv) (static ctx) mkKNext)
394,399c361,367
<   case mk of
<     MKHandle nm k' mknext h ctx | getName varName == nm -> do
<       apply knext mkaddr (BindingAddr ctx varName) (dynamic ctx)
<     MKHandle nm k' mknext h@(Handler _ _ henv) ctx -> do
<       let kx = ImplicitLAddr ctx (getName varName) (contextId u)
<       extendKStore kx (KNext (FHLink nm (contextId u) knext h) ctx henv k')
---
>   case mk of 
>     MKHandle nm k' mknext h venv ctx | getName varName == nm -> do 
>       let Just varAddr = lookupEnv varName venv
>       apply knext mkaddr varAddr (dynamic ctx)
>     MKHandle nm k' mknext h venv ctx -> do 
>       let kx = ImplicitLAddr ctx venv (contextId u)
>       extendKStore kx (KNext (FHLink nm (contextId u) knext h venv) (static ctx) k')
405,407c373,375
<   case mk of
<     MKHandle nm k' mknext h ctx | getName varName == nm -> do
<       d <- dLimit
---
>   case mk of 
>     MKHandle nm k' mknext h venv ctx | getName varName == nm -> do 
>       let env = M.delete varName venv
408a377
>       d <- dLimit
410,412c379,382
<       extendStore (BindingAddr newctx varName) val
<       let mk' = ImplicitAddr newctx (contextId u)
<       extendMKStore mk' (MKHandle nm k' mknext h newctx)
---
>       let newEnv = M.insert varName newctx env
>       extendStore (fromJust $ lookupEnv varName newEnv) val
>       let mk' = ImplicitAddr newctx newEnv (contextId u)
>       extendMKStore mk' (MKHandle nm k' mknext h newEnv newctx)
415,417c385,387
<     MKHandle nm k' mknext h@(Handler _ _ henv) ctx -> do
<       let kx = ImplicitLAddr ctx (getName varName) (contextId u)
<       extendKStore kx (KNext (FHLink nm (contextId u) knext h) ctx henv k')
---
>     MKHandle nm k' mknext h venv ctx -> do
>       let kx = ImplicitLAddr ctx venv (contextId u)
>       extendKStore kx (KNext (FHLink nm (contextId u) knext h venv) (static ctx) k')
426,435c396,397
< fvsVal :: AChange -> FixAAMR r s e [(S.Set TName, CombinedCtx)]
< fvsVal (AChangeClos e ctx) = return [(fvs e, ctx)]
< fvsVal (AChangeObj _ args) = do
<   args' <- mapM (store . snd) args
<   fvss <- mapM fvsVal args'
<   return $ concat fvss
< fvsVal _ = return []
< 
< doHandlerPrimitive :: HasCallStack => TName -> Name -> Addr -> Addr -> Addr -> [Addr] -> [AChange] -> CombinedCtx -> ExprContext -> FixAAMR r s e FixChange
< doHandlerPrimitive name n addr knext mkaddr arguments args ctx u | isClauseName n || n == nameHTag || n == nameEvvAt = do
---
> doHandlerPrimitive :: HasCallStack => TName -> Name -> Addr -> Addr -> Addr -> [Addr] -> [AChange] -> VEnv -> CombinedCtx -> ExprContext -> FixAAMR r s e FixChange
> doHandlerPrimitive name n addr knext mkaddr arguments args venv ctx u | isClauseName n || n == nameHTag || n == nameEvvAt = do
438c400
< doHandlerPrimitive name n addr knext mkaddr arguments args ctx u | isNamePerform n = do
---
> doHandlerPrimitive name n addr knext mkaddr arguments args venv ctx u | isNamePerform n = do
447c409
< doHandlerPrimitive name n addr knext mkaddr arguments args ctx u | n == nameLocalGet = do
---
> doHandlerPrimitive name n addr knext mkaddr arguments args venv ctx u | n == nameLocalGet = do
452c414
<   else do
---
>   else do 
454c416
< doHandlerPrimitive name n addr knext mkaddr arguments args ctx u | n == nameLocalSet = do
---
> doHandlerPrimitive name n addr knext mkaddr arguments args venv ctx u | n == nameLocalSet = do
464,465c426,428
< doHandlerPrimitive name n addr knext mkaddr arguments args ctx u | n == nameHandle = do
<   let [AChangeObj _ [hNameAddr], hnd, AChangeClos ret retenv, AChangeClos body bodyctx] = args
---
> doHandlerPrimitive name n addr knext mkaddr arguments args venv ctx u | n == nameHandle = do
>   args <- mapM store arguments
>   let [AChangeObj _ [hNameAddr], hnd, AChangeClos ret retenv, AChangeClos body bodyenv] = args
470,472c433,434
<   fvss <- fvsVal hnd 
<   let henv = BEnv $ S.unions (map fst fvss) 
<   trace ("OPS " ++ show label ++ " fvs: " ++ show henv ++ ":" ++ show ctx) $ return ()
---
>   henv <- mEnvOf hnd
>   -- trace ("OPS " ++ show henv) $ return ()
474,478d435
<   mapM_ (\(fvs, oldCtx) -> 
<     rebindAll fvs oldCtx newctx
<     ) fvss
<   let mk' = ImplicitAddr newctx (contextId u)
<   extendMKStore mk' (MKHandle label knext mkaddr (Handler (arguments !! 1) (Just ret) henv) newctx)
480,485c437,442
<   let benv = BEnv $ fvs body
<   rebindAll (bvars benv) bodyctx newctx
<   rebindAll (fvs ret) retenv newctx
<   --trace ("Applying handle: " ++ show label ++ " with env " ++ show newctx) $ return ()
<   eval bod benv EndKAddr mk' newctx
< doHandlerPrimitive name n addr knext mkaddr arguments args ctx u | n == nameLocalVar = do
---
>   -- MKHandle { eff :: Name, mkKNext:: Addr, mknext:: Addr, hnd :: ExprContext, henv :: VEnv, mkCtx:: CombinedCtx }
>   let mk' = ImplicitAddr newctx venv (contextId u)
>   extendMKStore mk' (MKHandle label knext mkaddr (Handler (arguments !! 1) (Just ret)) (M.unions [retenv, henv]) newctx)
>   -- trace ("Applying handle: " ++ show label ++ " with env " ++ show venv) $ return ()
>   eval bod (limitEnv bodyenv (fvs body)) EndKAddr mk' newctx
> doHandlerPrimitive name n addr knext mkaddr arguments args venv ctx u | n == nameLocalVar = do
489c446
<       AChangeClos e _ -> do
---
>       AChangeClos e env -> do
491c448
<         let newEnv = M.insert varName ctx
---
>         let newEnv = M.insert varName ctx env
493c450
<         extendStore (BindingAddr ctx varName) (head args)
---
>         extendStore (fromJust $ lookupEnv varName newEnv) (head args)
496d452
<         let env = BEnv (S.singleton varName)
498,500c454,456
<         let mk' = ImplicitAddr newctx (contextId u)
<         extendMKStore mk' (MKHandle (getName varName) knext mkaddr (Handler (arguments !! 1) Nothing env) newctx)
<         eval bod env EndKAddr mk' newctx
---
>         let mk' = ImplicitAddr newctx venv (contextId u)
>         extendMKStore mk' (MKHandle (getName varName) knext mkaddr (Handler (arguments !! 1) Nothing) newEnv newctx)
>         eval bod newEnv EndKAddr mk' newctx
503c459
<       AChangeClos e _ -> do
---
>       AChangeClos e env -> do
504a461
>         let newEnv = M.insert varName ctx env
506,508c463,464
<         let env = BEnv (S.singleton varName)
<         extendStore (BindingAddr ctx varName) (head args)
<         eval bod env knext mkaddr ctx
---
>         extendStore (fromJust $ lookupEnv varName newEnv) (head args)
>         eval bod newEnv knext mkaddr ctx
517c473
< rebind :: HasCallStack => Addr -> Addr -> FixAAMR r s e ()
---
> rebind :: Addr -> Addr -> FixAAMR r s e ()
