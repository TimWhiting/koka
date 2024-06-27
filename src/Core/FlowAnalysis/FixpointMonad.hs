-----------------------------------------------------------------------------
-- Copyright 2024 Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-- {-
--     Check if a constructor context is well formed, and create a context path
-- -}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# HLINT ignore "Use newtype instead of data" #-}

module Core.FlowAnalysis.FixpointMonad(
  FixTS, FixT, FixIn,
  SimpleChange(..),
  SimpleLattice(..), SLattice,
  Lattice(..),
  Contains(..),
  Label(..), ContX(..), ContF(..),
  memo, memoFull, push, each, doBottom, liftMaybe,
  withEnv, getEnv, getEnvR,
  getCache, cacheLookup,
  getState, getStateR, setState, updateState,
  runFix, runFixCont, runFixFinish, runFixFinishC,
  writeDependencyGraph,
  runExample
  ) where
import Debug.Trace (trace)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust, fromMaybe)
import Control.Monad.Reader (lift, ReaderT (runReaderT), ask, local)
import Control.Monad.State (StateT (..), MonadState (..), liftIO, get, put)
import Control.Monad.Identity (IdentityT, Identity (..))
import Data.List (intercalate)
import Control.Monad (foldM, ap)
import qualified Control.Monad.Fail as Fail
import Control.Monad.Trans
import Control.Monad.Trans.Cont (ContT (..))
import Control.Monad.Cont.Class (callCC)
import Data.Foldable (foldlM)
import GHC.IORef (newIORef)
import Data.IORef (writeIORef)
import System.Process (callCommand)

-- A type class for lattices
-- A lattice has a bottom value, a join operation, and a lte relation
class Lattice l d where
  bottom :: l d
  isBottom :: l d -> Bool
  join :: l d -> l d -> l d
  insert :: d -> l d -> l d
  lte :: d -> l d -> Bool
  elems :: l d -> [d]

class Label a where
  label :: a -> String

-- A simple lattice is a lattice where we just have bottom, top, and a singleton value
-- An abstract value of an integer can be represented using this. Top means any integer, bottom means no integers, and a singleton value means a single integer value.
-- lte is just equality and joining just goes to top if the values are different
-- 
-- The underlying type a just needs to implement Ord for this to work
data SimpleLattice a d = LBottom
  | LSingle a
  | LTop deriving (Eq, Ord)

type SLattice a = SimpleLattice a (SimpleChange a)

data SimpleChange a = LChangeTop | LChangeSingle a deriving (Show,Eq,Ord)

instance Show a => Show (SimpleLattice a d) where
  show LBottom = "LBottom"
  show (LSingle a) = "LSingle " ++ show a
  show LTop = "LTop"

instance Label a => Label (SimpleLattice a d) where
  label LBottom = "⊥"
  label (LSingle a) = label a
  label LTop = "⊤"

instance (Ord a) => Lattice (SimpleLattice a) (SimpleChange a) where
  bottom = LBottom
  insert (LChangeSingle a) b = LSingle a `join` b
  insert LChangeTop b = LTop
  join a b =
    case (a, b) of
      (LBottom, x) -> x
      (x, LBottom) -> x
      (LSingle x, LSingle y) -> if x == y then LSingle x else LTop
      _ -> LTop
  lte _ LTop = True
  lte (LChangeSingle m) (LSingle m') = m == m'
  lte _ _ = False
  elems LTop = [LChangeTop]
  elems LBottom = []
  elems (LSingle a) = [LChangeSingle a]
  isBottom LBottom = True
  isBottom _ = False

-- A type class to allow us to easily define lattices for types that can implement a contains relation
-- 
-- Sets are a good example of such lattices, which can also hold more than one value.
-- However, it is up to the user to ensure that the set is finite such that the fixpoint will not diverge.
class Contains a where
  contains :: a -> a -> Bool

data ChangeSet a d = ChangeSet (S.Set a)

-- Simple implementation of a set lattice
instance Ord a => Lattice (ChangeSet a) a where
  bottom = ChangeSet S.empty
  insert a (ChangeSet s) = ChangeSet $ S.insert a s
  join (ChangeSet a) (ChangeSet b) = ChangeSet $ S.union a b
  lte a (ChangeSet sb) = S.member a sb
  elems (ChangeSet a) = S.elems a
  isBottom (ChangeSet a) = S.null a

type FixTS e s i l d = FixT e s i l d d
data ContX e s i l d = ContX {
                            contV :: d -> FixIn e s i l d (), -- The continuation to call when the cache changes
                            from :: Maybe i,
                            fromId :: Integer
                          }
data ContF e s i l d = ContF {
                            contFV :: l d -> FixIn e s i l d (), -- The continuation to call when the cache changes
                            fromF :: Maybe i,
                            fromFId :: Integer
                          } 
instance Show (ContX e s i l d) where
  show _ = "ContX"
instance Show (ContF e s i l d) where
  show _ = "ContF"

type FixT e s i l d = ContT () (FixIn e s i l d)
type FixIn e s i l d = (ReaderT (e,Maybe i,Integer) (StateT (M.Map i (l d, Integer, [ContX e s i l d], [ContF e s i l d]), s, Integer, Bool) IO))

withEnv :: (e -> e) -> FixT e s i l d a -> FixT e s i l d a
withEnv f = local (\(e, i, id) -> (f e, i, id))

getEnv :: FixT e s i l d e
getEnv = do
  (f, s, t) <- ask
  return f

getState :: FixT e s i l d s
getState = do
  (_, res, _, _) <- get
  return res

getStateR :: FixIn e s i l d s
getStateR = do
  (_, res, _, _) <- get
  return res

getEnvR :: FixIn e s i l d e
getEnvR = do
  (f, _, _) <- ask
  return f

setState :: s -> FixT e s i l d  ()
setState x = do
  (f, s, t, invalid) <- get
  put (f, x, t, invalid)

getCache :: FixIn e s i l d (M.Map i (l d))
getCache = do
  (res, _, _, _) <- get
  return $ M.map (\(f,s,t,t1) -> f) res

cacheLookup :: Ord i => i -> FixIn e s i l d (Maybe (l d))
cacheLookup i = do
  M.lookup i <$> getCache

updateState :: (s -> s) -> FixT e s i l d  ()
updateState update = do
  st <- getState
  setState $ update st

liftMaybe :: Maybe a -> FixT e s i l d a
liftMaybe (Just x) = return x
liftMaybe Nothing = doBottom

doBottom :: FixT e s i l d b
doBottom = ContT (\x -> return ())

bottomInvalidate :: FixT e s i l d b
bottomInvalidate = do
  (cache, state, newId, _) <- get
  put (cache, state, newId, True)
  doBottom

-- This is an unsafe function, only make sure you revalidate the cache if the cache is properly invalidated (currently it is not - see TODO in memo)
-- Probably better to just run with a fresh cache, and just reuse some user state that is not invalid
resetInvalidate :: FixT e s i l d ()
resetInvalidate = do
  (cache, state, newId, _) <- get
  put (cache, state, newId, False)

localCtx :: Maybe i -> Integer -> FixIn e s i l d a -> FixIn e s i l d a
localCtx i id = local (\(e,_,_) -> (e,i,id))

localCtxT :: Maybe i -> Integer -> FixT e s i l d a -> FixT e s i l d a
localCtxT i id = local (\(e,_,_) -> (e,i,id))

-- Memoization function, memoizes a fixpoint computation by using a cache of previous results and continuations that depend on those results
memo :: (Show d, Show (l d), Show i, Ord i, Lattice l d) => i -> FixT e s i l d d -> FixT e s i l d d
memo key f = do
  (env, from, fromId) <- ask
  ContT (\c -> do
    (cache, state, newId, invalid) <- get -- TODO: Invalidate cache on all continuations
    let cont = ContX c from fromId
    case fromMaybe (bottom, newId, [], []) (M.lookup key cache) of
      (xss, tid, [], []) -> do
        -- First time requesting the memoed function with this key
        trace ("\nNew memo request for  " ++ show key ++ "\nFrom: " ++ show from ++ "\n") $ return ()
        put (M.insert key (xss, tid, [cont], []) cache, state, if tid == newId then newId + 1 else newId, invalid)
        mapM_ c (elems xss)
        runContT (localCtxT (Just key) tid f) (\x -> do
            -- For all results push them into the cache
            -- trace ("Got new result for " ++ show key ++ " " ++ show x) $ return ()
            push key x
          )
      (xss, tid, conts, fconts) -> do
        trace (show conts) $ return ()
        trace (show fconts) $ return ()
        -- Requesting the result of the memoized function from a different dependant
        put (M.insert key (xss, tid, cont:conts, fconts) cache, state, newId, invalid)
        trace ("\nNew continuation for " ++ show key ++ "\nFrom: " ++ show from ++ "\n") $ return ()
        mapM_ c (elems xss)
      
      )

memoFull :: (Show d, Show (l d), Show i, Ord i, Lattice l d) => i -> FixT e s i l d (l d) -> FixT e s i l d (l d)
memoFull key f = do
  (env, from, fromId) <- ask
  ContT (\c -> do
    (cache, state, newId, invalid) <- get -- TODO: Invalidate cache on all continuations
    let cont = ContF c from fromId
    case fromMaybe (bottom, newId, [], []) (M.lookup key cache) of
      (xss, tid, [], []) -> do
        -- First time requesting the memoed function with this key
        -- trace ("\nNew memo request for  " ++ show key ++ "\nFrom: " ++ show from ++ "\n") $ return ()
        put (M.insert key (xss, tid, [], [cont]) cache, state, if tid == newId then newId + 1 else newId, invalid)
        c xss
        runContT (localCtxT (Just key) tid f) (\x -> do
            -- For all results push them into the cache
            -- trace ("Got new result for " ++ show key ++ " " ++ show x) $ return ()
            mapM_ (\x -> push key x) (elems x)
          )
      (xss, tid, conts, fconts) -> do
        -- Requesting the result of the memoized function from a different dependant
        put (M.insert key (xss, tid, conts, cont:fconts) cache, state, newId, invalid)
        -- trace ("\nNew continuation for " ++ show key ++ "\nFrom: " ++ show from ++ "\n") $ return ()
        c xss
    )

each :: (Show d, Show b, Ord i, Show (l d), Lattice l d) => [FixT e s i l d b] -> FixT e s i l d b
each xs =
  ContT $ \c -> do -- Get the continuation
    -- For each monadic fixpoint, run the continuation piece, and call our continuation with each result
    mapM_ (\comp -> runContT comp (\res -> do      
      -- trace ("Calling continuation with " ++ show res) $ return ()
      c res)) xs

-- Adds a new result to the cache and calls all continuations that depend on that result
push :: (Show i, Show d, Show (l d), Ord i, Lattice l d) => i -> d -> FixIn e s i l d ()
push key value = do
  -- trace ("Pushing new result for " ++ show key ++ " : " ++ show value) $ return ()
  (cache, state, newId, invalid) <- get
  let cur = M.lookup key cache
  let (values, keyId, conts, fconts) = fromMaybe (bottom, newId, [], []) cur
  if lte value values then
    -- If the value already exists in the cache
    -- trace ("New result " ++ show value ++ " is already contained in " ++ show values) $ 
    return ()
  else do
    -- Otherwise, insert the value into the cache and call all continuations in the cache
    -- that depend on changes to this key
    let added = value `insert` values
    if keyId == newId then
      put (M.insert key (added, keyId, conts, fconts) cache, state, newId + 1, invalid)
    else
      put (M.insert key (added, keyId, conts, fconts) cache, state, newId, invalid)
    -- trace ("Calling continuations for " ++ show key ++ " " ++ show (length conts)) $ return ()
    mapM_ (\(ContX c f fi) -> do
      -- trace ("\nCalling continuation:" ++ show key ++ "\n\tFrom: " ++ show f ++ "\n\tTo: " ++ show key ++ "\n\tNew value: " ++ show value ++ "\n") $ return ()
      c value
      ) conts
    mapM_ (\(ContF c f fi) -> do
      c added
      ) fconts
    -- trace ("Finished calling continuations for " ++ show key) $ return ()

writeDependencyGraph :: (Label i, Show d, Label (l d), Ord i) => String -> M.Map i (l d, Integer, [ContX e s i l d], [ContF e s i l d]) -> IO ()
writeDependencyGraph mn cache = do
  let values = M.foldl (\acc (v, toId, conts, fconts) -> acc ++ fmap (\(ContX _ from fromId) -> (v, from, fromId, toId)) conts) [] cache
  let nodes = M.foldlWithKey (\acc k (v, toId, conts, fconts) -> (toId,k,v):acc) [] cache
  let edges = S.toList $ S.fromList $ fmap (\(v, f, fi, ti) -> (fi, ti)) values
  let dot = "digraph G {\n"
            ++ intercalate "\n" (fmap (\(a, b) -> show a ++ " -> " ++ show b) edges) ++ "\n"
            ++ intercalate "\n" (fmap (\(fi, k, v) -> show fi ++ " [label=\"" ++ label k ++ "\n\n" ++ label v ++ "\"]") nodes) 
            ++ "\n 0 [label=\"Start\"]\n"
            ++ "\n}"
  -- trace (show edges) $ return ()
  writeFile ("scratch/debug/graph-" ++ mn ++ ".dot") dot
  -- callCommand $ "dot -Tsvg scratch/debug/graph-" ++ mn ++ ".dot -o scratch/debug/graph-" ++ mn ++ ".svg"
  return ()

-- Runs a fixpoint computation with an environment and state
runFix :: (Show i, Show d, Show (l d), Label i, Label (l d), Ord i) => e -> s -> FixT e s i l d x -> IO (M.Map i (l d), s)
runFix e s f = do
  (_, (cache, state, _, _)) <- runStateT (runReaderT (runContT f (\x -> return ())) (e,Nothing,0)) (M.empty, s, 1, False)
  -- writeDependencyGraph cache
  return (fmap (\(f, s, t, t') -> f) cache, state)

-- Runs a fixpoint computation with an environment and state
runFixCont :: (Show i, Show d, Show (l d), Ord i) => FixT e s i l d x -> FixIn e s i l d ()
runFixCont f = 
  runContT f (\x -> return ())

runFixFinish :: (Show i, Show d, Show (l d), Label i, Label (l d), Ord i) => e -> s -> FixIn e s i l d x -> IO (M.Map i (l d), s, x)
runFixFinish e s f = do
  (x, (cache, state, _, _)) <- runStateT (runReaderT f (e,Nothing,0)) (M.empty, s, 1, False)
  return (fmap (\(f, s, t, t') -> f) cache, state, x)

runFixFinishC :: (Show i, Show d, Show (l d), Label i, Label (l d), Ord i) => e -> s -> FixIn e s i l d x -> IO (M.Map i (l d, Integer, [ContX e s i l d], [ContF e s i l d]), s, x)
runFixFinishC e s f = do
  (x, (cache, state, _, _)) <- runStateT (runReaderT f (e,Nothing,0)) (M.empty, s, 1, False)
  return (cache, state, x)

------------------------------ EXAMPLE USAGE ---------------------------------
---- An Example of how to use the fixpoint interface -- used for testing

newtype State = State{
  unique :: Int
} deriving Show

-- Takes in an integer and returns a fixpoint computation representing the fibonacci function
-- The fixpoint memoizes based on a tuple of the function name and the input
-- The fixpoint computation threads through State
-- The fixpoint computation doesn't use any environment monad
-- The fixpoint computation returns an integer encapsulated in a SimpleLattice
fib :: Int -> FixT () State (String, Int) (SimpleLattice Int) (SimpleChange Int) (SimpleChange Int)
fib n =
  -- memo using the key ("fib", n) 
  -- (note: "fib" is not actually required, but for mutual recursion you need some way of dispatching based on the function name)
  memo ("fib", n) $ do
    if n == 0 || n == 1 then return (LChangeSingle 1) else do
      incrementUnique
      x <- fib (n - 1)
      y <- fib (n - 2)
      case (x, y) of
        (LChangeSingle x, LChangeSingle y) -> return $ LChangeSingle (x + y)

swap :: [Int] -> FixT () () [Int] (SimpleLattice [Int]) (SimpleChange [Int]) (SimpleChange [Int])
swap l = do
  trace ("Swapping " ++ show l) $ return ()
  memo l $
    trace ("Memoizing " ++ show l) $
    case l of
      [x, y, z] -> do
        each [swap [y, x], swap [z, y]]
      [x, z] -> return $ LChangeSingle [z, x]

instance Label (String, Int) where
  label (s, i) = s ++ " " ++ show i

instance Label [Int] where
  label l = show l

instance Label Int where
  label i = show i

incrementUnique :: FixT e State b c (SimpleChange Int) ()
incrementUnique = updateState (\state -> state{unique = unique state + 1})

runExample :: IO ()
runExample = do
  comp <- runFix () (State 0) $ fib 6
  trace (show comp) $ return ()
  comp2 <- runFix () () $ swap [1, 2, 3]
  trace (show comp2) $ return ()