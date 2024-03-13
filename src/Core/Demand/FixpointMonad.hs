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

module Core.Demand.FixpointMonad(
  FixTS, FixT, FixTR,
  SimpleChange(..),
  SimpleLattice(..), SLattice,
  BasicLattice(..), Lattice(..),
  Contains(..),
  memo, push, each, doBottom,
  withEnv, getEnv,
  getCache, cacheLookup,
  getState, setState, updateState,
  runFix, runFixWithCache,
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

-- A type class for lattices
-- A lattice has a bottom value, a join operation, and a lte relation
class Lattice l d where
  bottom :: l d
  isBottom :: l d -> Bool
  join :: l d -> l d -> l d
  insert :: d -> l d -> l d
  lte :: d -> l d -> Bool
  elems :: l d -> [d]

-- A simple lattice is a lattice where we just have bottom, top, and a singleton value
-- An abstract value of an integer can be represented using this. Top means any integer, bottom means no integers, and a singleton value means a single integer value.
-- lte is just equality and joining just goes to top if the values are different
-- 
-- The underlying type a just needs to implement Ord for this to work
data SimpleLattice a d = LBottom
  | LSingle a
  | LTop deriving (Eq, Ord)

type SLattice a = SimpleLattice a (SimpleChange a)

data SimpleChange a = LChangeTop | LChangeSingle a deriving (Show,Eq)

instance Show a => Show (SimpleLattice a d) where
  show LBottom = "LBottom"
  show (LSingle a) = "LSingle " ++ show a
  show LTop = "LTop"

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

-- A Basic Lattice just delegates to the underlying type assuming that the underlying type implements the Contains type class and is a Monoid
data BasicLattice d a = BL a deriving (Eq, Ord)

-- The `bottom` value is just the monoid's `mempty` value, `join` is implemented with `mappend`, and the `contains` relation defines `subsumption` (i.e. `a` contains `b` if `a` is a superset of `b`)
instance (Eq a, Contains a, Monoid a) => Lattice (BasicLattice a) a where
  bottom = BL mempty
  join (BL a) (BL b) = BL $ a `mappend` b
  lte m (BL m') = m' `contains` m
  elems (BL m) = [m]
  insert a (BL b) = BL (a `mappend` b)
  isBottom (BL a) = a == mempty

instance Functor (BasicLattice a) where
  fmap f (BL a) = BL $ f a

instance (Contains a) => Contains (BasicLattice d a) where
  contains (BL a) (BL b) = a `contains` b
instance (Show a) => Show (BasicLattice d a) where
  show (BL a) = show a

instance (Semigroup a) => Semigroup (BasicLattice d a) where
  (BL a) <> (BL b) = BL $ a <> b

instance (Monoid a) => Monoid (BasicLattice d a) where
  mempty = BL mempty
  mappend = (<>)

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
type FixTR e s i l d = FixT e s i l d
data ContX e s i l d = ContX {
                            contV :: d -> FixIn e s i l d (), -- The continuation to call when the cache changes
                            from :: Maybe i,
                            fromId :: Integer,
                            to :: i, -- The query that the continuation is used with
                            toId :: Integer
                          } -- ReaderT DEnv (StateT (M.Map i (S.Set o, [ContX i o a]), State) Identity) a 
instance Show (ContX e s i l d) where
  show _ = ""

type FixT e s i l d = ContT () (FixIn e s i l d)
type FixIn e s i l d = (ReaderT (e,Maybe i,Integer) (StateT (M.Map i (l d, [ContX e s i l d]), s, Integer) IO))

withEnv :: (e -> e) -> FixT e s i l d a -> FixT e s i l d a
withEnv f = local (\(e, i, id) -> (f e, i, id))

getEnv :: FixT e s i l d e
getEnv = do
  (f, s, t) <- ask
  return f

getCache :: FixT e s i l d (M.Map i (l d))
getCache = do
  (res, _, _) <- get
  return $ M.map fst res

cacheLookup :: Ord i => i -> FixT e s i l d (Maybe (l d))
cacheLookup i = do
  M.lookup i <$> getCache

getState :: FixT e s i l d s
getState = do
  (_, res, _) <- get
  return res

setState :: s -> FixT e s i l d  ()
setState x = do
  (f, s, t) <- get
  put (f, x, t)

updateState :: (s -> s) -> FixT e s i l d  ()
updateState update = do
  st <- getState
  setState $ update st

doBottom :: FixTR e s i l d b
doBottom = ContT (\x -> return ())

localCtx :: Maybe i -> Integer -> FixIn e s i l d a -> FixIn e s i l d a
localCtx i id = local (\(e,_,_) -> (e,i,id))

localCtxT :: Maybe i -> Integer -> FixT e s i l d a -> FixT e s i l d a
localCtxT i id = local (\(e,_,_) -> (e,i,id))

-- Memoization function, memoizes a fixpoint computation by using a cache of previous results and continuations that depend on those results
memo :: (Show d, Show (l d), Show i, Ord i, Lattice l d) => i -> (i -> FixTR e s i l d d) -> FixTR e s i l d d
memo key f = do
  ContT (\c -> do
    (cache, state, newId) <- get
    (env, from, fromId) <- ask
    let cont = ContX c from fromId key
    case M.lookup key cache of
      -- Requesting the result of the memoized function from a different dependant
      Just (xss, conts) -> do
        let tid = toId $ head conts
        put (M.insert key (xss, cont tid:conts) cache, state, newId)
        trace ("\nNew continuation for " ++ show key ++ "\nFrom: " ++ show from ++ "\n") $ return ()
        mapM_ (contV (cont tid)) (elems xss)
      -- First time requesting the memoed function with this key
      Nothing -> do
        trace ("\nNew memo request for  " ++ show key ++ "\nFrom: " ++ show from ++ "\n") $ return ()
        put (M.insert key (bottom, [cont newId]) cache, state, newId + 1)
        runContT (localCtxT (Just key) newId $ f key) (\x ->
            -- For all results push them into the cache
            push key x
            -- trace ("Got new result for " ++ show key ++ " " ++ show x) $ return ()
          )
      )

each :: (Show d, Show b, Ord i, Show (l d), Lattice l d) => [FixTR e s i l d b] -> FixTR e s i l d b
each xs =
  ContT $ \c -> -- Get the continuation
    -- For each monadic fixpoint, run the continuation piece, and call our continuation with each result
    mapM_ (\comp -> runContT comp (\result -> c result)) xs

-- Adds a new result to the cache and calls all continuations that depend on that result
push :: (Show i, Show d, Show (l d), Ord i, Lattice l d) => i -> d -> FixIn e s i l d ()
push key value = do
  -- trace ("Pushing new result for " ++ show key ++ " : " ++ show value) $ return ()
  (cache, state, idV) <- get
  let cur = M.lookup key cache
  let (values, conts) = fromMaybe (bottom, []) cur
  if lte value values then
    -- If the value already exists in the cache
    -- trace ("New result " ++ show value ++ " is already contained in " ++ show xs) $ 
    return ()
  else do
    -- Otherwise, insert the value into the cache and call all continuations in the cache
    -- that depend on changes to this key
    let added = value `insert` values
    put (M.insert key (added, conts) cache, state, idV)
    -- trace ("Calling continuations for " ++ show key ++ " " ++ show (length conts)) $ return ()
    mapM_ (\(ContX c f fi t ti) -> do
      trace ("\nCalling continuation:" ++ show key ++ "\n\tFrom: " ++ show f ++ "\n\tTo: " ++ show t ++ "\n\tNew value: " ++ show value ++ "\n") $ return ()
      c value
      ) conts
    -- trace ("Finished calling continuations for " ++ show key) $ return ()

writeDependencyGraph :: (Show i, Show d, Show (l d), Ord i) => M.Map i (l d, [ContX e s i l d]) -> IO ()
writeDependencyGraph cache = do
  let edges = M.foldlWithKey (\acc k (v, conts) -> acc ++ (fmap (\(ContX _ f fi t ti) -> (f, fi, ti)) conts)) [] cache
  let nodes = S.toList $ S.fromList $ fmap (\(k, fi, ti) -> (fi, k)) edges
  let dot = "digraph G {\n" ++ (intercalate "\n" $ fmap (\(_, a, b) -> show a ++ " -> " ++ show b) edges) ++ "\n" ++ (intercalate "\n" $ fmap (\(fi, k) -> show fi ++ " [label=\"" ++ show k ++ "\"]") nodes) ++ "\n}"
  writeFile "graph.dot" dot
  return ()

-- Runs a fixpoint computation with an environment and state
runFix :: (Show i, Show d, Show (l d), Ord i) => e -> s -> ContT () (ReaderT (e,Maybe i,Integer) (StateT (M.Map i (l d, [ContX e s i l d]), s, Integer) IO)) x -> IO (M.Map i (l d), s)
runFix e s f = do
  (_, (cache, state, _)) <- runStateT (runReaderT (runContT f (\x -> return ())) (e,Nothing,0)) (M.empty, s, 0)
  writeDependencyGraph cache
  return (fmap fst cache, state)

-- Runs a fixpoint computation with an environment, state, and cache 
-- (this allows us to use prior results when those results would not have changed)
-- CAUTION: Results should be invalidated if any of the inputs to the computation change
runFixWithCache :: ContT () (ReaderT (r,Maybe i,Integer) (StateT (b, c, Integer) IO)) a -> r -> b -> c -> Integer -> IO (b, Integer, c)
runFixWithCache f e c s i = do
  (_, (cache, state, i)) <- runStateT (runReaderT (runContT f (\x -> return ())) (e,Nothing,i)) (c, s, i)
  return (cache, i, state)


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
fib :: Int -> FixTR () State (String, Int) (SimpleLattice Int) (SimpleChange Int) (SimpleChange Int)
fib n =
  -- memo using the key ("fib", n) 
  -- (note: "fib" is not actually required, but for mutual recursion you need some way of dispatching based on the function name)
  memo ("fib", n) $ \(_, n) ->
    if n == 0 || n == 1 then return (LChangeSingle 1) else do
      incrementUnique
      x <- fib (n - 1)
      y <- fib (n - 2)
      case (x, y) of
        (LChangeSingle x, LChangeSingle y) -> return $ LChangeSingle (x + y)

swap :: [Int] -> FixTR () () [Int] (SimpleLattice [Int]) (SimpleChange [Int]) (SimpleChange [Int])
swap l = do
  trace ("Swapping " ++ show l) $ return ()
  memo l $ \l ->
    trace ("Memoizing " ++ show l) $
    case l of
      [x, y, z] -> do
        each [swap [y, x], swap [z, y]]
      [x, z] -> return $ LChangeSingle [z, x]

incrementUnique :: FixTR e State b c (SimpleChange Int) ()
incrementUnique = updateState (\state -> state{unique = unique state + 1})

runExample :: IO ()
runExample = do
  comp <- runFix () (State 0) $ fib 6
  trace (show comp) $ return ()
  comp2 <- runFix () () $ swap [1, 2, 3]
  trace (show comp2) $ return ()