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

module Demand.FixpointMonad(
  SimpleLattice(..),
  SLattice,
  SimpleChange(..),
  BasicLattice(..),
  Lattice(..),
  Contains(..),
  doBottom,
  memo,
  push,
  each,
  runFixAEnv,
  runFix,
  runFixWithCache,
  runExample,
  FixTS,
  FixT,
  FixTR,
                        ) where
import Debug.Trace (trace)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust, fromMaybe)
import Control.Monad.Reader (lift, ReaderT (runReaderT))
import Control.Monad.State (StateT (..), MonadState (..), liftIO)
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
newtype ContX e s i l d = ContX { c:: d -> FixIn e s i l d (l d)} -- ReaderT DEnv (StateT (M.Map i (S.Set o, [ContX i o a]), State) Identity) a 
instance Show (ContX e s i l d) where
  show _ = ""

type FixT e s i l d = ContT (l d) (FixIn e s i l d)
type FixIn e s i l d = (ReaderT e (StateT (M.Map i (l d, [ContX e s i l d]), s) IO))

-- instance Lattice l d => MonadFail (FixTR e s i l d) where
--   fail = bottom

-- Memoization function, memoizes a fixpoint computation by using a cache of previous results and continuations that depend on those results
memo :: (Show d, Show (l d), Show i, Ord i, Lattice l d) => i -> (i -> FixTR e s i l d d) -> FixTR e s i l d d
memo key f = do
  ContT (\c -> do
    (cache, state) <- get
    case M.lookup key cache of
      Just (xss, conts) -> do
        put (M.insert key (xss, ContX c:conts) cache, state)
        -- trace ("New dependant on " ++ show key ++ " calling with current state " ++ show xss) $ return ()
        mapM_ c (elems xss)
        return bottom
      Nothing -> do
        -- trace ("Memoizing new result for " ++ show key) $ return ()
        put (M.insert key (bottom, [ContX c]) cache, state)
        runContT (f key) (\x -> do
            push key x
            -- trace ("Got new result for " ++ show key ++ " " ++ show x) $ return ()
            return bottom
          )
      )

each :: (Show d, Show b, Ord i, Show (l d), Lattice l d) => [FixTR e s i l d b] -> FixTR e s i l d b
each xs = do
  ContT $ \c -> do
    mapM_ (\x -> 
      runContT x $ \x ->  
      c x
      ) xs
    return bottom

doBottom :: (Lattice l d) => FixTR e s i l d b
doBottom = ContT $ \c -> return bottom

-- Adds a new result to the cache and calls all continuations that depend on that result
push :: (Show i, Show d, Show (l d), Ord i, Lattice l d) => i -> d -> FixIn e s i l d ()
push key value = do
  -- trace ("Pushing new result for " ++ show key ++ " : " ++ show value) $ return ()
  (cache, state) <- get
  let cur = M.lookup key cache
  let (xs, conts) = fromMaybe (bottom, []) cur
  if lte value xs then
    -- trace ("New result " ++ show value ++ " is already contained in " ++ show xs) $ 
    return ()
  else do
    let added = value `insert` xs
    put (M.insert key (added, conts) cache, state)
    -- trace ("Calling continuations for " ++ show key ++ " " ++ show (length conts)) $ return ()
    mapM_ (\(ContX c) -> c value) conts
    -- trace ("Finished calling continuations for " ++ show key) $ return ()

-- Runs a fixpoint computation with an environment and a state, and an input value
runFixAEnv :: (t -> ContT a (ReaderT r (StateT (M.Map k (b1, b2), c) IO)) a) -> t -> r -> c -> IO (a, M.Map k b1, c)
runFixAEnv f a e s = do
  (res, (cache, state)) <- runStateT (runReaderT (runContT (f a) return) e) (M.empty, s)
  return (res, fmap fst cache, state)

-- Runs a fixpoint computation with an environment and state
runFix :: ContT a (ReaderT r (StateT (M.Map k (b1, b2), c) IO)) a -> r -> c -> IO (a, M.Map k b1, c)
runFix f e s = do
  (res, (cache, state)) <- runStateT (runReaderT (runContT f return) e) (M.empty, s)
  return (res, fmap fst cache, state)

-- Runs a fixpoint computation with an environment, state, and cache 
-- (this allows us to use prior results when those results would not have changed)
-- CAUTION: Results should be invalidated if any of the inputs to the computation change
runFixWithCache :: ContT a (ReaderT r (StateT (b, c) IO)) a -> r -> b -> c -> IO (a, b, c)
runFixWithCache f e c s = do
  (res, (cache, state)) <- runStateT (runReaderT (runContT f return) e) (c, s)
  return (res, cache, state)


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
incrementUnique = do
  (cache, state) <- get
  put (cache, state{unique = unique state + 1})

runExample :: IO ()
runExample = do
  comp <- runStateT (runReaderT (runContT (fib 6) (\x -> return (insert x bottom))) ()) (M.empty, State 0)
  trace (show comp) $ return ()
  comp2 <- runStateT (runReaderT (runContT (swap [1, 2, 3]) (\x -> return (insert x bottom))) ()) (M.empty, ())
  trace (show comp2) $ return ()