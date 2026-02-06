{-# LANGUAGE DeriveGeneric #-}
module Core.FlowAnalysis.Full.Report where

import Data.Aeson (ToJSON, encode)
import GHC.Generics (Generic)
import qualified Data.Map as Map
import qualified Data.ByteString.Lazy as B
import Data.Fixed (Pico)

-- | Metrics for a specific sensitivity configuration.
-- To represent a 0-CFA baseline, use a specific runID (e.g., "0-0").
-- The Python analysis script will treat the first element of each cardinality list 
-- as the baseline value for productivity and expansion calculations.
data PolyVariantMetrics = PolyVariantMetrics
  { variant             :: String -- DMCFA / DMCFAE
  , d                   :: Int   -- ^ Identifier for the sensitivity level (e.g., "V2-K1" or "0-0").
  , m                   :: Int
  , benchmarkName       :: String   -- ^ Name of the benchmark being analyzed.
  , analysisTimes       :: [Pico] -- ^ Wall-clock time samples in seconds for statistical averaging.
  , isTimeout           :: Bool     -- ^ Flag indicating if the analysis exceeded the time limit.
  , storeMetrics        :: Maybe StoreMetrics -- ^ Detailed metrics; 'Nothing' indicates a timeout or crash.
  } deriving (Generic, Show)

-- | Partitioned store metrics with explicit literal/structural separation.
-- This structure facilitates the "Lattice of Sensitivities" approach (Smaragdakis et al., 2011).
data StoreMetrics = StoreMetrics
  { numStoreAddresses    :: Int -- ^ Total unique addresses in the polyvariant store (Value + Continuation).
  , numLitAddresses      :: Int -- ^ Addresses containing literals (Lattice values).
  , numStructAddresses   :: Int -- ^ Addresses containing closures or constructors.
  , numContAddresses     :: Int -- ^ Continuation addresses.
  , numIndirectCallTargetExprs  :: Int --
  , numTotalFixInputStates :: Int -- ^ Total FixInput states explored (cache size)
  -- | Precise counts (Singletons)
  -- Following Van Horn & Might (2010), we distinguish between semantic and structural precision.
  , valSemSingletons     :: Int -- ^ Semantic singletons across all value addresses.
  , contSemSingletons    :: Int -- ^ Semantic singletons in the continuation store.
  , valStrSingletons     :: Int -- ^ Structural singletons (Unique tags) in structural addresses.
  , contStrSingletons    :: Int -- ^ Structural singletons (Unique templates) in continuation addresses.
  , cont0CFAStrSingletons :: Int -- ^ Structural singletons after aggregating by 0CFA key (kAddrId).
  , val0CFAStrSingletons :: Int -- ^ Structural singletons after aggregating by 0CFA key (vAddrId).
  , combined0CFAStrSingletons :: Int -- ^ Combined value+continuation structural singletons at 0CFA level.
  , semReturnSingletons  :: Int -- ^ Call sites returning a precise semantic value.
  , strReturnSingletons  :: Int -- ^ Call sites returning a precise structural value
  , semTargetSingletons  :: Int -- ^ Call targets var expression returning a precise closure.
  , strTargetSingletons  :: Int -- ^ Call targets var expression returning a precise lambda.
  -- | Data Precision
  , literalTopCount      :: Int -- ^ Literal addresses that hit Top (-1 in histogram).
  , literal0CFATopCount  :: Int -- ^ Literal addresses hitting Top after 0CFA aggregation.
  -- | Context Explosion Metrics
  , exprContextHistogram :: Map.Map Int Int -- ^ Histogram: N contexts -> count of expressions with N contexts.
  , contContextHistogram :: Map.Map Int Int -- ^ Histogram: N contexts -> count of continuations with N contexts.
  -- | Productivity Mappings
  -- These maps store the cardinalities observed at each program point across all contexts.
  -- For 0-CFA runs, these lists will contain exactly one element.
  , exprToValSemSizes    :: Map.Map String [Int] -- ^ Exp ID to closure (constructor) set size.
  , structToContSemSizes :: Map.Map String [Int] -- ^ Structural ID to full frame set size.
  , callToSemRetSizes    :: Map.Map String [Int] -- ^ Call site ID to return value set size.
  , structToStrRetSizes  :: Map.Map String [Int] -- ^ Structural ID to structural return set size.
  -- | Structural Productivity Mappings
  -- Tracking Lambda/Constructor/Frame-Template counts per ID (Shivers, 1991).
  , exprToValStrSizes    :: Map.Map String [Int] -- ^ Exp ID to unique Lambda/Constructor tag count.
  , structToContStrSizes :: Map.Map String [Int] -- ^ Structural ID to unique frame-template count.
  , semCallTargetSizes   :: Map.Map String [Int] -- Call target var expression to closure set size
  , strCallTargetSizes   :: Map.Map String [Int] -- Call target var expression to lambda set size
  } deriving (Generic, Show)

 

instance ToJSON PolyVariantMetrics
instance ToJSON StoreMetrics