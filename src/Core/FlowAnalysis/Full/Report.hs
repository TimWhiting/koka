{-# LANGUAGE DeriveGeneric #-}
module Core.FlowAnalysis.Full.Report where

import Data.Aeson (ToJSON, encode)
import GHC.Generics (Generic)
import qualified Data.Map as Map
import qualified Data.ByteString.Lazy as B

-- | Baseline data from 0-CFA anchoring.
-- Cited as the standard monovariant control (Shivers, 1991).
data BaselineData = BaselineData
  { programName          :: String
  , bStoreAddrs          :: Int -- ^ Total unique addresses in the 0-CFA store (Value + Continuation)
  , bValueAddrs          :: Int -- ^ Total 0-CFA value addresses (for context depth)
  , bContAddrs           :: Int -- ^ Total 0-CFA continuation addresses
  -- | Baseline semantic cardinalities (Full Environment + Value) for productivity comparison.
  , bExprToValSemSizes   :: Map.Map String Int 
  , bExprToValStrSizes   :: Map.Map String Int 
  , bStructToContSemSizes :: Map.Map String Int 
  , bStructToContStrSizes :: Map.Map String Int 
  , bCallToSemRetSizes   :: Map.Map String Int 
  , bStructToStrRetSizes :: Map.Map String Int 
  } deriving (Generic, Show)

-- | Metrics for a specific sensitivity configuration.
data PolyVariantMetrics = PolyVariantMetrics
  { runID               :: String 
  , benchmarkName       :: String
  , analysisTimes       :: [Double] 
  , isTimeout           :: Bool
  , storeMetrics        :: Maybe StoreMetrics
  } deriving (Generic, Show)

-- | Partitioned store metrics with explicit literal/structural separation.
data StoreMetrics = StoreMetrics
  { numStoreAddresses    :: Int -- ^ Total unique addresses in the polyvariant store
  , numLitAddresses      :: Int -- ^ Addresses containing literals (Lattice values)
  , numStructAddresses   :: Int -- ^ Addresses containing closures or constructors
  , numContAddresses     :: Int -- ^ Continuation addresses
  -- | Precise counts (Singletons)
  , valSemSingletons     :: Int -- ^ Semantic singletons across all value addresses
  , contSemSingletons    :: Int 
  , valStrSingletons     :: Int -- ^ Structural singletons (Unique tags) in structural addresses
  , contStrSingletons    :: Int 
  , semReturnSingletons  :: Int 
  , strReturnSingletons  :: Int 
  -- | Data Precision
  , literalTopCount      :: Int -- ^ Literal addresses that hit Top (-1 in histogram)
  -- | Cardinality Histograms
  , valCardHist          :: Map.Map Int Int
  , contCardHist         :: Map.Map Int Int
  -- | Productivity Mappings
  , exprToValSemSizes    :: Map.Map String [Int]
  , structToContSemSizes :: Map.Map String [Int]
  , callToSemRetSizes    :: Map.Map String [Int]
  , structToStrRetSizes  :: Map.Map String [Int]
  , exprToValStrSizes    :: Map.Map String [Int]
  , structToContStrSizes :: Map.Map String [Int]
  } deriving (Generic, Show)

instance ToJSON BaselineData
instance ToJSON PolyVariantMetrics
instance ToJSON StoreMetrics