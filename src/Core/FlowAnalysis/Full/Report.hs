{-# LANGUAGE DeriveGeneric #-}
module Core.FlowAnalysis.Full.Report where

import Data.Aeson (ToJSON, encode)
import GHC.Generics (Generic)
import qualified Data.Map as Map
import qualified Data.ByteString.Lazy as B

-- | Baseline data from 0-CFA anchoring. Used to calculate Expansion and Productivity.
-- Cited as the standard monovariant control (Shivers, 1991).
data BaselineData = BaselineData
  { programName          :: String  -- ^ Unique name of the benchmark program.
  , bValueAddrs          :: Int     -- ^ Count of reachable addresses in the 0-CFA value store.
  , bContAddrs           :: Int     -- ^ Count of reachable addresses in the 0-CFA continuation store.
  -- | Baseline semantic cardinalities (Full Environment + Value) for productivity comparison.
  , bExprToValSemSizes   :: Map.Map String Int -- ^ Exp ID to closure/literal set size.
  , bExprToValStrSizes   :: Map.Map String Int -- ^ Exp ID to unique Lambda/Constructor tag count.
  , bStructToContSemSizes :: Map.Map String Int -- ^ Structural ID to full frame set size.
  , bStructToContStrSizes :: Map.Map String Int -- ^ Structural ID to unique frame-template count.
  , bCallToSemRetSizes   :: Map.Map String Int -- ^ Call site ID to return value set size.
  , bStructToStrRetSizes :: Map.Map String Int -- ^ Structural ID to structural return set size.
  } deriving (Generic, Show)

-- | Container for a specific sensitivity configuration run (e.g., polyvariant settings V, K).
data PolyVariantMetrics = PolyVariantMetrics
  { runID               :: String   -- ^ Identifier for the sensitivity level (e.g., "V2-K1").
  , benchmarkName       :: String   -- ^ Name of the benchmark being analyzed.
  , analysisTimes       :: [Double] -- ^ Wall-clock time samples in seconds for statistical averaging.
  , isTimeout           :: Bool     -- ^ Flag indicating if the analysis exceeded the time limit.
  , storeMetrics        :: Maybe StoreMetrics -- ^ Detailed metrics; 'Nothing' indicates a timeout or crash.
  } deriving (Generic, Show)

-- | Detailed partitioned store and return flow metrics.
data StoreMetrics = StoreMetrics
  { numValueAddresses    :: Int -- ^ Total unique addresses in the polyvariant value store.
  , numContAddresses     :: Int -- ^ Total unique addresses in the polyvariant continuation store.
  -- | Semantic Singletons: Addresses containing exactly one full value (Closure/Literal/Constructor).
  , valSemSingletons     :: Int 
  , contSemSingletons    :: Int 
  -- | Structural Singletons: Addresses resolving to a single code-level target (Lambda/Frame-Template).
  , valStrSingletons     :: Int 
  , contStrSingletons    :: Int 
  , semReturnSingletons  :: Int -- ^ Call sites returning a precise semantic value.
  , strReturnSingletons  :: Int -- ^ Continuation applications returning to a precise structural state.
  -- | Data Precision Metrics
  , literalTopCount      :: Int -- ^ Number of literal addresses that have collapsed to the lattice 'Top'.
  -- | Histograms for Semantic Cardinality. Key is cardinality, value is frequency. 
  -- Use -1 for Lattice 'Top' (Infinity).
  , valCardHist          :: Map.Map Int Int
  , contCardHist         :: Map.Map Int Int
  -- | Productivity Mappings: ID -> List of cardinalities found across all polyvariant contexts.
  , exprToValSemSizes    :: Map.Map String [Int]
  , structToContSemSizes :: Map.Map String [Int]
  , callToSemRetSizes    :: Map.Map String [Int]
  , structToStrRetSizes  :: Map.Map String [Int]
  -- | Structural Productivity Mappings: Tracks lambda/template counts per ID.
  , exprToValStrSizes    :: Map.Map String [Int]
  , structToContStrSizes :: Map.Map String [Int]
  } deriving (Generic, Show)

instance ToJSON BaselineData
instance ToJSON PolyVariantMetrics
instance ToJSON StoreMetrics