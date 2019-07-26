{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}

-- | This is a wrapper around IO that permits SMT queries

module Language.Fixpoint.Solver.Monad
       ( -- * Type
         SolveM

         -- * Execution
       , runSolverM

         -- * Get Binds
       , getBinds

         -- * SMT Query
       , filterRequired
       , filterValid
       , filterValidGradual
       , checkSat
       , smtEnablembqi

         -- * Debug
       , Stats
       , tickIter
       , stats
       , numIter
       )
       where

import           Control.DeepSeq
import           GHC.Generics
import           Language.Fixpoint.Utils.Progress
import qualified Language.Fixpoint.Types.Config  as C
import           Language.Fixpoint.Types.Config  (Config)
import qualified Language.Fixpoint.Types   as F
-- import qualified Language.Fixpoint.Misc    as Misc
-- import           Language.Fixpoint.SortCheck
import qualified Language.Fixpoint.Types.Solutions as F
import           Language.Fixpoint.Types   (pprint)
-- import qualified Language.Fixpoint.Types.Errors  as E
import           Language.Fixpoint.Smt.Serialize ()
import           Language.Fixpoint.Types.PrettyPrint ()
import           Language.Fixpoint.Smt.Interface
-- import qualified Language.Fixpoint.Smt.Theories as Thy
import           Language.Fixpoint.Solver.Sanitize
import           Language.Fixpoint.Graph.Types (SolverInfo (..))
-- import           Language.Fixpoint.Solver.Solution
-- import           Data.Maybe           (catMaybes)
import           Data.List            (partition)
-- import           Data.Char            (isUpper)
import           Text.PrettyPrint.HughesPJ (text)
import           Control.Monad.State.Strict
import qualified Data.HashMap.Strict as M
import           Data.Hashable
import           Data.Maybe (catMaybes)
import           Control.Exception.Base (bracket)

--------------------------------------------------------------------------------
-- | Solver Monadic API --------------------------------------------------------
--------------------------------------------------------------------------------

type SolveM s = StateT (SolverState s) IO

data SolverState s = SS 
  { ssCtx     :: !(Context s)          -- ^ SMT Solver Context
  , ssBinds   :: !(F.BindEnv s)        -- ^ All variables and types
  , ssStats   :: !Stats            -- ^ Solver Statistics
  }

data Stats = Stats 
  { numCstr :: !Int -- ^ # Horn Constraints
  , numIter :: !Int -- ^ # Refine Iterations
  , numBrkt :: !Int -- ^ # smtBracket    calls (push/pop)
  , numChck :: !Int -- ^ # smtCheckUnsat calls
  , numVald :: !Int -- ^ # times SMT said RHS Valid
  } deriving (Show, Generic)

instance NFData Stats

stats0    :: F.GInfo s c b -> Stats
stats0 fi = Stats nCs 0 0 0 0
  where
    nCs   = M.size $ F.cm fi


instance F.PTable Stats where
  ptable s = F.DocTable [ (text "# Constraints"         , pprint (numCstr s))
                        , (text "# Refine Iterations"   , pprint (numIter s))
                        , (text "# SMT Brackets"        , pprint (numBrkt s))
                        , (text "# SMT Queries (Valid)" , pprint (numVald s))
                        , (text "# SMT Queries (Total)" , pprint (numChck s))
                        ]

--------------------------------------------------------------------------------
runSolverM :: (SMTLIB2 s s, Hashable s, F.PPrint s, F.Fixpoint s, Ord s, Show s) => Config -> SolverInfo s b c -> SolveM s a -> IO a
--------------------------------------------------------------------------------
runSolverM cfg sI act =
  bracket acquire release $ \ctx -> do
    res <- runStateT act' (s0 ctx)
    smtWrite ctx "(exit)"
    return (fst res)
  where
    s0 ctx   = SS ctx be (stats0 fi)
    act'     = assumesAxioms (F.asserts fi) >> act
    release  = cleanupContext
    acquire  = makeContextWithSEnv cfg file initEnv
    initEnv  = symbolEnv   cfg fi
    be       = F.bs fi
    file     = C.srcFile cfg
    -- only linear arithmentic when: linear flag is on or solver /= Z3
    -- lar     = linear cfg || Z3 /= solver cfg
    fi       = (siQuery sI) {F.hoInfo = F.HOI (C.allowHO cfg) (C.allowHOqs cfg)}


--------------------------------------------------------------------------------
getBinds :: SolveM s (F.BindEnv s)
--------------------------------------------------------------------------------
getBinds = ssBinds <$> get

--------------------------------------------------------------------------------
getIter :: SolveM s Int
--------------------------------------------------------------------------------
getIter = numIter . ssStats <$> get

--------------------------------------------------------------------------------
incIter, incBrkt :: SolveM s ()
--------------------------------------------------------------------------------
incIter   = modifyStats $ \s -> s {numIter = 1 + numIter s}
incBrkt   = modifyStats $ \s -> s {numBrkt = 1 + numBrkt s}

--------------------------------------------------------------------------------
incChck, incVald :: Int -> SolveM s ()
--------------------------------------------------------------------------------
incChck n = modifyStats $ \s -> s {numChck = n + numChck s}
incVald n = modifyStats $ \s -> s {numVald = n + numVald s}

withContext :: (Context s -> IO a) -> SolveM s a
withContext k = (lift . k) =<< getContext

getContext :: SolveM s (Context s)
getContext = ssCtx <$> get

modifyStats :: (Stats -> Stats) -> SolveM s ()
modifyStats f = modify $ \s -> s { ssStats = f (ssStats s) }

--------------------------------------------------------------------------------
-- | SMT Interface -------------------------------------------------------------
--------------------------------------------------------------------------------
-- | `filterRequired [(x1, p1),...,(xn, pn)] q` returns a minimal list [xi] s.t.
--   /\ [pi] => q
--------------------------------------------------------------------------------
filterRequired :: F.Cand s a -> F.Expr s -> SolveM s [a]
--------------------------------------------------------------------------------
filterRequired = error "TBD:filterRequired"

{-
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

; Z3 will only track assertions that are named.

(assert (< 0 x))
(assert (! (< 0 y)       :named b2))
(assert (! (< x 10)      :named b3))
(assert (! (< y 10)      :named b4))
(assert (! (< (+ x y) 0) :named bR))
(check-sat)
(get-unsat-core)

> unsat (b2 bR)
-}

--------------------------------------------------------------------------------
-- | `filterValid p [(x1, q1),...,(xn, qn)]` returns the list `[ xi | p => qi]`
--------------------------------------------------------------------------------
filterValid :: (F.PPrint s, F.Fixpoint s, Ord s, SMTLIB2 s s, Hashable s, Show s) => F.SrcSpan -> F.Expr s -> F.Cand s a -> SolveM s [a]
--------------------------------------------------------------------------------
filterValid sp p qs = do
  qs' <- withContext $ \me ->
           smtBracket me "filterValidLHS" $
             filterValid_ sp p qs me
  -- stats
  incBrkt
  incChck (length qs)
  incVald (length qs')
  return qs'

filterValid_ :: (Show s, Hashable s, SMTLIB2 s s, Ord s, F.Fixpoint s, F.PPrint s) => F.SrcSpan -> F.Expr s -> F.Cand s a -> Context s -> IO [a]
filterValid_ sp p qs me = catMaybes <$> do
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracketAt sp me "filterValidRHS" $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      return $ if valid then Just x else Nothing


--------------------------------------------------------------------------------
-- | `filterValidGradual ps [(x1, q1),...,(xn, qn)]` returns the list `[ xi | p => qi]`
-- | for some p in the list ps
--------------------------------------------------------------------------------
filterValidGradual :: (F.PPrint s, F.Fixpoint s, Ord s, SMTLIB2 s s, Hashable s, Show s) => [F.Expr s] -> F.Cand s a -> SolveM s [a]
--------------------------------------------------------------------------------
filterValidGradual p qs = do
  qs' <- withContext $ \me ->
           smtBracket me "filterValidGradualLHS" $
             filterValidGradual_ p qs me
  -- stats
  incBrkt
  incChck (length qs)
  incVald (length qs')
  return qs'

filterValidGradual_ :: forall s a. (F.PPrint s, F.Fixpoint s, Ord s, Show s, Hashable s, SMTLIB2 s s) => [F.Expr s] -> F.Cand s a -> Context s -> IO [a]
filterValidGradual_ ps qs me
  = (map snd . fst) <$> foldM partitionCandidates ([], qs) ps
  where
    partitionCandidates :: (F.Cand s a, F.Cand s a) -> F.Expr s -> IO (F.Cand s a, F.Cand s a)
    partitionCandidates (ok, candidates) p = do
      (valids', invalids')  <- partition snd <$> filterValidOne_ p candidates me
      let (valids, invalids) = (fst <$> valids', fst <$> invalids')
      return (ok ++ valids, invalids)

filterValidOne_ :: (Show s, Hashable s, SMTLIB2 s s, Ord s, F.Fixpoint s, F.PPrint s) => F.Expr s -> F.Cand s a -> Context s -> IO [((F.Expr s, a), Bool)]
filterValidOne_ p qs me = do
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracket me "filterValidRHS" $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      return $ ((q, x), valid)

smtEnablembqi :: SolveM s ()
smtEnablembqi
  = withContext $ \me ->
      smtWrite me "(set-option :smt.mbqi true)"

--------------------------------------------------------------------------------
checkSat :: (F.PPrint s, F.Fixpoint s, Ord s, SMTLIB2 s s, Hashable s, Show s) => F.Expr s -> SolveM s  Bool
--------------------------------------------------------------------------------
checkSat p
  = withContext $ \me ->
      smtBracket me "checkSat" $
        smtCheckSat me p

--------------------------------------------------------------------------------
assumesAxioms :: (Show s, Hashable s, SMTLIB2 s s, Ord s, F.Fixpoint s, F.PPrint s) => [F.Triggered (F.Expr s)] -> SolveM s ()
--------------------------------------------------------------------------------
assumesAxioms es = withContext $ \me -> forM_  es $ smtAssertAxiom me


---------------------------------------------------------------------------
stats :: SolveM s Stats
---------------------------------------------------------------------------
stats = ssStats <$> get

---------------------------------------------------------------------------
tickIter :: Bool -> SolveM s Int
---------------------------------------------------------------------------
tickIter newScc = progIter newScc >> incIter >> getIter

progIter :: Bool -> SolveM s ()
progIter newScc = lift $ when newScc progressTick
