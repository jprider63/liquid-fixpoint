{-# LANGUAGE FlexibleContexts     #-}

-- | This module exports a single function that computes the dependency
-- information needed to eliminate non-cut KVars, and then transitively
-- collapse the resulting constraint dependencies.
-- See the type of `SolverInfo` for details.

module Language.Fixpoint.Solver.Eliminate ( solverInfo ) where

import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M
import           Data.Hashable

import           Language.Fixpoint.Types.Config    (Config)
import qualified Language.Fixpoint.Types.Solutions as Sol
import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Visitor   (kvars, isConcC)
import           Language.Fixpoint.Graph
import           Language.Fixpoint.Misc            (safeLookup, group, errorstar)
import           Language.Fixpoint.Solver.Sanitize

--------------------------------------------------------------------------------
-- | `solverInfo` constructs a `SolverInfo` comprising the Solution and various
--   indices needed by the worklist-based refinement loop
--------------------------------------------------------------------------------
solverInfo :: (PPrint s, Fixpoint s, Ord s, Show s, Hashable s, Eq s) => Config -> SInfo s a -> SolverInfo s a b
--------------------------------------------------------------------------------
solverInfo cfg sI = SI sHyp sI' cD cKs
  where
    cD             = elimDeps     sI es nKs ebs
    sI'            = cutSInfo     sI kI cKs
    sHyp           = Sol.fromList sE mempty mempty kHyps kS [] $ fromListSEnv [ (x, (i, sr_sort sr)) | (i,x,sr) <- bindEnvToList (bs sI)]
    kHyps          = nonCutHyps   sI kI nKs
    kI             = kIndex       sI
    (es, cKs, nKs) = kutVars cfg  sI
    kS             = kvScopes     sI es
    sE             = symbolEnv   cfg sI
    ebs            = S.fromList $ fst <$> flip lookupBindEnv (bs sI) <$> (ebinds sI)


--------------------------------------------------------------------------------
kvScopes :: (Hashable s, Eq s) => SInfo s a -> [CEdge s] -> M.HashMap (KVar s) IBindEnv
kvScopes sI es = is2env <$> kiM
  where
    is2env = foldr1 intersectionIBindEnv . fmap (senv . getSubC sI)
    kiM    = group $ [(k, i) | (Cstr i, KVar k) <- es ] ++
                     [(k, i) | (KVar k, Cstr i) <- es ]

--------------------------------------------------------------------------------

cutSInfo :: (Hashable s, Eq s) => SInfo s a -> KIndex s -> S.HashSet (KVar s) -> SInfo s a
cutSInfo si kI cKs = si { ws = ws', cm = cm' }
  where
    ws'   = M.filterWithKey (\k _ -> S.member k cKs) (ws si)
    cm'   = M.filterWithKey (\i c -> S.member i cs || isConcC c) (cm si)
    cs    = S.fromList      (concatMap kCs cKs)
    kCs k = M.lookupDefault [] k kI

kutVars :: (Ord s, Show s, Hashable s, Fixpoint s) => Config -> SInfo s a -> ([CEdge s], S.HashSet (KVar s), S.HashSet (KVar s))
kutVars cfg si   = (es, depCuts ds, depNonCuts ds)
  where
    (es, ds)     = elimVars cfg si

--------------------------------------------------------------------------------
-- | Map each `KVar` to the list of constraints on which it appears on RHS
--------------------------------------------------------------------------------
type KIndex s = M.HashMap (KVar s) [Integer]

--------------------------------------------------------------------------------
kIndex     :: (Hashable s, Eq s) => SInfo s a -> KIndex s
--------------------------------------------------------------------------------
kIndex si  = group [(k, i) | (i, c) <- iCs, k <- rkvars c]
  where
    iCs    = M.toList (cm si)
    rkvars = kvars . crhs

nonCutHyps :: (Eq s, Hashable s) => SInfo s a -> KIndex s -> S.HashSet (KVar s) -> [(KVar s, Sol.Hyp s)]
nonCutHyps si kI nKs = [ (k, nonCutHyp kI si k) | k <- S.toList nKs ]


nonCutHyp  :: (Hashable s, Eq s) => KIndex s -> SInfo s a -> KVar s -> Sol.Hyp s
nonCutHyp kI si k = nonCutCube <$> cs
  where
    cs            = getSubC   si <$> M.lookupDefault [] k kI

nonCutCube :: SimpC s a -> Sol.Cube s
nonCutCube c = Sol.Cube (senv c) (rhsSubst c) (subcId c) (stag c)

rhsSubst :: SimpC s a -> Subst s
rhsSubst             = rsu . crhs
  where
    rsu (PKVar _ su) = su
    rsu _            = errorstar "Eliminate.rhsSubst called on bad input"

getSubC :: SInfo s a -> Integer -> SimpC s a
getSubC si i = safeLookup msg i (cm si)
  where
    msg = "getSubC: " ++ show i
