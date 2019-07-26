-- | This module has various utility functions for accessing queries.
--   TODO: move the "clients" in Visitors into this module.

module Language.Fixpoint.Types.Utils (
  -- * Domain of a kvar
    kvarDomain

  -- * Free variables in a refinement
  , reftFreeVars

  -- * Deconstruct a SortedReft
  , sortedReftConcKVars
  ) where

import qualified Data.HashMap.Strict                  as M
import qualified Data.HashSet                         as S
import           Data.Hashable

import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Environments
import           Language.Fixpoint.Types.Constraints
import           Language.Fixpoint.Types.PrettyPrint (Fixpoint)

--------------------------------------------------------------------------------
-- | Compute the domain of a kvar
--------------------------------------------------------------------------------
kvarDomain :: (Eq s, Hashable s) => SInfo s a -> KVar s -> [Symbol s]
--------------------------------------------------------------------------------
kvarDomain si k = domain (bs si) (getWfC si k)

domain :: BindEnv s -> WfC s a -> [Symbol s]
domain be wfc = fst3 (wrft wfc) : map fst (envCs be $ wenv wfc)

getWfC :: (Eq s, Hashable s) => SInfo s a -> KVar s -> WfC s a
getWfC si k = ws si M.! k

--------------------------------------------------------------------------------
-- | Free variables of a refinement
--------------------------------------------------------------------------------
--TODO deduplicate (also in Solver/UniqifyBinds)
reftFreeVars :: (Ord s, Show s, Hashable s, Eq s, Fixpoint s) => Reft s -> S.HashSet (Symbol s)
reftFreeVars r@(Reft (v, _)) = S.delete v $ S.fromList $ syms r

--------------------------------------------------------------------------------
-- | Split a SortedReft into its concrete and KVar components
--------------------------------------------------------------------------------
sortedReftConcKVars :: (Show s, Fixpoint s, Hashable s, Ord s) => Symbol s -> SortedReft s -> ([Pred s], [KVSub s], [KVSub s])
sortedReftConcKVars x sr = go [] [] [] ves
  where
    ves                  = [(v, p `subst1` (v, eVar x)) | Reft (v, p) <- rs ]
    rs                   = reftConjuncts (sr_reft sr)
    t                    = sr_sort sr

    go ps ks gs ((v, PKVar k su    ):xs) = go ps (KVS v t k su:ks) gs xs 
    go ps ks gs ((v, PGrad k su _ _):xs) = go ps ks (KVS v t k su:gs) xs 
    go ps ks gs ((_, p):xs)              = go (p:ps) ks gs xs 
    go ps ks gs []                       = (ps, ks, gs)
