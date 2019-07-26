{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TupleSections      #-}

module Language.Fixpoint.Solver.GradualSolution
  ( -- * Create Initial Solution
    init
  ) where

import           Control.Parallel.Strategies
import qualified Data.HashMap.Strict            as M
import           Data.Hashable
import qualified Data.List                      as L
import           Data.Maybe                     (maybeToList, isNothing)
import           Data.Monoid                    ((<>))
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.PrettyPrint ()
import qualified Language.Fixpoint.SortCheck          as So
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types              as F
import qualified Language.Fixpoint.Types.Solutions    as Sol
import           Language.Fixpoint.Types.Constraints  hiding (ws, bs)
import           Prelude                              hiding (init, lookup)
import           Language.Fixpoint.Solver.Sanitize  (symbolEnv)
import Language.Fixpoint.SortCheck

--------------------------------------------------------------------------------
-- | Initial Gradual Solution (from Qualifiers and WF constraints) -------------
--------------------------------------------------------------------------------
init :: (NFData s, Hashable s, F.PPrint s, F.Fixpoint s, Ord s, Show s, F.Fixpoint a) => Config -> F.SInfo s a -> [(F.KVar s, (F.GWInfo s, [F.Expr s]))]
--------------------------------------------------------------------------------
init cfg si = map (elab . refineG si qs genv) gs `using` parList rdeepseq 
  where
    qs         = F.quals si
    gs         = snd <$> gs0
    genv       = instConstants si

    gs0        = L.filter (isGWfc . snd) $ M.toList (F.ws si)

    elab (k,(x,es)) = ((k,) . (x,)) $ (elaborate (F.atLoc F.dummySpan "init") (sEnv (gsym x) (gsort x)) <$> es)
    
    sEnv x s    = isEnv {F.seSort = F.insertSEnv x s (F.seSort isEnv)}
    isEnv       = symbolEnv cfg si


--------------------------------------------------------------------------------
refineG :: (Hashable s, Show s, F.Fixpoint s, F.PPrint s, Ord s) => F.SInfo s a -> [F.Qualifier s] -> F.SEnv s (F.Sort s) -> F.WfC s a -> (F.KVar s, (F.GWInfo s, [F.Expr s]))
refineG fi qs genv w = (k, (F.gwInfo w, Sol.qbExprs qb))
  where 
    (k, qb) = refine fi qs genv w 

refine :: (Ord s, F.PPrint s, F.Fixpoint s, Show s, Hashable s, Eq s) => F.SInfo s a -> [F.Qualifier s] -> F.SEnv s (F.Sort s) -> F.WfC s a -> (F.KVar s, Sol.QBind s)
refine fi qs genv w = refineK (allowHOquals fi) env qs $ F.wrft w
  where
    env             = wenv <> genv
    wenv            = F.sr_sort <$> F.fromListSEnv (F.envCs (F.bs fi) (F.wenv w))

instConstants :: (Hashable s, Eq s) => F.SInfo s a -> F.SEnv s (F.Sort s)
instConstants = F.fromListSEnv . filter notLit . F.toListSEnv . F.gLits
  where
    notLit    = not . F.isLitSymbol . F.symbol . fst


refineK :: (Show s, F.Fixpoint s, F.PPrint s, Ord s, Hashable s) => Bool -> F.SEnv s (F.Sort s) -> [F.Qualifier s] -> (F.Symbol s, F.Sort s, F.KVar s) -> (F.KVar s, Sol.QBind s)
refineK ho env qs (v, t, k) = (k, eqs')
   where
    eqs                     = instK ho env v t qs
    eqs'                    = Sol.qbFilter (okInst env v t) eqs

--------------------------------------------------------------------------------
instK :: (Hashable s, Show s, F.Fixpoint s, F.PPrint s, Ord s, Eq s) => Bool
      -> F.SEnv s (F.Sort s)
      -> F.Symbol s
      -> F.Sort s
      -> [F.Qualifier s]
      -> Sol.QBind s
--------------------------------------------------------------------------------
instK ho env v t = Sol.qb . unique . concatMap (instKQ ho env v t)
  where
    unique       = L.nubBy ((. Sol.eqPred) . (==) . Sol.eqPred)

instKQ :: (Ord s, F.PPrint s, F.Fixpoint s, Show s, Hashable s, Eq s) => Bool
       -> F.SEnv s (F.Sort s)
       -> F.Symbol s
       -> F.Sort s
       -> F.Qualifier s
       -> [Sol.EQual s]
instKQ ho env v t q
  = do (su0, v0) <- candidates senv [(t, [v])] qt
       xs        <- match senv tyss [v0] (So.apply su0 <$> qts)
       return     $ Sol.eQual q (reverse xs)
    where
       qt : qts   = qpSort <$> F.qParams q
       tyss       = instCands ho env
       senv       = (`F.lookupSEnvWithDistance` env)

instCands :: (Hashable s, Eq s) => Bool -> F.SEnv s (F.Sort s) -> [(F.Sort s, [F.Symbol s])]
instCands ho env = filter isOk tyss
  where
    tyss      = groupList [(t, x) | (x, t) <- xts]
    isOk      = if ho then const True else isNothing . F.functionSort . fst
    xts       = F.toListSEnv env

match :: (Ord s, F.PPrint s, F.Fixpoint s) => So.Env s -> [(F.Sort s, [F.Symbol s])] -> [F.Symbol s] -> [F.Sort s] -> [[F.Symbol s]]
match env tyss xs (t : ts)
  = do (su, x) <- candidates env tyss t
       match env tyss (x : xs) (So.apply su <$> ts)
match _   _   xs []
  = return xs

--------------------------------------------------------------------------------
candidates :: (F.Fixpoint s, F.PPrint s, Ord s) => So.Env s -> [(F.Sort s, [F.Symbol s])] -> F.Sort s -> [(So.TVSubst s, F.Symbol s)]
--------------------------------------------------------------------------------
candidates env tyss tx = 
    [(su, y) | (t, ys) <- tyss
             , su      <- maybeToList $ So.unifyFast mono env tx t
             , y       <- ys                                   ]
  where
    mono = So.isMono tx

--------------------------------------------------------------------------------
okInst :: (Hashable s, Ord s, F.PPrint s, F.Fixpoint s, Show s) => F.SEnv s (F.Sort s) -> F.Symbol s -> F.Sort s -> Sol.EQual s -> Bool
--------------------------------------------------------------------------------
okInst env v t eq = isNothing tc
  where
    sr            = F.RR t (F.Reft (v, p))
    p             = Sol.eqPred eq
    tc            = So.checkSorted F.dummySpan env sr 


