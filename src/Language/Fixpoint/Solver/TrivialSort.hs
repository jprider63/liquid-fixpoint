{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Fixpoint.Solver.TrivialSort (nontrivsorts) where

import           GHC.Generics        (Generic)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Visitor
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types hiding (simplify)
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Misc
import qualified Data.HashSet            as S
import           Data.Hashable
import qualified Data.HashMap.Strict     as M
import           Data.List (foldl')
import qualified Data.Graph              as G
import           Data.Maybe
import           Text.Printf
import           Debug.Trace

-------------------------------------------------------------------------
nontrivsorts :: (Ord s, Fixpoint s, Hashable s, Show s, PPrint s, Fixpoint a) => Config -> FInfo s a -> IO (Result s a)
-------------------------------------------------------------------------
nontrivsorts cfg fi = do
  let fi' = simplify' cfg fi
  writeFInfo cfg fi' $ queryFile Out cfg
  return mempty

simplify' :: (Show s, Fixpoint s, Hashable s, Ord s) => Config -> FInfo s a -> FInfo s a
simplify' _ fi = simplifyFInfo (mkNonTrivSorts fi) fi

--------------------------------------------------------------------
-- | The main data types
--------------------------------------------------------------------
type NonTrivSorts s = S.HashSet (Sort s)
type KVarMap s      = M.HashMap (KVar s) [Sort s]
data Polarity       = Lhs | Rhs
type TrivInfo s     = (NonTrivSorts s, KVarMap s)
--------------------------------------------------------------------

--------------------------------------------------------------------
mkNonTrivSorts :: (Hashable s, Ord s) => FInfo s a -> NonTrivSorts s
--------------------------------------------------------------------
mkNonTrivSorts = {- tracepp "mkNonTrivSorts: " . -}  nonTrivSorts . trivInfo

--------------------------------------------------------------------
nonTrivSorts :: (Ord s, Eq s, Hashable s) => TrivInfo s -> NonTrivSorts s
--------------------------------------------------------------------
nonTrivSorts ti = S.fromList [s | S s <- ntvs]
  where
    ntvs        = [fst3 (f v) | v <- G.reachable g root]
    (g, f, fv)  = G.graphFromEdges $ ntGraph ti
    root        = fromMaybe err    $ fv NTV
    err         = errorstar "nonTrivSorts: cannot find root!"

ntGraph :: (Hashable s, Eq s) => TrivInfo s -> NTG s
ntGraph ti = [(v,v,vs) | (v, vs) <- groupList $ ntEdges ti]

ntEdges :: TrivInfo s -> [(NTV s, NTV s)]
ntEdges (nts, kvm) = es ++ [(v, u) | (u, v) <- es]
  where
    es = [(NTV, S s) | s       <- S.toList nts         ]
      ++ [(K k, S s) | (k, ss) <- M.toList kvm, s <- ss]

type NTG s = [(NTV s, NTV s, [NTV s])]

data NTV s = NTV
           | K !(KVar s)
           | S !(Sort s)
           deriving (Eq, Ord, Show, Generic)

instance (Hashable s) => Hashable (NTV s)

--------------------------------------------------------------------
trivInfo :: (Hashable s, Eq s) => FInfo s a -> TrivInfo s
--------------------------------------------------------------------
trivInfo fi = updTISubCs (M.elems $ cm fi)
            . updTIBinds (bs fi)
            $ (S.empty, M.empty)

updTISubCs :: (Eq s, Hashable s) => [SubC s a] -> TrivInfo s -> TrivInfo s
updTISubCs cs ti = foldl' (flip updTISubC) ti cs

updTISubC :: (Hashable s, Eq s) => SubC s a -> TrivInfo s -> TrivInfo s
updTISubC c = updTI Lhs (slhs c) . updTI Rhs (srhs c)

updTIBinds :: (Hashable s, Eq s) => BindEnv s -> TrivInfo s -> TrivInfo s
updTIBinds be ti = foldl' (flip (updTI Lhs)) ti ts
  where
    ts           = [t | (_,_,t) <- bindEnvToList be]

--------------------------------------------------------------------
updTI :: (Eq s, Hashable s) => Polarity -> SortedReft s -> TrivInfo s -> TrivInfo s
--------------------------------------------------------------------
updTI p (RR t r) = addKVs t (kvars r) . addNTS p r t

addNTS :: (Eq s, Hashable s) => Polarity -> Reft s -> Sort s -> TrivInfo s -> TrivInfo s
addNTS p r t ti
  | isNTR p r = addSort t ti
  | otherwise = ti

addKVs :: (Hashable s, Eq s) => Sort s -> [KVar s] -> TrivInfo s -> TrivInfo s
addKVs t ks ti     = foldl' addK ti ks
  where
    addK (ts, m) k = (ts, inserts k t m)

addSort :: (Hashable s, Eq s) => Sort s -> TrivInfo s -> TrivInfo s
addSort t (ts, m) = (S.insert t ts, m)

--------------------------------------------------------------------
isNTR :: (Eq s) => Polarity -> Reft s -> Bool
--------------------------------------------------------------------
isNTR Rhs = not . trivR
isNTR Lhs = not . trivOrSingR

trivR :: (Eq s) => Reft s -> Bool
trivR = all trivP . conjuncts . reftPred

trivOrSingR :: (Eq s) => Reft s -> Bool
trivOrSingR (Reft (v, p)) = all trivOrSingP $ conjuncts p
  where
    trivOrSingP p         = trivP p || singP v p

trivP :: (Eq s) => Expr s -> Bool
trivP (PKVar {}) = True
trivP p          = isTautoPred p

singP :: (Eq s) => Symbol s -> Expr s -> Bool
singP v (PAtom Eq (EVar x) _)
  | v == x                    = True
singP v (PAtom Eq _ (EVar x))
  | v == x                    = True
singP _ _                     = False

-------------------------------------------------------------------------
simplifyFInfo :: (Ord s, Hashable s, Fixpoint s, Show s, Eq s) => NonTrivSorts s -> FInfo s a -> FInfo s a
-------------------------------------------------------------------------
simplifyFInfo tm fi = fi {
     cm   = simplifySubCs   tm $ cm fi
   , ws   = simplifyWfCs    tm $ ws fi
   , bs   = simplifyBindEnv tm $ bs fi
}

simplifyBindEnv :: (Ord s, Hashable s, Fixpoint s, Show s) => NonTrivSorts s -> BindEnv s -> BindEnv s
simplifyBindEnv tm = mapBindEnv (\_ (x, sr) -> (x, simplifySortedReft tm sr))

simplifyWfCs :: (Eq s, Hashable s) => NonTrivSorts s -> M.HashMap (KVar s) (WfC s a) -> M.HashMap (KVar s) (WfC s a)
simplifyWfCs tm = M.filter (isNonTrivialSort tm . snd3 . wrft)

simplifySubCs :: (Show s, Fixpoint s, Hashable s, Ord s, Eq k, Hashable k)
              => NonTrivSorts s -> M.HashMap k (SubC s a) -> M.HashMap k (SubC s a)
simplifySubCs ti cm = trace msg cm'
  where
    cm' = tx cm
    tx  = M.fromList . mapMaybe (simplifySubC ti) . M.toList
    msg = printf "simplifySUBC: before = %d, after = %d \n" n n'
    n   = M.size cm
    n'  = M.size cm'

simplifySubC :: forall s a b. (Ord s, Hashable s, Fixpoint s, Show s) => NonTrivSorts s -> (b, SubC s a) -> Maybe (b, SubC s a)
simplifySubC tm (i, c)
 | isNonTrivial @s @_ srhs' = Just (i, c { slhs = slhs' , srhs = srhs' })
 | otherwise          = Nothing
  where
    slhs'             = simplifySortedReft tm (slhs c)
    srhs'             = simplifySortedReft tm (srhs c)

simplifySortedReft :: (Show s, Fixpoint s, Hashable s, Ord s, Eq s) => NonTrivSorts s -> SortedReft s -> SortedReft s
simplifySortedReft tm sr
  | nonTrivial = sr
  | otherwise  = sr { sr_reft = mempty }
  where
    nonTrivial = isNonTrivialSort tm (sr_sort sr)

isNonTrivialSort :: (Hashable s, Eq s) => NonTrivSorts s -> Sort s -> Bool
isNonTrivialSort tm t = S.member t tm
