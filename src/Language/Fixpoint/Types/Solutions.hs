{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE TupleSections              #-}

-- | This module contains the top-level SOLUTION data types,
--   including various indices used for solving.

module Language.Fixpoint.Types.Solutions (

  -- * Solution tables
    Solution, GSolution
  , Sol (gMap, sEnv, sEbd, sxEnv)
  , updateGMap, updateGMapWithKey
  , sScp
  , CMap

  -- * Solution elements
  , Hyp, Cube (..), QBind, GBind
  , EQual (..)
  , EbindSol (..)

  -- * Equal elements
  , eQual
  , trueEqual

  -- * Gradual Solution elements
  , qbToGb, gbToQbs, gbEquals, equalsGb, emptyGMap, qbExprs

  -- * Solution Candidates (move to SolverMonad?)
  , Cand

  -- * Constructor
  , fromList

  -- * Update
  , update
  , updateEbind

  -- * Lookup
  , lookupQBind
  , lookup, glookup

  -- * Manipulating QBind
  , qb
  , qbPreds
  , qbFilter

  , gbFilterM

  -- * Conversion for client
  , result, resultGradual

  -- * "Fast" Solver (DEPRECATED as unsound)
  , Index  (..)
  , KIndex (..)
  , BindPred (..)
  , BIndex (..)
  ) where

import           Prelude hiding (lookup)
import           GHC.Generics
import           Control.DeepSeq
import           Data.Hashable
import qualified Data.Maybe                 as Mb 
import qualified Data.HashMap.Strict        as M
import qualified Data.List                  as L
import           Data.Generics             (Data)
import           Data.Semigroup            (Semigroup (..))
import           Data.Typeable             (Typeable)
import           Control.Monad (filterM)
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Spans 
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Theories
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Environments
import           Language.Fixpoint.Types.Constraints
import           Language.Fixpoint.Types.Substitutions
import           Language.Fixpoint.SortCheck (elaborate)
import           Text.PrettyPrint.HughesPJ.Compat

--------------------------------------------------------------------------------
-- | Update Solution -----------------------------------------------------------
--------------------------------------------------------------------------------
update :: (Eq s, Hashable s, Show s) => Sol s a (QBind s) -> [KVar s] -> [(KVar s, EQual s)] -> (Bool, Sol s a (QBind s))
--------------------------------------------------------------------------------
update s ks kqs = {- tracepp msg -} (or bs, s')
  where
    kqss        = groupKs ks kqs
    (bs, s')    = folds update1 s kqss
    -- msg      = printf "ks = %s, s = %s" (showpp ks) (showpp s)

folds   :: (a -> b -> (c, a)) -> a -> [b] -> ([c], a)
folds f b = L.foldl' step ([], b)
  where
     step (cs, acc) x = (c:cs, x')
       where
         (c, x')      = f acc x

groupKs :: (Hashable s, Eq s) => [KVar s] -> [(KVar s, EQual s)] -> [(KVar s, QBind s)]
groupKs ks kqs = [ (k, QB eqs) | (k, eqs) <- M.toList $ groupBase m0 kqs ]
  where
    m0         = M.fromList $ (,[]) <$> ks

update1 :: (Show s, Hashable s, Eq s) => Sol s a (QBind s) -> (KVar s, QBind s) -> (Bool, Sol s a (QBind s))
update1 s (k, qs) = (change, updateK k qs s)
  where
    oldQs         = lookupQBind s k
    change        = qbSize oldQs /= qbSize qs


--------------------------------------------------------------------------------
-- | The `Solution` data type --------------------------------------------------
--------------------------------------------------------------------------------
type Solution s = Sol s () (QBind s)
type GSolution s = Sol s (((Symbol s, Sort s), Expr s), GBind s) (QBind s)
newtype QBind s = QB [EQual s]   deriving (Show, Data, Typeable, Generic, Eq)
newtype GBind s = GB [[EQual s]] deriving (Show, Data, Typeable, Generic)

emptyGMap :: GSolution s -> GSolution s
emptyGMap sol = mapGMap sol (\(x,_) -> (x, GB []))

updateGMapWithKey :: (Hashable s, Eq s) => [(KVar s, QBind s)] -> GSolution s -> GSolution s
updateGMapWithKey kqs sol = sol {gMap =  foldl (\m (k, (QB eq)) -> M.adjust (\(x, GB eqs) -> (x, GB (if eq `elem` eqs then eqs else eq:eqs))) k m) (gMap sol) kqs }

qb :: [EQual s] -> QBind s
qb = QB

qbEQuals :: QBind s -> [EQual s]
qbEQuals (QB xs) = xs

qbExprs :: QBind s -> [Expr s]
qbExprs (QB xs) = eqPred <$> xs

qbToGb :: QBind s -> GBind s
qbToGb (QB xs) = GB $ map (:[]) xs

gbToQbs :: (Fixpoint s, Ord s) => GBind s -> [QBind s]
gbToQbs (GB [])  = [QB [trueEqual]]
gbToQbs (GB ess) = QB <$> ess

gbEquals :: GBind s -> [[EQual s]]
gbEquals (GB eqs) = eqs

equalsGb :: [[EQual s]] -> GBind s
equalsGb = GB

gbFilterM :: Monad m => ([EQual s] -> m Bool) -> GBind s -> m (GBind s)
gbFilterM f (GB eqs) = GB <$> filterM f eqs

qbSize :: QBind s -> Int
qbSize = length . qbEQuals

qbFilter :: (EQual s -> Bool) -> QBind s -> QBind s
qbFilter f (QB eqs) = QB (filter f eqs)

instance (NFData s) => NFData (QBind s)
instance (NFData s) => NFData (GBind s)

instance (Fixpoint s, PPrint s, Ord s) => PPrint (QBind s) where
  pprintTidy k = pprintTidy k . qbEQuals

--------------------------------------------------------------------------------
-- | An `EbindSol` contains the relevant information for an existential-binder;
--   (See tests/pos/ebind-*.fq for examples.) This is either 
--   1. the constraint whose HEAD is a singleton that defines the binder, OR 
--   2. the solved out TERM that we should use in place of the ebind at USES.
--------------------------------------------------------------------------------
data EbindSol s
  = EbDef [SimpC s ()] (Symbol s) -- ^ The constraint whose HEAD "defines" the Ebind
                             -- and the @FixSymbol@ for that EBind
  | EbSol (Expr s)             -- ^ The solved out term that should be used at USES.
  | EbIncr                 -- ^ EBinds not to be solved for (because they're currently being solved for)
   deriving (Show, Generic, NFData)

instance (PPrint s, Fixpoint s, Ord s, Eq s) => PPrint (EbindSol s) where 
  pprintTidy k (EbDef i x) = "EbDef:" <+> pprintTidy k i <+> pprintTidy k x
  pprintTidy k (EbSol e)   = "EbSol:" <+> pprintTidy k e
  pprintTidy _ (EbIncr)    = "EbIncr"

--------------------------------------------------------------------------------
updateEbind :: (Ord s, Fixpoint s, Show s) => Sol s a b -> BindId -> Pred s -> Sol s a b 
--------------------------------------------------------------------------------
updateEbind s i !e = case M.lookup i (sEbd s) of 
  Nothing         -> errorstar $ "updateEBind: Unknown ebind " ++ show i
  Just (EbSol e0) -> errorstar $ "updateEBind: Re-assigning ebind " ++ show i ++ " with solution: " ++ show e0 
  Just _          -> s { sEbd = M.insert i (EbSol e) (sEbd s) }
    
--------------------------------------------------------------------------------
-- | A `Sol` contains the various indices needed to compute a solution,
--   in particular, to compute `lhsPred` for any given constraint.
--------------------------------------------------------------------------------
data Sol s b a = Sol
  { sEnv :: !(SymEnv s)                      -- ^ Environment used to elaborate solutions
  , sMap :: !(M.HashMap (KVar s) a)          -- ^ Actual solution (for cut kvar)
  , gMap :: !(M.HashMap (KVar s) b)          -- ^ Solution for gradual variables
  , sHyp :: !(M.HashMap (KVar s) (Hyp s))        -- ^ Defining cubes  (for non-cut kvar)
  , sScp :: !(M.HashMap (KVar s) IBindEnv)   -- ^ Set of allowed binders for kvar
  , sEbd :: !(M.HashMap BindId (EbindSol s)) -- ^ EbindSol for each existential binder
  , sxEnv :: !(SEnv s (BindId, Sort s))      --   TODO: merge with sEnv? used for sorts of ebinds to solve ebinds in lhsPred
  } deriving (Generic)

deriving instance (NFData s, NFData b, NFData a) => NFData (Sol s b a)

updateGMap :: Sol s b a -> M.HashMap (KVar s) b -> Sol s b a
updateGMap sol gmap = sol {gMap = gmap}

mapGMap :: Sol s b a -> (b -> b) -> Sol s b a
mapGMap sol f = sol {gMap = M.map f (gMap sol)}

instance (Hashable s, Eq s) => Semigroup (Sol s a b) where
  s1 <> s2 = Sol { sEnv  = (sEnv s1)  <> (sEnv s2)
                 , sMap  = (sMap s1)  <> (sMap s2)
                 , gMap  = (gMap s1)  <> (gMap s2)
                 , sHyp  = (sHyp s1)  <> (sHyp s2)
                 , sScp  = (sScp s1)  <> (sScp s2)
                 , sEbd  = (sEbd s1)  <> (sEbd s2) 
                 , sxEnv = (sxEnv s1) <> (sxEnv s2) 
                 }

instance (Hashable s, Eq s) => Monoid (Sol s a b) where
  mempty = Sol { sEnv = mempty 
               , sMap = mempty 
               , gMap = mempty 
               , sHyp = mempty 
               , sScp = mempty 
               , sEbd = mempty
               , sxEnv = mempty
               }
  mappend = (<>)

instance Functor (Sol s a) where
  fmap f (Sol e s m1 m2 m3 m4 m5) = Sol e (f <$> s) m1 m2 m3 m4 m5

instance (Ord s, Fixpoint s, PPrint s, PPrint a, PPrint b) => PPrint (Sol s a b) where
  pprintTidy k s = vcat [ "sMap :=" <+> pprintTidy k (sMap s)
                        , "sEbd :=" <+> pprintTidy k (sEbd s) 
                        ]

--------------------------------------------------------------------------------
-- | A `Cube` is a single constraint defining a KVar ---------------------------
--------------------------------------------------------------------------------
type Hyp s    = ListNE (Cube s)

data Cube s = Cube
  { cuBinds :: IBindEnv  -- ^ Binders       from defining Env
  , cuSubst :: Subst s     -- ^ Substitutions from cstrs    Rhs
  , cuId    :: SubcId    -- ^ Id            of   defining Cstr
  , cuTag   :: Tag       -- ^ Tag           of   defining Cstr (DEBUG)
  } deriving (Generic, NFData)

instance PPrint (Cube s) where
  pprintTidy _ c = "Cube" <+> pprint (cuId c)

instance Show (Cube s) where
  show = showpp
--------------------------------------------------------------------------------
result :: (Fixpoint s, Ord s) => Sol s a (QBind s) -> M.HashMap (KVar s) (Expr s)
--------------------------------------------------------------------------------
result s = sMap $ (pAnd . fmap eqPred . qbEQuals) <$> s


--------------------------------------------------------------------------------
resultGradual :: GSolution s -> M.HashMap (KVar s) (Expr s, [Expr s])
--------------------------------------------------------------------------------
resultGradual s = fmap go' (gMap s)
  where
    go' ((_,e), GB eqss)
     = (e, [PAnd $ fmap eqPred eqs | eqs <- eqss])


--------------------------------------------------------------------------------
-- | Create a Solution ---------------------------------------------------------
--------------------------------------------------------------------------------
fromList :: (Hashable s, Eq s) => SymEnv s 
         -> [(KVar s, a)] 
         -> [(KVar s, b)] 
         -> [(KVar s, Hyp s)] 
         -> M.HashMap (KVar s) IBindEnv 
         -> [(BindId, EbindSol s)]
         -> SEnv s (BindId, Sort s)
         -> Sol s a b
fromList env kGs kXs kYs z ebs xbs
        = Sol env kXm kGm kYm z ebm xbs
  where
    kXm = M.fromList kXs
    kYm = M.fromList kYs
    kGm = M.fromList kGs
    ebm = M.fromList ebs

--------------------------------------------------------------------------------
qbPreds :: (Fixpoint s, Ord s, PPrint s, Hashable s, Show s, Eq s) => String -> Sol s a (QBind s) -> Subst s -> QBind s -> [(Pred s, EQual s)]
--------------------------------------------------------------------------------
qbPreds msg s su (QB eqs) = [ (elabPred eq, eq) | eq <- eqs ]
  where
    elabPred eq           = elaborate (atLoc eq $ "qbPreds:" ++ msg) env 
                          . subst su 
                          . eqPred 
                          $ eq
    env                   = sEnv s

--------------------------------------------------------------------------------
-- | Read / Write Solution at KVar ---------------------------------------------
--------------------------------------------------------------------------------
lookupQBind :: (Eq s, Hashable s, Show s) => Sol s a (QBind s) -> KVar s -> QBind s
--------------------------------------------------------------------------------
lookupQBind s k = {- tracepp _msg $ -} Mb.fromMaybe (QB []) (lookupElab s k)
  where
    _msg        = "lookupQB: k = " ++ show k

--------------------------------------------------------------------------------
glookup :: (Hashable s, Eq s, Show s) => GSolution s -> KVar s -> Either (Hyp s) (Either (QBind s) (((Symbol s, Sort s), Expr s), GBind s))
--------------------------------------------------------------------------------
glookup s k
  | Just gbs <- M.lookup k (gMap s)
  = Right (Right gbs)
  | Just cs  <- M.lookup k (sHyp s) -- non-cut variable, return its cubes
  = Left cs
  | Just eqs <- lookupElab s k
  = Right (Left eqs)                 -- TODO: don't initialize kvars that have a hyp solution
  | otherwise
  = errorstar $ "solLookup: Unknown kvar " ++ show k



--------------------------------------------------------------------------------
lookup :: (Hashable s, Eq s, Show s) => Sol s a (QBind s) -> KVar s -> Either (Hyp s) (QBind s)
--------------------------------------------------------------------------------
lookup s k
  | Just cs  <- M.lookup k (sHyp s) -- non-cut variable, return its cubes
  = Left cs
  | Just eqs <- lookupElab s k
  = Right eqs                 -- TODO: don't initialize kvars that have a hyp solution
  | otherwise
  = errorstar $ "solLookup: Unknown kvar " ++ show k

lookupElab :: (Hashable s, Eq s) => Sol s b (QBind s) -> KVar s -> Maybe (QBind s)
lookupElab s k = M.lookup k (sMap s)

--------------------------------------------------------------------------------
updateK :: (Hashable s, Eq s) => KVar s -> a -> Sol s b a -> Sol s b a
--------------------------------------------------------------------------------
updateK k qs s = s { sMap = M.insert k qs (sMap s)
--                 , sBot = M.delete k    (sBot s)
                   }


--------------------------------------------------------------------------------
-- | A `Cand` is an association list indexed by predicates
--------------------------------------------------------------------------------
type Cand s a   = [(Expr s, a)]


--------------------------------------------------------------------------------
-- | Instantiated Qualifiers ---------------------------------------------------
--------------------------------------------------------------------------------
data EQual s = EQL
  { eqQual :: !(Qualifier s)
  , eqPred  :: !(Expr s)
  , _eqArgs :: ![Expr s]
  } deriving (Eq, Show, Data, Typeable, Generic)

instance Loc (EQual s) where 
  srcSpan = srcSpan . eqQual 

trueEqual :: (Ord s, Fixpoint s) => EQual s
trueEqual = EQL trueQual mempty []

instance (Ord s, PPrint s, Fixpoint s) => PPrint (EQual s) where
  pprintTidy k = pprintTidy k . eqPred

instance (NFData s) => NFData (EQual s)

{- EQL :: q:_ -> p:_ -> ListX F.Expr {q_params q} -> _ @-}
eQual :: (Show s, Fixpoint s, Ord s, Hashable s, Eq s) => Qualifier s -> [Symbol s] -> EQual s
eQual q xs = {- tracepp "eQual" $ -} EQL q p es
  where
    p      = subst su $  qBody q
    su     = mkSubst  $  safeZip "eQual" qxs es
    es     = eVar    <$> xs
    qxs    = qpSym   <$> qParams q

--------------------------------------------------------------------------------
-- | A KIndex uniquely identifies each *use* of a KVar in an (LHS) binder
--------------------------------------------------------------------------------
data KIndex s = KIndex { kiBIndex :: !BindId
                     , kiPos    :: !Int
                     , kiKVar   :: !(KVar s)
                     }
              deriving (Eq, Ord, Show, Generic)

instance (Hashable s) => Hashable (KIndex s)

instance (Show s) => PPrint (KIndex s) where
  pprintTidy _ = tshow

--------------------------------------------------------------------------------
-- | A BIndex is created for each LHS Bind or RHS constraint
--------------------------------------------------------------------------------
data BIndex    = Root
               | Bind !BindId
               | Cstr !SubcId
                 deriving (Eq, Ord, Show, Generic)

instance Hashable BIndex

instance PPrint BIndex where
  pprintTidy _ = tshow

--------------------------------------------------------------------------------
-- | Each `Bind` corresponds to a conjunction of a `bpConc` and `bpKVars`
--------------------------------------------------------------------------------
data BindPred s = BP
  { bpConc :: !(Pred s)                  -- ^ Concrete predicate (PTrue o)
  , bpKVar :: ![KIndex s]              -- ^ KVar-Subst pairs
  } deriving (Show)

instance (Ord s, Fixpoint s, Show s) => PPrint (BindPred s) where
  pprintTidy _ = tshow


--------------------------------------------------------------------------------
-- | A Index is a suitably indexed version of the cosntraints that lets us
--   1. CREATE a monolithic "background formula" representing all constraints,
--   2. ASSERT each lhs via bits for the subc-id and formulas for dependent cut KVars
--------------------------------------------------------------------------------
data Index s = FastIdx
  { bindExpr   :: !(BindId |-> BindPred s) -- ^ BindPred for each BindId
  , kvUse      :: !(KIndex s |-> KVSub s)    -- ^ Definition of each `KIndex`
  , kvDef      :: !(KVar s   |-> Hyp s)      -- ^ Constraints defining each `KVar`
  , envBinds   :: !(CMap IBindEnv)       -- ^ Binders of each Subc
  , envTx      :: !(CMap [SubcId])       -- ^ Transitive closure oof all dependent binders
  , envSorts   :: !(SEnv s (Sort s))           -- ^ Sorts for all symbols
  -- , bindPrev   :: !(BIndex |-> BIndex)   -- ^ "parent" (immediately dominating) binder
  -- , kvDeps     :: !(CMap [KIndex])       -- ^ List of (Cut) KVars on which a SubC depends
  }

type CMap a  = M.HashMap SubcId a
