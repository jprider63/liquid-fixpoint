{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs                      #-}

module Language.Fixpoint.Types.Environments (

  -- * Environments
    SEnv, SESearch(..)
  , emptySEnv, toListSEnv, fromListSEnv, fromMapSEnv
  , mapSEnvWithKey, mapSEnv, mapMSEnv
  , insertSEnv, deleteSEnv, memberSEnv, lookupSEnv, unionSEnv, unionSEnv'
  , intersectWithSEnv
  , differenceSEnv
  , filterSEnv
  , lookupSEnvWithDistance
  , envCs

  -- * Local Constraint Environments
  , IBindEnv, BindId, BindMap
  , emptyIBindEnv
  , insertsIBindEnv
  , deleteIBindEnv
  , elemsIBindEnv
  , fromListIBindEnv
  , memberIBindEnv
  , unionIBindEnv
  , diffIBindEnv
  , intersectionIBindEnv
  , nullIBindEnv
  , filterIBindEnv

  -- * Global Binder Environments
  , BindEnv, beBinds
  , emptyBindEnv
  , insertBindEnv, lookupBindEnv
  , filterBindEnv, mapBindEnv, mapWithKeyMBindEnv, adjustBindEnv
  , bindEnvFromList, bindEnvToList, elemsBindEnv
  , EBindEnv, splitByQuantifiers

  -- * Information needed to lookup and update Solutions
  -- , SolEnv (..)

  -- * Groups of KVars (needed by eliminate)
  , Packs (..)
  , getPack
  , makePack
  ) where

-- import qualified Data.Binary as B
import qualified Data.Binary as B
import qualified Data.List   as L
import           Data.Generics             (Data)
import           Data.Semigroup            (Semigroup (..))
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)
import           Data.Hashable
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S
import           Data.Maybe
import           Data.Function             (on)
import           Text.PrettyPrint.HughesPJ.Compat
import           Control.DeepSeq

import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Substitutions ()
import           Language.Fixpoint.Misc

type BindId        = Int
type BindMap a     = M.HashMap BindId a

newtype IBindEnv   = FB (S.HashSet BindId) deriving (Eq, Data, Typeable, Generic)

instance PPrint IBindEnv where
  pprintTidy _ = pprint . L.sort . elemsIBindEnv

newtype SEnv s a   = SE { seBinds :: M.HashMap (Symbol s) a }
                     deriving (Eq, Data, Typeable, Generic, Foldable, Traversable)

data SizedEnv a    = BE { _beSize  :: !Int
                        , beBinds :: !(BindMap a)
                        } deriving (Eq, Show, Functor, Foldable, Generic, Traversable)

instance PPrint a => PPrint (SizedEnv a) where
  pprintTidy k (BE _ m) = pprintTidy k m

-- Invariant: All BindIds in the map are less than beSize
type BindEnv s     = SizedEnv (Symbol s, SortedReft s)
newtype EBindEnv s = EB (BindEnv s)

splitByQuantifiers :: BindEnv s -> [BindId] -> (BindEnv s, EBindEnv s)
splitByQuantifiers (BE i bs) ebs = ( BE i $ M.filterWithKey (\k _ -> not (elem k ebs)) bs
                                   , EB $ BE i $ M.filterWithKey (\k _ -> elem k ebs) bs
                                   )

-- data SolEnv        = SolEnv { soeBinds :: !BindEnv } 
--                     deriving (Eq, Show, Generic)

instance (PPrint a, PPrint s, Ord s) => PPrint (SEnv s a) where
  pprintTidy k = pprintKVs k . L.sortBy (compare `on` fst) . toListSEnv

toListSEnv              ::  SEnv s a -> [(Symbol s, a)]
toListSEnv (SE env)     = M.toList env

fromListSEnv            ::  (Eq s, Hashable s) => [(Symbol s, a)] -> SEnv s a
fromListSEnv            = SE . M.fromList

fromMapSEnv             ::  M.HashMap (Symbol s) a -> SEnv s a
fromMapSEnv             = SE

mapSEnv                 :: (a -> b) -> SEnv s a -> SEnv s b
mapSEnv f (SE env)      = SE (fmap f env)

mapMSEnv                :: (Eq s, Hashable s, Monad m) => (a -> m b) -> SEnv s a -> m (SEnv s b)
mapMSEnv f env          = fromListSEnv <$> mapM (secondM f) (toListSEnv env)

mapSEnvWithKey          :: (Eq s, Hashable s) => ((Symbol s, a) -> (Symbol s, b)) -> SEnv s a -> SEnv s b
mapSEnvWithKey f        = fromListSEnv . fmap f . toListSEnv

deleteSEnv :: (Eq s, Hashable s) => Symbol s -> SEnv s a -> SEnv s a
deleteSEnv x (SE env)   = SE (M.delete x env)

insertSEnv :: (Eq s, Hashable s) => Symbol s -> a -> SEnv s a -> SEnv s a
insertSEnv x v (SE env) = SE (M.insert x v env)

lookupSEnv :: (Eq s, Hashable s) => Symbol s -> SEnv s a -> Maybe a
lookupSEnv x (SE env)   = M.lookup x env

emptySEnv :: SEnv s a
emptySEnv               = SE M.empty

memberSEnv :: (Eq s, Hashable s) => Symbol s -> SEnv s a -> Bool
memberSEnv x (SE env)   = M.member x env

intersectWithSEnv :: (Eq s, Hashable s) => (v1 -> v2 -> a) -> SEnv s v1 -> SEnv s v2 -> SEnv s a
intersectWithSEnv f (SE m1) (SE m2) = SE (M.intersectionWith f m1 m2)

differenceSEnv :: (Eq s, Hashable s) => SEnv s a -> SEnv s w -> SEnv s a
differenceSEnv (SE m1) (SE m2) = SE (M.difference m1 m2)

filterSEnv :: (Eq s, Hashable s) => (a -> Bool) -> SEnv s a -> SEnv s a
filterSEnv f (SE m)     = SE (M.filter f m)

unionSEnv :: (Eq s, Hashable s) => SEnv s a -> M.HashMap (Symbol s) a -> SEnv s a
unionSEnv (SE m1) m2    = SE (M.union m1 m2)

unionSEnv' :: (Eq s, Hashable s) => SEnv s a -> SEnv s a -> SEnv s a
unionSEnv' (SE m1) (SE m2)    = SE (M.union m1 m2)

lookupSEnvWithDistance :: (Eq s, Hashable s) => Symbol s -> SEnv s a -> SESearch s a
lookupSEnvWithDistance x (SE env)
  = case M.lookup x env of
     Just z  -> Found z
     Nothing -> Alts $ FS . symbol <$> alts
  where
    alts       = takeMin $ zip (editDistance x' <$> ss) ss
    ss         = symbolString . symbol <$> fst <$> M.toList env
    x'         = symbolString . symbol $ x
    takeMin xs = [z | (d, z) <- xs, d == getMin xs]
    getMin     = minimum . (fst <$>)


data SESearch s a = Found a | Alts [Symbol s]

-- | Functions for Indexed Bind Environment

instance Semigroup IBindEnv where
  (FB e1) <> (FB e2) = FB (e1 <> e2)

instance Monoid IBindEnv where
  mempty  = emptyIBindEnv
  mappend = (<>)

emptyIBindEnv :: IBindEnv
emptyIBindEnv = FB S.empty

deleteIBindEnv :: BindId -> IBindEnv -> IBindEnv
deleteIBindEnv i (FB s) = FB (S.delete i s)

memberIBindEnv :: BindId -> IBindEnv -> Bool
memberIBindEnv i (FB s) = S.member i s

insertsIBindEnv :: [BindId] -> IBindEnv -> IBindEnv
insertsIBindEnv is (FB s) = FB (foldr S.insert s is)

elemsIBindEnv :: IBindEnv -> [BindId]
elemsIBindEnv (FB s) = S.toList s

fromListIBindEnv :: [BindId] -> IBindEnv
fromListIBindEnv = FB . S.fromList

-- | Functions for Global Binder Environment
insertBindEnv :: Symbol s -> SortedReft s -> BindEnv s -> (BindId, BindEnv s)
insertBindEnv x r (BE n m) = (n, BE (n + 1) (M.insert n (x, r) m))

emptyBindEnv :: BindEnv s
emptyBindEnv = BE 0 M.empty

filterBindEnv   :: (BindId -> Symbol s -> SortedReft s -> Bool) -> BindEnv s -> BindEnv s
filterBindEnv f (BE n be) = BE n (M.filterWithKey (\ n (x, r) -> f n x r) be)

bindEnvFromList :: [(BindId, Symbol s, SortedReft s)] -> BindEnv s
bindEnvFromList [] = emptyBindEnv
bindEnvFromList bs = BE (1 + maxId) be
  where
    maxId          = maximum $ fst3 <$> bs
    be             = M.fromList [(n, (x, r)) | (n, x, r) <- bs]

elemsBindEnv :: BindEnv s -> [BindId]
elemsBindEnv be = fst3 <$> bindEnvToList be

bindEnvToList :: BindEnv s -> [(BindId, Symbol s, SortedReft s)]
bindEnvToList (BE _ be) = [(n, x, r) | (n, (x, r)) <- M.toList be]

mapBindEnv :: (BindId -> (Symbol s, SortedReft s) -> (Symbol s, SortedReft s)) -> BindEnv s -> BindEnv s
mapBindEnv f (BE n m) = BE n $ M.mapWithKey f m
-- (\i z -> tracepp (msg i z) $ f z) m
--  where
--    msg i z = "beMap " ++ show i ++ " " ++ show z

mapWithKeyMBindEnv :: (Monad m) => ((BindId, (Symbol s, SortedReft s)) -> m (BindId, (Symbol s, SortedReft s))) -> BindEnv s -> m (BindEnv s)
mapWithKeyMBindEnv f (BE n m) = (BE n . M.fromList) <$> mapM f (M.toList m)

lookupBindEnv :: BindId -> BindEnv s -> (Symbol s, SortedReft s)
lookupBindEnv k (BE _ m) = fromMaybe err (M.lookup k m)
  where
    err                  = errorstar $ "lookupBindEnv: cannot find binder" ++ show k

filterIBindEnv :: (BindId -> Bool) -> IBindEnv -> IBindEnv
filterIBindEnv f (FB m) = FB (S.filter f m)

unionIBindEnv :: IBindEnv -> IBindEnv -> IBindEnv
unionIBindEnv (FB m1) (FB m2) = FB $ m1 `S.union` m2

intersectionIBindEnv :: IBindEnv -> IBindEnv -> IBindEnv
intersectionIBindEnv (FB m1) (FB m2) = FB $ m1 `S.intersection` m2

nullIBindEnv :: IBindEnv -> Bool
nullIBindEnv (FB m) = S.null m

diffIBindEnv :: IBindEnv -> IBindEnv -> IBindEnv
diffIBindEnv (FB m1) (FB m2) = FB $ m1 `S.difference` m2

adjustBindEnv :: ((Symbol s, SortedReft s) -> (Symbol s, SortedReft s)) -> BindId -> BindEnv s -> BindEnv s
adjustBindEnv f i (BE n m) = BE n $ M.adjust f i m

instance Functor (SEnv s) where
  fmap = mapSEnv

instance (IsListConName s, Eq s, Fixpoint s) => Fixpoint (EBindEnv s) where
  toFix (EB (BE _ m)) = vcat $ map toFixBind $ hashMapToAscList m
    where
      toFixBind (i, (x, r)) = "ebind" <+> toFix i <+> toFix x <+> ": { " <+> toFix (sr_sort r) <+> " }"

instance (IsListConName s, Fixpoint s, Eq s, Ord s) => Fixpoint (BindEnv s) where
  toFix (BE _ m) = vcat $ map toFixBind $ hashMapToAscList m
    where
      toFixBind (i, (x, r)) = "bind" <+> toFix i <+> toFix x <+> ":" <+> toFix r

instance (Fixpoint a, Hashable s, Eq s, Fixpoint s, Ord s) => Fixpoint (SEnv s a) where
   toFix (SE m)   = toFix (hashMapToAscList m)

instance Fixpoint (SEnv s a) => Show (SEnv s a) where
  show = render . toFix

instance (Eq s, Hashable s) => Semigroup (SEnv s a) where
  s1 <> s2 = SE $ M.union (seBinds s1) (seBinds s2)

instance (Eq s, Hashable s) => Monoid (SEnv s a) where
  mempty        = SE M.empty

instance Semigroup (BindEnv s) where
  (BE 0 _) <> b        = b
  b        <> (BE 0 _) = b
  _        <> _        = errorstar "mappend on non-trivial BindEnvs"

instance Monoid (BindEnv s) where
  mempty  = BE 0 M.empty
  mappend = (<>)

envCs :: BindEnv s -> IBindEnv -> [(Symbol s, SortedReft s)]
envCs be env = [lookupBindEnv i be | i <- elemsIBindEnv env]

instance Fixpoint (IBindEnv) where
  toFix (FB ids) = text "env" <+> toFix ids

--------------------------------------------------------------------------------

instance (NFData s) => NFData (Packs s)
instance NFData IBindEnv
instance (NFData s) => NFData (BindEnv s)
instance (NFData a, NFData s) => NFData (SEnv s a)

instance (Eq s, Hashable s, B.Binary s) => B.Binary (Packs s)
instance B.Binary IBindEnv
instance (Eq s, Hashable s, B.Binary s) => B.Binary (BindEnv s)
instance (B.Binary a, B.Binary s, Hashable s, Eq s) => B.Binary (SEnv s a)
instance (Hashable a, Eq a, B.Binary a) => B.Binary (S.HashSet a) where
  put = B.put . S.toList
  get = S.fromList <$> B.get

--------------------------------------------------------------------------------
-- | Constraint Pack Sets ------------------------------------------------------
--------------------------------------------------------------------------------

newtype Packs s = Packs { packm :: M.HashMap (KVar s) Int }
               deriving (Eq, Show, Generic)

instance (Fixpoint s) => Fixpoint (Packs s) where
  toFix (Packs m) = vcat $ (("pack" <+>) . toFix) <$> kIs
    where
      kIs = L.sortBy (compare `on` snd) . M.toList $ m

instance (Fixpoint s) => PPrint (Packs s) where
  pprintTidy _ = toFix

instance (Eq s, Hashable s) => Semigroup (Packs s) where
  m1 <> m2 = Packs $ M.union (packm m1) (packm m2)

instance (Eq s, Hashable s) => Monoid (Packs s) where
  mempty  = Packs mempty
  mappend = (<>)

getPack :: (Eq s, Hashable s) => KVar s -> Packs s -> Maybe Int
getPack k (Packs m) = M.lookup k m

makePack :: (Ord s, Hashable s) => [S.HashSet (KVar s)] -> Packs s
makePack kvss = Packs (M.fromList kIs)
  where
    kIs       = [ (k, i) | (i, ks) <- kPacks, k <- ks ]
    kPacks    = zip [0..] . coalesce . fmap S.toList $ kvss
