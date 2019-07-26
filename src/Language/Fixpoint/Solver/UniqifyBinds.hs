{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE PatternGuards       #-}

-- This module makes it so no binds with different sorts have the same name.

module Language.Fixpoint.Solver.UniqifyBinds (renameAll) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Solver.Sanitize (dropDeadSubsts)
import           Language.Fixpoint.Misc          (fst3, mlookup)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L
import           Data.Foldable       (foldl')
import           Data.Maybe          (catMaybes, fromJust, isJust)
import           Data.Hashable       (Hashable)
import           GHC.Generics        (Generic)
import           Control.Arrow       (second)
import           Control.DeepSeq     (NFData, ($!!))
-- import Debug.Trace (trace)

--------------------------------------------------------------------------------
renameAll    :: (NFData s, Show s, Fixpoint s, Ord s, Hashable s) => SInfo s a -> SInfo s a
--------------------------------------------------------------------------------
renameAll fi2 = fi6
  where
    fi6       = {-# SCC "dropDead"    #-} dropDeadSubsts  fi5
    fi5       = {-# SCC "dropUnused"  #-} dropUnusedBinds fi4
    fi4       = {-# SCC "renameBinds" #-} renameBinds fi3 $!! rnm
    fi3       = {-# SCC "renameVars"  #-} renameVars fi2 rnm $!! idm
    rnm       = {-# SCC "mkRenameMap" #-} mkRenameMap $!! bs fi2
    idm       = {-# SCC "mkIdMap"     #-} mkIdMap fi2


--------------------------------------------------------------------------------
-- | `dropUnusedBinds` replaces the refinements of "unused" binders with "true".
--   see tests/pos/unused.fq for an example of why this phase is needed.
--------------------------------------------------------------------------------
dropUnusedBinds :: forall a s. (Show s, Fixpoint s, Ord s, Hashable s) => SInfo s a -> SInfo s a
dropUnusedBinds fi = fi {bs = filterBindEnv isUsed (bs fi)}-- { bs = mapBindEnv tx (bs fi) }
  where
    -- _tx i (x, r)
    -- | isUsed i    = (x, r)
    -- | otherwise   = (x, top r)
    isUsed i _x r  = {- tracepp (unwords ["isUsed", show i, showpp _x]) $ -} memberIBindEnv i usedBinds || isTauto @s @_ r
    usedBinds      = L.foldl' unionIBindEnv emptyIBindEnv (cEnvs ++ wEnvs)
    wEnvs          = wenv <$> M.elems (ws fi)
    cEnvs          = senv <$> M.elems (cm fi)

data Ref
  = RB !BindId    -- ^ Bind identifier
  | RI !Integer   -- ^ Constraint identifier?
    deriving (Eq, Generic)

instance NFData   Ref
instance Hashable Ref

-- | An `IdMap` stores for each constraint and BindId the
--   set of other BindIds that it references, i.e. those
--   where it needs to know when their names gets changed
type IdMap = M.HashMap Ref (S.HashSet BindId)

-- | A `RenameMap` maps an old name and sort to new name,
--   represented by a hashmap containing association lists.
--   `Nothing` as new name means the name is the same as the old.
type RenameMap s = M.HashMap (Symbol s) [(Sort s, Maybe FixSymbol)]

--------------------------------------------------------------------------------
mkIdMap :: (Hashable s, Ord s, Fixpoint s, Show s) => SInfo s a -> IdMap
--------------------------------------------------------------------------------
mkIdMap fi = M.foldlWithKey' (updateIdMap $ bs fi) M.empty $ cm fi

updateIdMap :: (Show s, Fixpoint s, Ord s, Eq s, Hashable s) => BindEnv s -> IdMap -> Integer -> SimpC s a -> IdMap
updateIdMap be m scId s = M.insertWith S.union (RI scId) refSet m'
  where
    ids                 = elemsIBindEnv (senv s)
    nameMap             = M.fromList [(fst $ lookupBindEnv i be, i) | i <- ids]
    m'                  = foldl' (insertIdIdLinks be nameMap) m ids
    symSet              = S.fromList $ syms $ crhs s
    refSet              = namesToIds symSet nameMap

insertIdIdLinks :: (Fixpoint s, Show s, Ord s, Eq s, Hashable s) => BindEnv s -> M.HashMap (Symbol s) BindId -> IdMap -> BindId -> IdMap
insertIdIdLinks be nameMap m i = M.insertWith S.union (RB i) refSet m
  where
    sr     = snd $ lookupBindEnv i be
    symSet = reftFreeVars $ sr_reft sr
    refSet = namesToIds symSet nameMap

namesToIds :: (Hashable s, Eq s) => S.HashSet (Symbol s) -> M.HashMap (Symbol s) BindId -> S.HashSet BindId
namesToIds xs m = S.fromList $ catMaybes [M.lookup x m | x <- S.toList xs] --TODO why any Nothings?

--------------------------------------------------------------------------------
mkRenameMap :: (Eq s, Hashable s) => BindEnv s -> RenameMap s
--------------------------------------------------------------------------------
mkRenameMap be = foldl' (addId be) M.empty ids
  where
    ids = fst3 <$> bindEnvToList be

addId :: (Hashable s, Eq s) => BindEnv s -> RenameMap s -> BindId -> RenameMap s
addId be m i
  | M.member sym m = addDupId m sym t i
  | otherwise      = M.insert sym [(t, Nothing)] m
  where
    (sym, t)       = second sr_sort $ lookupBindEnv i be

addDupId :: (Hashable s, Eq s) => RenameMap s -> Symbol s -> Sort s -> BindId -> RenameMap s
addDupId m sym t i
  | isJust $ L.lookup t mapping = m
  | otherwise                   = M.insert sym ((t, Just $ renameSymbol (symbol sym) i) : mapping) m
  where
    mapping = fromJust $ M.lookup sym m

--------------------------------------------------------------------------------
-- | `renameVars` seems to do the actual work of renaming all the binders
--   to use their sort-specific names.
--------------------------------------------------------------------------------
renameVars :: (Hashable s, Show s, Fixpoint s, Ord s) => SInfo s a -> RenameMap s -> IdMap -> SInfo s a
--------------------------------------------------------------------------------
renameVars fi rnMap idMap = M.foldlWithKey' (updateRef rnMap) fi idMap

updateRef :: (Ord s, Fixpoint s, Show s, Hashable s, Eq s) => RenameMap s -> SInfo s a -> Ref -> S.HashSet BindId -> SInfo s a
updateRef rnMap fi rf bset = applySub (mkSubst subs) fi rf
  where
    symTList = [second sr_sort $ lookupBindEnv i $ bs fi | i <- S.toList bset]
    subs     = catMaybes $ mkSubUsing rnMap <$> symTList

mkSubUsing :: (Eq s, Hashable s, Show s) => RenameMap s -> (Symbol s, Sort s) -> Maybe (Symbol s, Expr s)
mkSubUsing m (sym, t) = do
  newName <- fromJust $ L.lookup t $ mlookup m sym
  return (sym, eVar newName)

applySub :: (Show s, Fixpoint s, Hashable s, Ord s) => Subst s -> SInfo s a -> Ref -> SInfo s a
applySub sub fi (RB i) = fi { bs = adjustBindEnv go i (bs fi) }
  where
    go (sym, sr)       = (sym, subst sub sr)

applySub sub fi (RI i) = fi { cm = M.adjust go i (cm fi) }
  where
    go c               = c { _crhs = subst sub (_crhs c) }

--------------------------------------------------------------------------------
renameBinds :: (Show s, Hashable s, Eq s) => SInfo s a -> RenameMap s -> SInfo s a
--------------------------------------------------------------------------------
renameBinds fi m = fi { bs = bindEnvFromList $ renameBind m <$> beList }
  where
    beList       = bindEnvToList $ bs fi

renameBind :: (Eq s, Hashable s, Show s) => RenameMap s -> (BindId, Symbol s, SortedReft s) -> (BindId, Symbol s, SortedReft s)
renameBind m (i, sym, sr)
  | Just newSym <- mnewSym = (i, FS newSym, sr)
  | otherwise              = (i, sym,    sr)
  where
    t                      = sr_sort sr
    mnewSym                = fromJust $ L.lookup t $ mlookup m sym
