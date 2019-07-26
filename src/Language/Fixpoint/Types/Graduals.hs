{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE TupleSections              #-}

-- | This module contains the top-level SOLUTION data types,
--   including various indices used for solving.

module Language.Fixpoint.Types.Graduals (
  uniquify,

  makeSolutions,

  GSol,

  Gradual (..)
  ) where

import Language.Fixpoint.Types.Refinements
import Language.Fixpoint.Types.Constraints
import Language.Fixpoint.Types.Config
import Language.Fixpoint.Types.PrettyPrint
import Language.Fixpoint.Types.Environments
import Language.Fixpoint.Types.Substitutions
import Language.Fixpoint.Types.Visitor
import Language.Fixpoint.Types.Spans
import Language.Fixpoint.Types.Theories
import Language.Fixpoint.Types.Names        (gradIntSymbol, tidySymbol, Symbol (..), symbol)
import Language.Fixpoint.Misc               (allCombinations, errorstar)

import Control.DeepSeq

import qualified Data.HashMap.Strict       as M
import           Data.Hashable
import qualified Data.List                 as L

import Control.Monad.State.Lazy
import Data.Maybe (fromMaybe)
import Data.Semigroup (Semigroup (..))
import qualified Language.Fixpoint.SortCheck       as So
import Language.Fixpoint.Solver.Sanitize (symbolEnv)


data GSol s = GSol !(SymEnv s) !(M.HashMap (KVar s) (Expr s, GradInfo))

instance (Hashable s, Eq s) => Semigroup (GSol s) where
  (GSol e1 m1) <> (GSol e2 m2) = GSol (e1 <> e2) (m1 <> m2)

instance (Hashable s, Eq s) => Monoid (GSol s) where
  mempty = GSol mempty mempty

instance (PPrint s, Show s, Fixpoint s, Ord s, Hashable s) => Show (GSol s) where
  show (GSol _ m) = "GSOL = \n" ++ unlines ((\(k,(e, i)) -> showpp k ++ showInfo i ++  " |-> " ++ showpp (tx e)) <$> M.toList m)
    where
      tx e = subst (mkSubst @s $ [(x, EVar . FS $ tidySymbol (symbol x)) | x <- syms e]) e
      showInfo i = show i


makeSolutions :: (Hashable s, PPrint s, Fixpoint s, Ord s, Show s, NFData a, Fixpoint a, Show a)
              => Config -> SInfo s a
              -> [(KVar s, (GWInfo s, [[Expr s]]))]
              -> Maybe [GSol s]

makeSolutions _ _ []
  = Nothing
makeSolutions cfg fi kes
  = Just $ map (GSol env . M.fromList) (allCombinations (go  <$> kes))
  where
    go (k, (i, es)) = [(k, (pAnd (gexpr i:e'), ginfo i)) | e' <- es]
    env = symbolEnv cfg fi


-------------------------------------------------------------------------------
-- |  Make each gradual appearence unique -------------------------------------
-------------------------------------------------------------------------------
uniquify :: (Eq s, Hashable s, NFData a, Fixpoint a, Loc a) => SInfo s a -> (SInfo s a)

uniquify fi = fi{cm = cm', ws = ws', bs = bs'}
  where
  (cm', km, bs') = uniquifyCS (bs fi) (cm fi)
  ws'            = expandWF km (ws fi)

uniquifyCS :: (Hashable s, Eq s, NFData a, Fixpoint a, Loc a)
           => BindEnv s
           -> M.HashMap SubcId (SimpC s a)
           -> (M.HashMap SubcId (SimpC s a), M.HashMap (KVar s) [(KVar s, Maybe SrcSpan)], BindEnv s)
uniquifyCS bs cs
  = (x, km, benv st)
--   = (x, km, mapBindEnv (\i (x,r) -> if i `elem` ubs st then (x, ungrad r) else (x, r)) $ benv st)
  where
    (x, st) = runState (uniq cs) (initUniqueST bs)
    km      = kmap st
    -- gs      = [x | xs <- M.elems km, (x,_) <- xs]


class Unique s a where
   uniq :: a -> UniqueM s a

instance Unique s a => Unique s (M.HashMap SubcId a) where
  uniq m = M.fromList <$> mapM (\(i,x) -> (i,) <$> uniq x) (M.toList m)

instance (Eq s, Hashable s, Loc a) => Unique s (SimpC s a) where
  uniq cs = do
    updateLoc $ srcSpan $ _cinfo cs
    rhs <- uniq (_crhs cs)
    env <- uniq (_cenv cs)
    return cs{_crhs = rhs, _cenv = env}

instance (Hashable s, Eq s) => Unique s IBindEnv where
  uniq env = withCache (fromListIBindEnv <$> mapM uniq (elemsIBindEnv env))

instance (Hashable s, Eq s) => Unique s BindId where
  uniq i = do
    bs <- benv <$> get
    let (x, t) = lookupBindEnv i bs
    resetChange
    t' <- uniq t
    hasChanged <- change <$> get
    if hasChanged
      then do let (i', bs') = insertBindEnv x t' bs
              updateBEnv i bs'
              return i'
      else return i

instance (Hashable s, Eq s) => Unique s (SortedReft s) where
  uniq (RR s r) = RR s <$> uniq r

instance (Eq s, Hashable s) => Unique s (Reft s) where
  uniq (Reft (x,e)) = (Reft . (x,)) <$> uniq e

instance (Hashable s, Eq s) => Unique s (Expr s) where
  uniq = mapMExpr go
   where
    go (PGrad k su i e) = do
      k'  <- freshK k
      src <- uloc <$> get
      return $ PGrad k' su (i{gused = src}) e
    go e              = return e

-------------------------------------------------------------------------------
-- | The Unique Monad ---------------------------------------------------------
-------------------------------------------------------------------------------

type UniqueM s = State (UniqueST s)
data UniqueST s
  = UniqueST { freshId :: Integer
             , kmap    :: M.HashMap (KVar s) [(KVar s, Maybe SrcSpan)]
             , change  :: Bool
             , cache   :: M.HashMap (KVar s) (KVar s)
             , uloc    :: Maybe SrcSpan
             , ubs     :: [BindId]
             , benv    :: BindEnv s
             }

updateLoc :: SrcSpan -> UniqueM s ()
updateLoc x = modify $ \s -> s{uloc = Just x}

withCache :: (Eq s, Hashable s) => UniqueM s a -> UniqueM s a
withCache act = do
  emptyCache
  a <- act
  emptyCache
  return a

emptyCache :: (Hashable s, Eq s) => UniqueM s ()
emptyCache = modify $ \s -> s{cache = mempty}

addCache :: (Hashable s, Eq s) => KVar s -> KVar s -> UniqueM s ()
addCache k k' = modify $ \s -> s{cache = M.insert k k' (cache s)}

updateBEnv :: BindId -> BindEnv s -> UniqueM s ()
updateBEnv i bs = modify $ \s -> s{benv = bs, ubs = i:(ubs s)}

setChange :: UniqueM s ()
setChange = modify $ \s -> s{change = True}

resetChange :: UniqueM s ()
resetChange = modify $ \s -> s{change = False}

initUniqueST :: (Hashable s, Eq s) => BindEnv s ->  UniqueST s
initUniqueST = UniqueST 0 mempty False mempty Nothing mempty

freshK, freshK' :: (Eq s, Hashable s) => KVar s -> UniqueM s (KVar s)
freshK k  = do
  setChange
  cached <- cache <$> get
  case M.lookup k cached of
    {- OPTIMIZATION: Only create one fresh occurence of ? per constraint environment. -}
    Just k' -> return  k'
    Nothing -> freshK' k

freshK' k = do
  i <- freshId <$> get
  modify $ (\s -> s{freshId = i + 1})
  let k' = KV . FS $ gradIntSymbol i
  addK k k'
  addCache k k'
  return k'

addK :: (Hashable s, Eq s) => KVar s -> KVar s -> UniqueM s ()
addK key val =
  modify $ (\s -> s{kmap = M.insertWith (++) key [(val, uloc s)] (kmap s)})

-------------------------------------------------------------------------------
-- | expandWF -----------------------------------------------------------------
-------------------------------------------------------------------------------

expandWF :: (Hashable s, Eq s, NFData a, Fixpoint a)
         => M.HashMap (KVar s) [(KVar s, Maybe SrcSpan)]
         -> M.HashMap (KVar s) (WfC s a)
         -> M.HashMap (KVar s) (WfC s a)
expandWF km ws
  = M.fromList $
       ([(k, updateKVar k src w) | (i, w) <- gws, (kw, ks) <- km', kw == i, (k, src) <- ks]
        ++ kws)
  where
    (gws, kws)       = L.partition (isGWfc . snd) $ M.toList ws
    km'              = M.toList km
    updateKVar k src wfc = wfc { wrft = (\(v,s,_) -> (v,s,k)) $ wrft wfc
                               , wloc = (wloc wfc){gused = src}
                               }

-------------------------------------------------------------------------------
-- |  Substitute Gradual Solution ---------------------------------------------
-------------------------------------------------------------------------------

class Gradual s a | a -> s where
  gsubst :: GSol s -> a -> a

instance (Fixpoint s, Ord s, PPrint s, Hashable s, Show s, Eq s) => Gradual s (Expr s) where
  gsubst (GSol env m) e   = mapGVars' (\(k, _) -> Just (fromMaybe (err k) (mknew k))) e
    where
      mknew k = So.elaborate "initBGind.mkPred" env $ fst <$> M.lookup k m
      err   k = errorstar ("gradual substitution: Cannot find " ++ showpp k)

instance (Hashable s, PPrint s, Ord s, Fixpoint s, Show s, Eq s) => Gradual s (Reft s) where
  gsubst su (Reft (x, e)) = Reft (x, gsubst su e)

instance (Show s, Fixpoint s, Ord s, PPrint s, Hashable s, Eq s) => Gradual s (SortedReft s) where
  gsubst su r = r {sr_reft = gsubst su (sr_reft r)}

instance (Hashable s, PPrint s, Ord s, Fixpoint s, Show s, Eq s) => Gradual s (SimpC s a) where
  gsubst su c = c {_crhs = gsubst su (_crhs c)}

instance (Hashable s, PPrint s, Ord s, Fixpoint s, Show s, Eq s) => Gradual s (BindEnv s) where
  gsubst su = mapBindEnv (\_ (x, r) -> (x, gsubst su r))

instance Gradual s v => Gradual s (M.HashMap k v) where
  gsubst su = M.map (gsubst su)

instance (Fixpoint s, Ord s, PPrint s, Hashable s, Show s, Eq s) => Gradual s (SInfo s a) where
  gsubst su fi = fi { bs = gsubst su (bs fi)
                    , cm = gsubst su (cm fi)
                    }
