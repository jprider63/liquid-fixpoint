{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.Fixpoint.Types.Visitor (
  -- * Visitor
     Visitor (..)
  ,  Visitable (..)

  -- * Extracting FixSymbolic Constants (String Literals)
  ,  SymConsts (..)

  -- * Default Visitor
  , defaultVisitor

  -- * Transformers
  , trans

  -- * Accumulators
  , fold

  -- * Clients
  , stripCasts
  , kvars, eapps
  , size, lamSize
  , envKVars
  , envKVarsN
  , rhsKVars
  , mapKVars, mapKVars', mapGVars', mapKVarSubsts
  , mapExpr, mapMExpr

  -- * Coercion Substitutions
  , CoSub
  , applyCoSub

  -- * Predicates on Constraints
  , isConcC , isKvarC

  -- * Sorts
  , foldSort
  , mapSort
  , foldDataDecl


  ) where

-- import           Control.Monad.Trans.State.Strict (State, modify, runState)
-- import           Control.DeepSeq
import           Data.Semigroup      (Semigroup (..))
import           Control.Monad.State.Strict
import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M
import           Data.Hashable
import qualified Data.List           as L
import           Language.Fixpoint.Types hiding (mapSort)
import qualified Language.Fixpoint.Misc as Misc




data Visitor s acc ctx = Visitor {
 -- | Context @ctx@ is built in a "top-down" fashion; not "across" siblings
    ctxExpr :: ctx -> Expr s -> ctx

  -- | Transforms can access current @ctx@
  , txExpr  :: ctx -> Expr s -> Expr s

  -- | Accumulations can access current @ctx@; @acc@ value is monoidal
  , accExpr :: ctx -> Expr s -> acc
  }

---------------------------------------------------------------------------------
defaultVisitor :: (Monoid acc) => Visitor s acc ctx
---------------------------------------------------------------------------------
defaultVisitor = Visitor
  { ctxExpr    = const
  , txExpr     = \_ x -> x
  , accExpr    = \_ _ -> mempty
  }

------------------------------------------------------------------------

fold         :: (Visitable s t, Monoid a) => Visitor s a ctx -> ctx -> a -> t -> a
fold v c a t = snd $ execVisitM v c a visit t

trans        :: (Visitable s t, Monoid a) => Visitor s a ctx -> ctx -> a -> t -> t
trans v c _ z = fst $ execVisitM v c mempty visit z

execVisitM :: Visitor s a ctx -> ctx -> a -> (Visitor s a ctx -> ctx -> t -> State a t) -> t -> (t, a)
execVisitM v c a f x = runState (f v c x) a

type VisitM acc = State acc

accum :: (Monoid a) => a -> VisitM a ()
accum !z = modify (mappend z)
  -- do
  -- !cur <- get
  -- put ((mappend $!! z) $!! cur)

(<$$>) :: (Monad m) => (a -> m b) -> [a] -> m [b]
f <$$> xs = f Misc.<$$> xs

-- (<$$>) ::  (Applicative f) => (a -> f b) -> [a] -> f [b]
-- f <$$> x = traverse f x
-- _ <$$> []     = return []
-- f <$$> (x:xs) = do
  -- !y  <- f x
  -- !ys <- f <$$> xs
  -- return (y:ys)
------------------------------------------------------------------------------
class Visitable s t | t -> s where
  visit :: (Monoid a) => Visitor s a c -> c -> t -> VisitM a t

instance Visitable s (Expr s) where
  visit = visitExpr

instance Visitable s (Reft s) where
  visit v c (Reft (x, ra)) = (Reft . (x, )) <$> visit v c ra

instance Visitable s (SortedReft s) where
  visit v c (RR t r) = RR t <$> visit v c r

instance Visitable s (Symbol s, SortedReft s) where
  visit v c (sym, sr) = (sym, ) <$> visit v c sr

instance Visitable s (BindEnv s) where
  visit v c = mapM (visit v c)

---------------------------------------------------------------------------------
-- WARNING: these instances were written for mapKVars over GInfos only;
-- check that they behave as expected before using with other clients.
instance Visitable s (SimpC s a) where
  visit v c x = do
    rhs' <- visit v c (_crhs x)
    return x { _crhs = rhs' }

instance Visitable s (SubC s a) where
  visit v c x = do
    lhs' <- visit v c (slhs x)
    rhs' <- visit v c (srhs x)
    return x { slhs = lhs', srhs = rhs' }

instance (Visitable s (c a)) => Visitable s (GInfo s c a) where
  visit v c x = do
    cm' <- mapM (visit v c) (cm x)
    bs' <- visit v c (bs x)
    ae' <- visit v c (ae x) 
    return x { cm = cm', bs = bs', ae = ae' }

instance Visitable s (AxiomEnv s) where 
  visit v c x = do 
    eqs'    <- mapM (visit v c) (aenvEqs   x) 
    simpls' <- mapM (visit v c) (aenvSimpl x) 
    return x { aenvEqs = eqs' , aenvSimpl = simpls'} 

instance Visitable s (Equation s) where 
  visit v c eq = do 
    body' <- visit v c (eqBody eq) 
    return eq { eqBody = body' } 

instance Visitable s (Rewrite s) where 
  visit v c rw = do 
    body' <- visit v c (smBody rw) 
    return rw { smBody = body' } 

---------------------------------------------------------------------------------
visitExpr :: (Monoid a) => Visitor s a ctx -> ctx -> Expr s -> VisitM a (Expr s)
visitExpr !v    = vE
  where
    vE !c !e    = do {-# SCC "visitExpr.vE.accum" #-} accum acc
                     {-# SCC "visitExpr.vE.step" #-}  step c' e'
      where !c'  = ctxExpr v c  e
            !e'  = txExpr  v c' e
            !acc = accExpr v c' e
    step _ !e@(ESym _)       = return e
    step _ !e@(ECon _)       = return e
    step _ !e@(EVar _)       = return e
    step !c !(EApp f e)      = EApp        <$> vE c f  <*> vE c e
    step !c !(ENeg e)        = ENeg        <$> vE c e
    step !c !(EBin o e1 e2)  = EBin o      <$> vE c e1 <*> vE c e2
    step !c !(EIte p e1 e2)  = EIte        <$> vE c p  <*> vE c e1 <*> vE c e2
    step !c !(ECst e t)      = (`ECst` t)  <$> vE c e
    step !c !(PAnd  ps)      = PAnd        <$> (vE c <$$> ps)
    step !c !(POr  ps)       = POr         <$> (vE c <$$> ps)
    step !c !(PNot p)        = PNot        <$> vE c p
    step !c !(PImp p1 p2)    = PImp        <$> vE c p1 <*> vE c p2
    step !c !(PIff p1 p2)    = PIff        <$> vE c p1 <*> vE c p2
    step !c !(PAtom r e1 e2) = PAtom r     <$> vE c e1 <*> vE c e2
    step !c !(PAll xts p)    = PAll   xts  <$> vE c p
    step !c !(ELam (x,t) e)  = ELam (x,t)  <$> vE c e
    step !c !(ECoerc a t e)  = ECoerc a t  <$> vE c e
    step !c !(PExist xts p)  = PExist xts  <$> vE c p
    step !c !(ETApp e s)     = (`ETApp` s) <$> vE c e
    step !c !(ETAbs e s)     = (`ETAbs` s) <$> vE c e
    step _  !p@(PKVar _ _)   = return p
    step !c !(PGrad k su i e) = PGrad k su i <$> vE c e

mapKVars :: (Ord s, Fixpoint s, Hashable s, Visitable s t, Show s) => (KVar s -> Maybe (Expr s)) -> t -> t
mapKVars f = mapKVars' f'
  where
    f' (kv', _) = f kv'

mapKVars' :: (Show s, Visitable s t, Hashable s, Ord s, Fixpoint s) => ((KVar s, Subst s) -> Maybe (Expr s)) -> t -> t
mapKVars' f            = trans kvVis () ()
  where
    kvVis              = defaultVisitor { txExpr = txK }
    txK _ (PKVar k su)
      | Just p' <- f (k, su) = subst su p'
    txK _ (PGrad k su _ _)
      | Just p' <- f (k, su) = subst su p'
    txK _ p            = p



mapGVars' :: (Show s, Fixpoint s, Ord s, Hashable s, Visitable s t) => ((KVar s, Subst s) -> Maybe (Expr s)) -> t -> t
mapGVars' f            = trans kvVis () ()
  where
    kvVis              = defaultVisitor { txExpr = txK }
    txK _ (PGrad k su _ _)
      | Just p' <- f (k, su) = subst su p'
    txK _ p            = p

mapExpr :: Visitable s t => (Expr s -> Expr s) -> t -> t
mapExpr f = trans (defaultVisitor {txExpr = const f}) () ()


mapMExpr :: (Monad m) => (Expr s -> m (Expr s)) -> Expr s -> m (Expr s)
mapMExpr f = go
  where
    go e@(ESym _)      = f e
    go e@(ECon _)      = f e
    go e@(EVar _)      = f e
    go e@(PKVar _ _)   = f e
    go (PGrad k s i e) = f =<< (PGrad k s i <$>  go e                     )
    go (ENeg e)        = f =<< (ENeg        <$>  go e                     )
    go (PNot p)        = f =<< (PNot        <$>  go p                     )
    go (ECst e t)      = f =<< ((`ECst` t)  <$>  go e                     )
    go (PAll xts p)    = f =<< (PAll   xts  <$>  go p                     )
    go (ELam (x,t) e)  = f =<< (ELam (x,t)  <$>  go e                     )
    go (ECoerc a t e)  = f =<< (ECoerc a t  <$>  go e                     )
    go (PExist xts p)  = f =<< (PExist xts  <$>  go p                     )
    go (ETApp e s)     = f =<< ((`ETApp` s) <$>  go e                     )
    go (ETAbs e s)     = f =<< ((`ETAbs` s) <$>  go e                     )
    go (EApp g e)      = f =<< (EApp        <$>  go g  <*> go e           )
    go (EBin o e1 e2)  = f =<< (EBin o      <$>  go e1 <*> go e2          )
    go (PImp p1 p2)    = f =<< (PImp        <$>  go p1 <*> go p2          )
    go (PIff p1 p2)    = f =<< (PIff        <$>  go p1 <*> go p2          )
    go (PAtom r e1 e2) = f =<< (PAtom r     <$>  go e1 <*> go e2          )
    go (EIte p e1 e2)  = f =<< (EIte        <$>  go p  <*> go e1 <*> go e2)
    go (PAnd  ps)      = f =<< (PAnd        <$> (go <$$> ps)              )
    go (POr  ps)       = f =<< (POr         <$> (go <$$> ps)              )

mapKVarSubsts :: Visitable s t => (KVar s -> Subst s -> Subst s) -> t -> t
mapKVarSubsts f          = trans kvVis () ()
  where
    kvVis                = defaultVisitor { txExpr = txK }
    txK _ (PKVar k su)   = PKVar k (f k su)
    txK _ (PGrad k su i e) = PGrad k (f k su) i e
    txK _ p              = p

newtype MInt = MInt Integer -- deriving (Eq, NFData)

instance Semigroup MInt where
  MInt m <> MInt n = MInt (m + n)

instance Monoid MInt where
  mempty  = MInt 0
  mappend = (<>)

size :: Visitable s t => t -> Integer
size t    = n
  where
    MInt n = fold szV () mempty t
    szV    = (defaultVisitor :: Visitor s MInt t) { accExpr = \ _ _ -> MInt 1 }


lamSize :: Visitable s t => t -> Integer
lamSize t    = n
  where
    MInt n = fold szV () mempty t
    szV    = (defaultVisitor :: Visitor s MInt t) { accExpr = accum }
    accum _ (ELam _ _) = MInt 1
    accum _ _          = MInt 0

eapps :: Visitable s t => t -> [Expr s]
eapps                 = fold eappVis () []
  where
    eappVis              = (defaultVisitor :: Visitor s [KVar s] t) { accExpr = eapp' }
    eapp' _ e@(EApp _ _) = [e]
    eapp' _ _            = []

kvars :: Visitable s t => t -> [KVar s]
kvars                 = fold kvVis () []
  where
    kvVis             = (defaultVisitor :: Visitor s [KVar s] t) { accExpr = kv' }
    kv' _ (PKVar k _)     = [k]
    kv' _ (PGrad k _ _ _) = [k]
    kv' _ _               = []

envKVars :: (Hashable s, Eq s, TaggedC s c a) => BindEnv s -> c a -> [KVar s]
envKVars be c = squish [ kvs sr |  (_, sr) <- clhs be c]
  where
    squish    = S.toList  . S.fromList . concat
    kvs       = kvars . sr_reft

envKVarsN :: (Hashable s, Eq s, TaggedC s c a) => BindEnv s -> c a -> [(KVar s, Int)]
envKVarsN be c = tally [ kvs sr |  (_, sr) <- clhs be c]
  where
    tally      = Misc.count . concat
    kvs        = kvars . sr_reft

rhsKVars :: (TaggedC s c a) => c a -> [KVar s]
rhsKVars = kvars . crhs -- rhsCs

isKvarC :: (Eq s, TaggedC s c a) => c a -> Bool
isKvarC = all isKvar . conjuncts . crhs

isConcC :: (Eq s, TaggedC s c a) => c a -> Bool
isConcC = all isConc . conjuncts . crhs

isKvar :: Expr s -> Bool
isKvar (PKVar {}) = True
isKvar (PGrad {}) = True
isKvar _          = False

isConc :: Expr s -> Bool
isConc = null . kvars

stripCasts :: (Visitable s t) => t -> t
stripCasts = trans (defaultVisitor { txExpr = const go }) () ()
  where
    go (ECst e _) = e
    go e          = e

-- stripCasts :: Expr s -> Expr s
-- stripCasts = mapExpr go
--  where
--    go (ECst e _) = e
--    go e          = e

--------------------------------------------------------------------------------
-- | @CoSub@ is a map from (coercion) ty-vars represented as 'FObj s'
--   to the ty-vars that they should be substituted with. Note the
--   domain and range are both FixSymbol and not the Int used for real ty-vars.
--------------------------------------------------------------------------------
type CoSub s = M.HashMap (Symbol s) (Sort s) 

applyCoSub :: (Eq s, Hashable s) => CoSub s -> Expr s -> Expr s
applyCoSub coSub      = mapExpr fE
  where
    fE (ECoerc s t e) = ECoerc  (txS s) (txS t) e
    fE (ELam (x,t) e) = ELam (x, txS t)         e
    fE e              = e
    txS               = mapSort fS
    fS (FObj a)       = {- FObj -} (txV a)
    fS t              = t
    txV a             = M.lookupDefault (FObj a) a coSub

---------------------------------------------------------------------------------
-- | Visitors over @Sort@
---------------------------------------------------------------------------------
foldSort :: (a -> Sort s -> a) -> a -> Sort s -> a
foldSort f = step
  where
    step b t           = go (f b t) t
    go b (FFunc t1 t2) = L.foldl' step b [t1, t2]
    go b (FApp t1 t2)  = L.foldl' step b [t1, t2]
    go b (FAbs _ t)    = go b t
    go b _             = b

mapSort :: (Sort s -> Sort s) -> Sort s -> Sort s
mapSort f = step
  where
    step !x           = go (f x)
    go !(FFunc t1 t2) = FFunc (step t1) (step t2)
    go !(FApp t1 t2)  = FApp  (step t1) (step t2)
    go !(FAbs i t)    = FAbs i (step t)
    go !t             = t

foldDataDecl :: (a -> Sort s -> a) -> a -> DataDecl s -> a
foldDataDecl f acc = L.foldl' f acc . dataDeclSorts

dataDeclSorts :: DataDecl s -> [Sort s]
dataDeclSorts = concatMap dataCtorSorts . ddCtors

dataCtorSorts :: DataCtor s -> [Sort s]
dataCtorSorts = map dfSort . dcFields
---------------------------------------------------------------
-- | String Constants -----------------------------------------
---------------------------------------------------------------

-- symConstLits    :: FInfo s a -> [(Symbol s, Sort s)]
-- symConstLits fi = [(symbol c, strSort) | c <- symConsts fi]

class SymConsts a where
  symConsts :: a -> [SymConst]

-- instance  SymConsts (FInfo s a) where
instance (SymConsts (c a)) => SymConsts (GInfo s c a) where
  symConsts fi = Misc.sortNub $ csLits ++ bsLits ++ qsLits
    where
      csLits   = concatMap symConsts $ M.elems  $  cm    fi
      bsLits   = symConsts           $ bs                fi
      qsLits   = concatMap symConsts $ qBody   <$> quals fi

instance SymConsts (BindEnv s) where
  symConsts    = concatMap (symConsts . snd) . M.elems . beBinds

instance SymConsts (SubC s a) where
  symConsts c  = symConsts (slhs c) ++
                 symConsts (srhs c)

instance SymConsts (SimpC s a) where
  symConsts c  = symConsts (crhs c)

instance SymConsts (SortedReft s) where
  symConsts = symConsts . sr_reft

instance SymConsts (Reft s) where
  symConsts (Reft (_, ra)) = getSymConsts ra


instance SymConsts (Expr s) where
  symConsts = getSymConsts

getSymConsts :: Visitable s t => t -> [SymConst]
getSymConsts         = fold scVis () []
  where
    scVis            = (defaultVisitor :: Visitor s [SymConst] t)  { accExpr = sc }
    sc _ (ESym c)    = [c]
    sc _ _           = []
