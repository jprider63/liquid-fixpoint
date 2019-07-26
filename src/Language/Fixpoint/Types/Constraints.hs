{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE PatternGuards              #-}

-- | This module contains the top-level QUERY data types and elements,
--   including (Horn) implication & well-formedness constraints and sets.
module Language.Fixpoint.Types.Constraints (

   -- * Top-level Queries
    FInfo, SInfo, GInfo (..), FInfoWithOpts(..)
  , convertFormat
  , Solver

   -- * Serializing
  , toFixpoint
  , writeFInfo
  , saveQuery

   -- * Constructing Queries
  , fi

  -- * Constraints
  , WfC (..), isGWfc, updateWfCExpr
  , SubC, SubcId
  , mkSubC, subcId, sid, senv, slhs, srhs, stag, subC, wfC
  , SimpC (..)
  , Tag
  , TaggedC, clhs, crhs
  -- , strengthenLhs
  , strengthenHyp
  , strengthenBinds

  -- * Accessing Constraints
  , addIds
  , sinfo
  , shiftVV
  , gwInfo, GWInfo (..)

  -- * Qualifiers
  , Qualifier   (..)
  , QualParam   (..)
  , QualPattern (..)
  , trueQual
  , qualifier
  , mkQual
  , remakeQual
  , mkQ 
  , qualBinds

  -- * Results
  , FixSolution
  , GFixSolution, toGFixSol
  , Result (..)
  , unsafe, isUnsafe, isSafe ,safe

  -- * Cut KVars
  , Kuts (..)
  , ksMember

  -- * Higher Order Logic
  , HOInfo (..)
  , allowHO
  , allowHOquals

  -- * Axioms
  , AxiomEnv (..)
  , Equation (..)
  , mkEquation
  , Rewrite  (..)

  -- * Misc  [should be elsewhere but here due to dependencies]
  , substVars
  , sortVars
  ) where

import qualified Data.Binary as B
import           Data.Generics             (Data)
import           Data.Semigroup            (Semigroup (..))
import           Data.Typeable             (Typeable)
import           Data.Hashable
import           GHC.Generics              (Generic)
import qualified Data.List                 as L -- (sort, nub, delete)
import           Data.Maybe                (catMaybes)
import           Control.DeepSeq
import           Control.Monad             (void)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Config hiding (allowHO)
import           Language.Fixpoint.Types.Triggers
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Substitutions
import           Language.Fixpoint.Types.Environments
import qualified Language.Fixpoint.Utils.Files as Files

import           Language.Fixpoint.Misc
import           Text.PrettyPrint.HughesPJ.Compat
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S

--------------------------------------------------------------------------------
-- | Constraints ---------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ type Tag = { v : [Int] | len v == 1 } @-}

type Tag           = [Int]

data WfC s a  =  WfC  { wenv  :: !IBindEnv
                    , wrft  :: (Symbol s, Sort s, KVar s)
                    , winfo :: !a
                    }
             | GWfC { wenv  :: !IBindEnv
                    , wrft  :: !(Symbol s, Sort s, KVar s)
                    , winfo :: !a
                    , wexpr :: !(Expr s)
                    , wloc  :: !GradInfo
                    }
              deriving (Eq, Generic, Functor)

data GWInfo s = GWInfo { gsym  :: Symbol s
                     , gsort :: Sort s
                     , gexpr :: Expr s
                     , ginfo :: GradInfo
                     }
              deriving (Eq, Generic)

gwInfo :: WfC s a -> GWInfo s
gwInfo (GWfC _ (x,s,_) _ e i)
  = GWInfo x s e i
gwInfo _
  = errorstar "gwInfo"

updateWfCExpr :: (Expr s -> Expr s) -> WfC s a -> WfC s a
updateWfCExpr _ w@(WfC {})  = w
updateWfCExpr f w@(GWfC {}) = w{wexpr = f (wexpr w)}

isGWfc :: WfC s a -> Bool
isGWfc (GWfC {}) = True
isGWfc (WfC  {}) = False

instance HasGradual s (WfC s a) where
  isGradual = isGWfc

type SubcId = Integer

data SubC s a = SubC
  { _senv  :: !IBindEnv
  , slhs   :: !(SortedReft s)
  , srhs   :: !(SortedReft s)
  , _sid   :: !(Maybe SubcId)
  , _stag  :: !Tag
  , _sinfo :: !a
  }
  deriving (Eq, Generic, Functor)

data SimpC s a = SimpC
  { _cenv  :: !IBindEnv
  , _crhs  :: !(Expr s)
  , _cid   :: !(Maybe Integer)
  , cbind  :: !BindId               -- ^ Id of lhs/rhs binder
  , _ctag  :: !Tag
  , _cinfo :: !a
  }
  deriving (Generic, Functor)

instance Loc a => Loc (SimpC s a) where 
  srcSpan = srcSpan . _cinfo

strengthenHyp :: (Fixpoint s, Ord s) => SInfo s a -> [(Integer, Expr s)] -> SInfo s a
strengthenHyp si ies = strengthenBinds si bindExprs
  where
    bindExprs        = safeFromList "strengthenHyp" [ (subcBind si i, e) | (i, e) <- ies ]

subcBind :: SInfo s a -> SubcId -> BindId
subcBind si i
  | Just c <- M.lookup i (cm si)
  = cbind c
  | otherwise
  = errorstar $ "Unknown subcId in subcBind: " ++ show i


strengthenBinds :: (Fixpoint s, Ord s) => SInfo s a -> M.HashMap BindId (Expr s) -> SInfo s a
strengthenBinds si m = si { bs = mapBindEnv f (bs si) }
  where
    f i (x, sr)      = case M.lookup i m of
                         Nothing -> (x, sr)
                         Just e  -> (x, strengthenSortedReft sr e)

strengthenSortedReft :: (IsListConName s, Fixpoint s, Ord s) => SortedReft s -> Expr s -> SortedReft s
strengthenSortedReft (RR s (Reft (v, r))) e = RR s (Reft (v, pAnd [r, e]))


{-
  [(Int, Expr)]  ==> [(BindId, Expr)]

 -}

-- strengthenLhs :: Expr s -> SubC s a -> SubC s a
-- strengthenLhs e subc = subc {slhs = go (slhs subc)}
--  where
--    go (RR s (Reft(v, r))) = RR s (Reft (v, pAnd [r, e]))

class TaggedC s c a | c -> s where
  senv  :: c a -> IBindEnv
  sid   :: c a -> Maybe Integer
  stag  :: c a -> Tag
  sinfo :: c a -> a
  clhs  :: BindEnv s -> c a -> [(Symbol s, SortedReft s)]
  crhs  :: c a -> Expr s

instance TaggedC s (SimpC s) a where
  senv      = _cenv
  sid       = _cid
  stag      = _ctag
  sinfo     = _cinfo
  crhs      = _crhs
  clhs be c = envCs be (senv c)

instance TaggedC s (SubC s) a where
  senv      = _senv
  sid       = _sid
  stag      = _stag
  sinfo     = _sinfo
  crhs      = reftPred . sr_reft . srhs
  clhs be c = sortedReftBind (slhs c) : envCs be (senv c)

sortedReftBind :: SortedReft s -> (Symbol s, SortedReft s)
sortedReftBind sr = (x, sr)
  where
    Reft (x, _)   = sr_reft sr

subcId :: (TaggedC s c a) => c a -> SubcId
subcId = mfromJust "subCId" . sid

---------------------------------------------------------------------------
-- | Solutions and Results
---------------------------------------------------------------------------

type GFixSolution s = GFixSol s (Expr s)

type FixSolution s = M.HashMap (KVar s) (Expr s)

newtype GFixSol s e = GSol (M.HashMap (KVar s) (e, [e]))
  deriving (Generic, Semigroup, Monoid, Functor)

toGFixSol :: M.HashMap (KVar s) (e, [e]) -> GFixSol s e
toGFixSol = GSol


data Result s a = Result 
  { resStatus    :: !(FixResult a)
  , resSolution  :: !(FixSolution s)
  , gresSolution :: !(GFixSolution s) 
  }
  deriving (Generic, Show, Functor)

instance (Eq s, Hashable s) => Semigroup (Result s a) where
  r1 <> r2  = Result stat soln gsoln
    where
      stat  = (resStatus r1)    <> (resStatus r2)
      soln  = (resSolution r1)  <> (resSolution r2)
      gsoln = (gresSolution r1) <> (gresSolution r2)

instance (Hashable s, Eq s) => Monoid (Result s a) where
  mempty        = Result mempty mempty mempty
  mappend       = (<>)

unsafe, safe :: (Eq s, Hashable s) => Result s a
unsafe = mempty {resStatus = Unsafe []}
safe   = mempty {resStatus = Safe}

isSafe :: Result s a -> Bool
isSafe (Result Safe _ _) = True
isSafe _                 = False

isUnsafe :: Result s a -> Bool
isUnsafe r | Unsafe _ <- resStatus r
  = True
isUnsafe _ = False

instance (Ord a, Fixpoint a) => Fixpoint (FixResult (SubC s a)) where
  toFix Safe             = text "Safe"
  -- toFix (UnknownError d) = text $ "Unknown Error: " ++ d
  toFix (Crash xs msg)   = vcat $ [ text "Crash!" ] ++  pprSinfos "CRASH: " xs ++ [parens (text msg)]
  toFix (Unsafe xs)      = vcat $ text "Unsafe:" : pprSinfos "WARNING: " xs

pprSinfos :: (Ord a, Fixpoint a) => String -> [SubC s a] -> [Doc]
pprSinfos msg = map ((text msg <->) . toFix) . L.sort . fmap sinfo

instance (Hashable s, Show s, Fixpoint s, Fixpoint a, Ord s) => Show (WfC s a) where
  show = showFix

instance (Fixpoint s, Ord s, Fixpoint a) => Show (SubC s a) where
  show = showFix

instance (Ord s, Fixpoint s, Fixpoint a) => Show (SimpC s a) where
  show = showFix

instance (Ord s, Fixpoint a, Fixpoint s) => PPrint (SubC s a) where
  pprintTidy _ = toFix

instance (Ord s, Fixpoint s, Fixpoint a) => PPrint (SimpC s a) where
  pprintTidy _ = toFix

instance (Hashable s, Ord s, Fixpoint a, Fixpoint s, Show s) => PPrint (WfC s a) where
  pprintTidy _ = toFix

instance (Fixpoint s, Fixpoint a, Ord s) => Fixpoint (SubC s a) where
  toFix c     = hang (text "\n\nconstraint:") 2 bd
     where bd =   toFix (senv c)
              $+$ text "lhs" <+> toFix (slhs c)
              $+$ text "rhs" <+> toFix (srhs c)
              $+$ (pprId (sid c) <+> text "tag" <+> toFix (stag c))
              $+$ toFixMeta (text "constraint" <+> pprId (sid c)) (toFix (sinfo c))

instance (Fixpoint s, Fixpoint a, Ord s) => Fixpoint (SimpC s a) where
  toFix c     = hang (text "\n\nsimpleConstraint:") 2 bd
     where bd =   toFix (senv c)
              $+$ text "rhs" <+> toFix (crhs c)
              $+$ (pprId (sid c) <+> text "tag" <+> toFix (stag c))
              $+$ toFixMeta (text "simpleConstraint" <+> pprId (sid c)) (toFix (sinfo c))

instance (Ord s, Fixpoint a, Fixpoint s, Show s, Hashable s) => Fixpoint (WfC s a) where
  toFix w     = hang (text "\n\nwf:") 2 bd
    where bd  =   toFix (wenv w)
              -- NOTE: this next line is printed this way for compatability with the OCAML solver
              $+$ text "reft" <+> toFix (RR t (Reft (v, PKVar k mempty)))
              $+$ toFixMeta (text "wf") (toFix (winfo w))
              $+$ if (isGWfc w) then (toFixMeta (text "expr") (toFix (wexpr w))) else mempty
          (v, t, k) = wrft w

toFixMeta :: Doc -> Doc -> Doc
toFixMeta k v = text "// META" <+> k <+> text ":" <+> v

pprId :: Show a => Maybe a -> Doc
pprId (Just i)  = "id" <+> tshow i
pprId _         = ""

instance (Fixpoint s, PPrint s, Ord s) => PPrint (GFixSolution s) where
  pprintTidy k (GSol xs) = vcat $ punctuate "\n\n" (pprintTidyGradual k <$> M.toList xs)

pprintTidyGradual :: (Ord s, Fixpoint s, PPrint s) => Tidy -> (KVar s, (Expr s, [Expr s])) -> Doc
pprintTidyGradual _ (x, (e, es)) = ppLocOfKVar x <+> text ":=" <+> (ppNonTauto " && " e <-> pprint es)

ppLocOfKVar :: KVar s -> Doc
ppLocOfKVar = text. dropWhile (/='(') . symbolString . symbol . kv

ppNonTauto :: (Eq s, Fixpoint s, PPrint s, Ord s) => Doc -> Expr s -> Doc
ppNonTauto d e
  | isTautoPred e = mempty
  | otherwise     = pprint e <-> d

instance (Ord s, PPrint s, Fixpoint s) => Show   (GFixSolution s) where
  show = showpp

----------------------------------------------------------------
instance (B.Binary s) => B.Binary (QualPattern s)
instance (B.Binary s) => B.Binary (QualParam s)
instance (Hashable s, Eq s, B.Binary s) => B.Binary (Qualifier s)
instance (B.Binary s, Eq s, Hashable s) => B.Binary (Kuts s)
instance B.Binary HOInfo
instance (Hashable s, Eq s, B.Binary s) => B.Binary (GWInfo s)
instance (B.Binary s, Eq s, Hashable s) => B.Binary (GFixSolution s)
instance (Hashable s, B.Binary s, Eq s, B.Binary a) => B.Binary (SubC s a)
instance (Hashable s, Eq s, B.Binary s, B.Binary a) => B.Binary (WfC s a)
instance (Hashable s, B.Binary s, Eq s, B.Binary a) => B.Binary (SimpC s a)
instance (B.Binary s, Eq s, Hashable s, B.Binary (c a), B.Binary a) => B.Binary (GInfo s c a)

instance (NFData s) => NFData (QualPattern s)
instance (NFData s) => NFData (QualParam s)
instance (NFData s) => NFData (Qualifier s)
instance (NFData s) =>  NFData (Kuts s)
instance NFData HOInfo
instance (NFData s) => NFData (GFixSolution s)
instance (NFData s) => NFData (GWInfo s)

instance (NFData s, NFData a) => NFData (SubC s a)
instance (NFData s, NFData a) => NFData (WfC s a)
instance (NFData s, NFData a) => NFData (SimpC s a)
instance (NFData s, NFData (c a), NFData a) => NFData (GInfo s c a)
instance (NFData s, NFData a) => NFData (Result s a)

---------------------------------------------------------------------------
-- | "Smart Constructors" for Constraints ---------------------------------
---------------------------------------------------------------------------

wfC :: (Fixpoint s, Fixpoint a, Ord s) => IBindEnv -> SortedReft s -> a -> [WfC s a]
wfC be sr x = if all isEmptySubst sus -- ++ gsus)
                 -- NV TO RJ This tests fails with [LT:=GHC.Types.LT][EQ:=GHC.Types.EQ][GT:=GHC.Types.GT]]
                 -- NV TO RJ looks like a resolution issue
                then [WfC be (v, sr_sort sr, k) x      | k         <- ks ]
                  ++ [GWfC be (v, sr_sort sr, k) x e i | (k, e, i) <- gs ]
                else errorstar msg
  where
    msg             = "wfKvar: malformed wfC " ++ show sr ++ "\n" ++ show (sus ++ gsus)
    Reft (v, ras)   = sr_reft sr
    (ks, sus)       = unzip $ go ras
    (gs, gsus)      = unzip $ go' ras

    go (PKVar k su) = [(k, su)]
    go (PAnd es)    = [(k, su) | PKVar k su <- es]
    go _            = []

    go' (PGrad k su i e) = [((k, e, i), su)]
    go' (PAnd es)      = concatMap go' es
    go' _              = []

mkSubC :: IBindEnv -> SortedReft s -> SortedReft s -> Maybe Integer -> Tag -> a -> SubC s a
mkSubC = SubC

subC :: (Ord s, Fixpoint s, Hashable s, Show s) => IBindEnv -> SortedReft s -> SortedReft s -> Maybe Integer -> Tag -> a -> [SubC s a]
subC γ sr1 sr2 i y z = [SubC γ sr1' (sr2' r2') i y z | r2' <- reftConjuncts r2]
   where
     RR t1 r1          = sr1
     RR t2 r2          = sr2
     sr1'              = RR t1 $ shiftVV r1  vv'
     sr2' r2'          = RR t2 $ shiftVV r2' vv'
     vv'               = mkVV i

mkVV :: Maybe Integer -> Symbol s
mkVV (Just i)  = FS . vv $ Just i
mkVV Nothing   = FS $ vvCon

shiftVV :: (IsListConName s, Hashable s, Eq s, Ord s, Fixpoint s, Show s) => Reft s -> Symbol s -> Reft s
shiftVV r@(Reft (v, ras)) v'
   | v == v'   = r
   | otherwise = Reft (v', subst1 ras (v, EVar v'))

addIds :: (Eq s, Hashable s, Ord s, Fixpoint s, Show s) => [SubC s a] -> [(Integer, SubC s a)]
addIds = zipWith (\i c -> (i, shiftId i $ c {_sid = Just i})) [1..]
  where 
    -- Adding shiftId to have distinct VV for SMT conversion
    shiftId i c = c { slhs = shiftSR i $ slhs c }
                    { srhs = shiftSR i $ srhs c }
    shiftSR i sr = sr { sr_reft = shiftR i $ sr_reft sr }
    shiftR i r@(Reft (v, _)) = shiftVV r (FS $ intSymbol (symbol v) i)

--------------------------------------------------------------------------------
-- | Qualifiers ----------------------------------------------------------------
--------------------------------------------------------------------------------
data Qualifier s = Q 
  { qName   :: !FixSymbol     -- ^ Name
  , qParams :: [QualParam s] -- ^ Parameters
  , qBody   :: !(Expr s)       -- ^ Predicate
  , qPos    :: !SourcePos  -- ^ Source Location
  }
  deriving (Eq, Show, Data, Typeable, Generic)

data QualParam s = QP 
  { qpSym  :: !FixSymbol
  , qpPat  :: !(QualPattern s)
  , qpSort :: !(Sort s)
  } 
  deriving (Eq, Show, Data, Typeable, Generic)

data QualPattern s
  = PatNone                 -- ^ match everything 
  | PatPrefix !(Symbol s) !Int  -- ^ str . $i  i.e. match prefix 'str' with suffix bound to $i
  | PatSuffix !Int !(Symbol s)  -- ^ $i . str  i.e. match suffix 'str' with prefix bound to $i
  | PatExact  !(Symbol s)       -- ^ str       i.e. exactly match 'str'
  deriving (Eq, Show, Data, Typeable, Generic)

trueQual :: (Fixpoint s, Eq s, Ord s) => Qualifier s
trueQual = Q (symbol ("QTrue" :: String)) [] mempty (dummyPos "trueQual")

instance Loc (Qualifier s) where
  srcSpan q = SS l l
    where
      l     = qPos q

instance (Eq s, Hashable s, Ord s, Fixpoint s, Show s) => Subable s (Qualifier s) where 
  syms   = qualFreeSymbols 
  subst  = mapQualBody . subst
  substf = mapQualBody . substf
  substa = mapQualBody . substa

mapQualBody :: (Expr s -> Expr s) -> Qualifier s -> Qualifier s
mapQualBody f q = q { qBody = f (qBody q) }
  
qualFreeSymbols :: (Show s, Fixpoint s, Ord s, Eq s, Hashable s) => Qualifier s -> [Symbol s]
qualFreeSymbols q = filter f xs 
  where
    f (FS s)      = not . isPrim $ s
    f _           = False
    xs            = syms (qBody q) L.\\ syms (qpSym <$> qParams q) 

instance (Fixpoint s, Eq s) => Fixpoint (QualParam s) where 
  toFix (QP x _ t) = toFix (x, t) 

instance (Fixpoint s, Eq s, PPrint s) => PPrint (QualParam s) where 
  pprintTidy k (QP x pat t) = pprintTidy k x <+> pprintTidy k pat <+> colon <+> pprintTidy k t 

instance (PPrint s) => PPrint (QualPattern s) where 
  pprintTidy _ PatNone         = "" 
  pprintTidy k (PatPrefix s i) = "as" <+> pprintTidy k s <+> ("$" <-> pprint i)
  pprintTidy k (PatSuffix s i) = "as" <+> ("$" <-> pprint i) <+> pprintTidy k s 
  pprintTidy k (PatExact  s  ) = "~"  <+> pprintTidy k s 

instance (Fixpoint s, Ord s) => Fixpoint (Qualifier s) where
  toFix = pprQual

instance (PPrint s) => PPrint (Qualifier s) where
  pprintTidy k q = "qualif" <+> pprintTidy k (qName q) <+> "defined at" <+> pprintTidy k (qPos q)

pprQual :: (Fixpoint s, Ord s) => Qualifier s -> Doc
pprQual (Q n xts p l) = text "qualif" <+> text (symbolString (symbol n)) <-> parens args <-> colon <+> parens (toFix p) <+> text "//" <+> toFix l
  where
    args              = intersperse comma (toFix <$> xts)

qualifier :: (Show s, Eq s, Hashable s, Ord s, Fixpoint s) => SEnv s (Sort s) -> SourcePos -> SEnv s (Sort s) -> FixSymbol -> Sort s -> Expr s -> Qualifier s
qualifier lEnv l γ v so p   = mkQ "Auto" ((v, so) : xts) p l
  where
    xs  = L.delete v $ L.nub $ syms p
    xts = catMaybes $ zipWith (envSort l lEnv γ) xs [0..]

mkQ :: FixSymbol -> [(FixSymbol, Sort s)] -> Expr s -> SourcePos -> Qualifier s 
mkQ n = Q n . qualParams

qualParams :: [(FixSymbol, Sort s)] -> [QualParam s]
qualParams xts = [ QP x PatNone t | (x, t) <- xts]

qualBinds   :: Qualifier s -> [(FixSymbol, Sort s)]
qualBinds q = [ (qpSym qp, qpSort qp) | qp <- qParams q ]

envSort :: (Eq s, Hashable s) => SourcePos -> SEnv s (Sort s) -> SEnv s (Sort s) -> Symbol s -> Integer -> Maybe (Symbol s, Sort s)
envSort l lEnv tEnv x i
  | Just t <- lookupSEnv x tEnv = Just (x, t)
  | Just _ <- lookupSEnv x lEnv = Nothing
  | otherwise                   = Just (x, ai)
  where
    ai  = {- trace msg $ -} fObj $ FS $ Loc l l $ tempSymbol "LHTV" i
    -- msg = "unknown symbol in qualifier: " ++ show x

remakeQual :: (Ord s) => Qualifier s -> Qualifier s
remakeQual q = mkQual (qName q) (qParams q) (qBody q) (qPos q)

-- | constructing qualifiers
mkQual :: (Ord s) => FixSymbol -> [QualParam s] -> Expr s -> SourcePos -> Qualifier s
mkQual n qps p = Q n qps' p 
  where
    qps'       = zipWith (\qp t' -> qp { qpSort = t'}) qps ts'
    ts'        = gSorts (qpSort <$> qps) 

gSorts :: (Ord s) => [Sort s] -> [Sort s]
gSorts ts = substVars su <$> ts 
  where
    su    = (`zip` [0..]) . sortNub . concatMap sortVars $ ts

substVars :: (Eq s) => [(Symbol s, Int)] -> Sort s -> Sort s
substVars su = mapSort' tx
  where
    tx (FObj x)
      | Just i <- lookup x su = FVar i
    tx t                      = t

sortVars :: Sort s -> [Symbol s]
sortVars = foldSort' go []
  where
    go b (FObj x) = x : b
    go b _        = b

-- COPIED from Visitor due to cyclic deps
mapSort' :: (Sort s -> Sort s) -> Sort s -> Sort s
mapSort' f = step
  where
    step             = go . f
    go (FFunc t1 t2) = FFunc (step t1) (step t2)
    go (FApp t1 t2)  = FApp (step t1) (step t2)
    go (FAbs i t)    = FAbs i (step t)
    go t             = t

-- COPIED from Visitor due to cyclic deps
foldSort' :: (a -> Sort s -> a) -> a -> Sort s -> a
foldSort' f = step
  where
    step b t           = go (f b t) t
    go b (FFunc t1 t2) = L.foldl' step b [t1, t2]
    go b (FApp t1 t2)  = L.foldl' step b [t1, t2]
    go b (FAbs _ t)    = go b t
    go b _             = b


--------------------------------------------------------------------------------
-- | Constraint Cut Sets -------------------------------------------------------
--------------------------------------------------------------------------------

newtype Kuts s = KS { ksVars :: S.HashSet (KVar s) }
               deriving (Eq, Show, Generic)

instance (Fixpoint s) => Fixpoint (Kuts s) where
  toFix (KS s) = vcat $ (("cut " <->) . toFix) <$> S.toList s

ksMember :: (Eq s, Hashable s) => KVar s -> Kuts s -> Bool
ksMember k (KS s) = S.member k s

instance (Eq s, Hashable s) => Semigroup (Kuts s) where
  k1 <> k2 = KS $ S.union (ksVars k1) (ksVars k2)

instance (Hashable s, Eq s) => Monoid (Kuts s) where
  mempty  = KS S.empty
  mappend = (<>)

------------------------------------------------------------------------
-- | Constructing Queries
------------------------------------------------------------------------
fi :: (Hashable s, Ord s, Fixpoint s, Show s)
   => [SubC s a]
   -> [WfC s a]
   -> BindEnv s
   -> SEnv s (Sort s)
   -> SEnv s (Sort s)
   -> Kuts s
   -> [Qualifier s]
   -> M.HashMap BindId a
   -> Bool
   -> Bool
   -> [Triggered (Expr s)]
   -> AxiomEnv s
   -> [DataDecl s]
   -> [BindId] 
   -> GInfo s (SubC s) a
fi cs ws binds ls ds ks qs bi aHO aHOq es axe adts ebs
  = FI { cm       = M.fromList $ addIds cs
       , ws       = M.fromListWith err [(k, w) | w <- ws, let (_, _, k) = wrft w]
       , bs       = foldr (adjustBindEnv stripReft) binds ebs
       , gLits    = ls
       , dLits    = ds
       , kuts     = ks
       , quals    = qs
       , bindInfo = bi
       , hoInfo   = HOI aHO aHOq
       , asserts  = es
       , ae       = axe
       , ddecls   = adts
       , ebinds   = ebs 
       }
  where
    --TODO handle duplicates gracefully instead (merge envs by intersect?)
    err = errorstar "multiple WfCs with same kvar"
    stripReft (sym, reft) = (sym, reft { sr_reft = trueReft })

------------------------------------------------------------------------
-- | Top-level Queries
------------------------------------------------------------------------

data FInfoWithOpts s a = FIO 
  { fioFI   :: FInfo s a
  , fioOpts :: [String]
  }

type FInfo s a   = GInfo s (SubC s) a
type SInfo s a   = GInfo s (SimpC s) a

data HOInfo = HOI 
  { hoBinds :: Bool          -- ^ Allow higher order binds in the environemnt
  , hoQuals :: Bool          -- ^ Allow higher order quals
  }
  deriving (Eq, Show, Generic)

allowHO, allowHOquals :: GInfo s c a -> Bool
allowHO      = hoBinds . hoInfo
allowHOquals = hoQuals . hoInfo

data GInfo s c a = FI 
  { cm       :: !(M.HashMap SubcId (c a))  -- ^ cst id |-> Horn Constraint
  , ws       :: !(M.HashMap (KVar s) (WfC s a))  -- ^ Kvar  |-> WfC defining its scope/args
  , bs       :: !(BindEnv s)                   -- ^ Bind  |-> (Symbol s, SortedReft s)
  , ebinds   :: ![BindId]                  -- ^ Subset of existential binders
  , gLits    :: !(SEnv s (Sort s))               -- ^ Global Constant symbols
  , dLits    :: !(SEnv s (Sort s))               -- ^ Distinct Constant symbols
  , kuts     :: !(Kuts s)                      -- ^ Set of KVars *not* to eliminate
  , quals    :: ![Qualifier s]               -- ^ Abstract domain
  , bindInfo :: !(M.HashMap BindId a)      -- ^ Metadata about binders
  , ddecls   :: ![DataDecl s]                -- ^ User-defined data declarations
  , hoInfo   :: !HOInfo                    -- ^ Higher Order info
  , asserts  :: ![Triggered (Expr s)]          -- ^ TODO: what is this?
  , ae       :: AxiomEnv s                   -- ^ Information about reflected function defs
  }
  deriving (Eq, Show, Functor, Generic)

instance HasGradual s (GInfo s c a) where
  isGradual info = any isGradual (M.elems $ ws info)

instance Semigroup HOInfo where
  i1 <> i2 = HOI { hoBinds = hoBinds i1 || hoBinds i2
                 , hoQuals = hoQuals i1 || hoQuals i2
                 }

instance Monoid HOInfo where
  mempty        = HOI False False

instance (Eq s, Hashable s) => Semigroup (GInfo s c a) where
  i1 <> i2 = FI { cm       = (cm i1)       <> (cm i2)
                , ws       = (ws i1)       <> (ws i2)
                , bs       = (bs i1)       <> (bs i2)
                , ebinds   = (ebinds i1)   <> (ebinds i2)
                , gLits    = (gLits i1)    <> (gLits i2)
                , dLits    = (dLits i1)    <> (dLits i2)
                , kuts     = (kuts i1)     <> (kuts i2)
                , quals    = (quals i1)    <> (quals i2)
                , bindInfo = (bindInfo i1) <> (bindInfo i2)
                , ddecls   = (ddecls i1)   <> (ddecls i2)
                , hoInfo   = (hoInfo i1)   <> (hoInfo i2)
                , asserts  = (asserts i1)  <> (asserts i2)
                , ae       = (ae i1)       <> (ae i2)
                }


instance (Eq s, Hashable s) => Monoid (GInfo s c a) where
  mempty        = FI { cm       = M.empty
                     , ws       = mempty 
                     , bs       = mempty 
                     , ebinds   = mempty 
                     , gLits    = mempty 
                     , dLits    = mempty 
                     , kuts     = mempty 
                     , quals    = mempty 
                     , bindInfo = mempty 
                     , ddecls   = mempty 
                     , hoInfo   = mempty 
                     , asserts  = mempty 
                     , ae       = mempty
                     } 

instance PTable (SInfo s a) where
  ptable z = DocTable [ (text "# Sub Constraints", pprint $ length $ cm z)
                      , (text "# WF  Constraints", pprint $ length $ ws z)
                      ]

--------------------------------------------------------------------------
-- | Rendering Queries
--------------------------------------------------------------------------
toFixpoint :: (IsListConName s, PPrint s, Ord s, Fixpoint s, Hashable s, Show s, Fixpoint a, Fixpoint (c a)) => Config -> GInfo s c a -> Doc
--------------------------------------------------------------------------
toFixpoint cfg x' =    cfgDoc   cfg
                  $++$ declsDoc x'
                  $++$ aeDoc    x'
                  $++$ qualsDoc x'
                  $++$ kutsDoc  x'
                --   $++$ packsDoc x'
                  $++$ gConDoc   x'
                  $++$ dConDoc   x'
                  $++$ bindsDoc
                  $++$ csDoc    x'
                  $++$ wsDoc    x'
                  $++$ binfoDoc x'
                  $++$ text "\n"
  where
    cfgDoc cfg    = text ("// " ++ show cfg)
    gConDoc       = sEnvDoc "constant"             . gLits
    dConDoc       = sEnvDoc "distinct"             . dLits
    csDoc         = vcat     . map toFix . M.elems . cm
    wsDoc         = vcat     . map toFix . M.elems . ws
    kutsDoc       = toFix    . kuts
    -- packsDoc      = toFix    . packs
    declsDoc      = vcat     . map ((text "data" <+>) . toFix) . ddecls
    (ubs, ebs)    = splitByQuantifiers (bs x') (ebinds x')
    bindsDoc      = toFix    ubs
               $++$ toFix    ebs
    qualsDoc      = vcat     . map toFix . quals
    aeDoc         = toFix    . ae
    metaDoc (i,d) = toFixMeta (text "bind" <+> toFix i) (toFix d)
    mdata         = metadata cfg
    binfoDoc
      | mdata     = vcat     . map metaDoc . M.toList . bindInfo
      | otherwise = \_ -> text "\n"

($++$) :: Doc -> Doc -> Doc
x $++$ y = x $+$ text "\n" $+$ y

sEnvDoc :: (IsListConName s, Eq s, Fixpoint s) => Doc -> SEnv s (Sort s) -> Doc
sEnvDoc d       = vcat . map kvD . toListSEnv
  where
    kvD (c, so) = d <+> toFix c <+> ":" <+> parens (toFix so)

writeFInfo :: (IsListConName s, PPrint s, Show s, Hashable s, Fixpoint s, Ord s, Fixpoint a, Fixpoint (c a)) => Config -> GInfo s c a -> FilePath -> IO ()
writeFInfo cfg fq f = writeFile f (render $ toFixpoint cfg fq)

--------------------------------------------------------------------------------
-- | Query Conversions: FInfo to SInfo
--------------------------------------------------------------------------------
convertFormat :: (Fixpoint a) => FInfo s a -> SInfo s a
--------------------------------------------------------------------------------
convertFormat fi = fi' { cm = subcToSimpc bindm <$> cm fi' }
  where
    (bindm, fi') = M.foldlWithKey' outVV (M.empty, fi) $ cm fi

subcToSimpc :: BindM -> SubC s a -> SimpC s a
subcToSimpc m s = SimpC
  { _cenv       = senv s
  , _crhs       = reftPred $ sr_reft $ srhs s
  , _cid        = sid s
  , cbind      = safeLookup "subcToSimpc" (subcId s) m
  , _ctag       = stag s
  , _cinfo      = sinfo s
  }

outVV :: (BindM, FInfo s a) -> Integer -> SubC s a -> (BindM, FInfo s a)
outVV (m, fi) i c = (m', fi')
  where
    fi'           = fi { bs = be', cm = cm' }
    m'            = M.insert i bId m
    (bId, be')    = insertBindEnv x sr $ bs fi
    cm'           = M.insert i c' $ cm fi
    c'            = c { _senv = insertsIBindEnv [bId] $ senv c }
    sr            = slhs c
    x             = reftBind $ sr_reft sr

type BindM = M.HashMap Integer BindId

---------------------------------------------------------------------------
-- | Top level Solvers ----------------------------------------------------
---------------------------------------------------------------------------
type Solver s a = Config -> FInfo s a -> IO (Result s (Integer, a))

--------------------------------------------------------------------------------
saveQuery :: (IsListConName s, PPrint s, Fixpoint s, Ord s, Show s, Hashable s, B.Binary s, Eq s) => Config -> FInfo s a -> IO ()
--------------------------------------------------------------------------------
saveQuery cfg fi = {- when (save cfg) $ -} do
  let fi'  = void fi
  saveBinaryQuery cfg fi'
  saveTextQuery cfg   fi'

saveBinaryQuery :: (B.Binary s, Eq s, Hashable s) => Config -> FInfo s () -> IO ()
saveBinaryQuery cfg fi = do
  let bfq  = queryFile Files.BinFq cfg
  putStrLn $ "Saving Binary Query: " ++ bfq ++ "\n"
  ensurePath bfq
  B.encodeFile bfq fi

saveTextQuery :: (IsListConName s, PPrint s, Show s, Ord s, Fixpoint s, Hashable s) => Config -> FInfo s () -> IO ()
saveTextQuery cfg fi = do
  let fq   = queryFile Files.Fq cfg
  putStrLn $ "Saving Text Query: "   ++ fq ++ "\n"
  ensurePath fq
  writeFile fq $ render (toFixpoint cfg fi)

---------------------------------------------------------------------------
-- | Axiom Instantiation Information --------------------------------------
---------------------------------------------------------------------------
data AxiomEnv s = AEnv
  { aenvEqs     :: ![Equation s]
  , aenvSimpl   :: ![Rewrite s]
  , aenvExpand  :: M.HashMap SubcId Bool
  }
  deriving (Eq, Show, Generic)

instance (Hashable s, B.Binary s, Eq s) => B.Binary (AxiomEnv s)
instance (Hashable s, B.Binary s, Eq s) => B.Binary (Rewrite s)
instance (Hashable s, Eq s, B.Binary s) => B.Binary (Equation s)
instance B.Binary SMTSolver
instance B.Binary Eliminate
instance (NFData s) => NFData (AxiomEnv s)
instance (NFData s) => NFData (Rewrite s)
instance (NFData s) => NFData (Equation s)
instance NFData SMTSolver
instance NFData Eliminate

instance Semigroup (AxiomEnv s) where
  a1 <> a2        = AEnv aenvEqs' aenvSimpl' aenvExpand'
    where
      aenvEqs'    = (aenvEqs a1)    <> (aenvEqs a2)
      aenvSimpl'  = (aenvSimpl a1)  <> (aenvSimpl a2)
      aenvExpand' = (aenvExpand a1) <> (aenvExpand a2)

instance Monoid (AxiomEnv s) where
  mempty          = AEnv [] [] (M.fromList [])
  mappend         = (<>)

instance (IsListConName s, Show s, Fixpoint s, Ord s) => PPrint (AxiomEnv s) where
  pprintTidy _ = text . show

data Equation s = Equ
  { eqName :: !(Symbol s)           -- ^ name of reflected function
  , eqArgs :: [(Symbol s, Sort s)]  -- ^ names of parameters
  , eqBody :: !(Expr s)             -- ^ definition of body
  , eqSort :: !(Sort s)             -- ^ sort of body
  , eqRec  :: !Bool             -- ^ is this a recursive definition
  }
  deriving (Eq, Show, Generic)

mkEquation :: (IsListConName s, Eq s, Hashable s, Ord s, Fixpoint s, Show s) => Symbol s -> [(Symbol s, Sort s)] -> Expr s -> Sort s -> Equation s
mkEquation f xts e out = Equ f xts e out (f `elem` syms e)

instance (IsListConName s, Show s, Fixpoint s, Eq s, Hashable s, Ord s) => Subable s (Equation s) where
  syms   a = syms (eqBody a) -- ++ F.syms (axiomEq a)
  subst su = mapEqBody (subst su)
  substf f = mapEqBody (substf f)
  substa f = mapEqBody (substa f)

mapEqBody :: (Expr s -> Expr s) -> Equation s -> Equation s
mapEqBody f a = a { eqBody = f (eqBody a) }

instance (IsListConName s, Fixpoint s, Ord s, PPrint s) => PPrint (Equation s) where
  pprintTidy _ = toFix

ppArgs :: (PPrint a) => [a] -> Doc
ppArgs = parens . intersperse ", " . fmap pprint

-- eg  SMeasure (f D [x1..xn] e)
-- for f (D x1 .. xn) = e
data Rewrite s  = SMeasure
  { smName  :: Symbol s         -- eg. f
  , smDC    :: Symbol s         -- eg. D
  , smArgs  :: [Symbol s]       -- eg. xs
  , smBody  :: Expr s           -- eg. e[xs]
  }
  deriving (Eq, Show, Generic)

instance (IsListConName s, Fixpoint s, Ord s, PPrint s) => Fixpoint (AxiomEnv s) where
  toFix axe = vcat ((toFix <$> aenvEqs axe) ++ (toFix <$> aenvSimpl axe))
              $+$ text "expand" <+> toFix (pairdoc <$> M.toList(aenvExpand axe))
    where
      pairdoc (x,y) = text $ show x ++ " : " ++ show y

instance Fixpoint Doc where
  toFix = id

instance (IsListConName s, Ord s, Eq s, PPrint s, Fixpoint s) => Fixpoint (Equation s) where
  toFix (Equ f xs e _ _) = "define" <+> toFix f <+> ppArgs xs <+> text "=" <+> parens (toFix e)

instance (IsListConName s, Ord s, Fixpoint s) => Fixpoint (Rewrite s) where
  toFix (SMeasure f d xs e)
    = text "match"
   <+> toFix f
   <+> parens (toFix d <+> hsep (toFix <$> xs))
   <+> text " = "
   <+> parens (toFix e)

instance (IsListConName s, Ord s, Fixpoint s) => PPrint (Rewrite s) where
  pprintTidy _ = toFix
