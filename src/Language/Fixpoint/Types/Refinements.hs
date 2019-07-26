{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE FunctionalDependencies     #-}
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
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE PatternSynonyms            #-}

-- | This module has the types for representing terms in the refinement logic.

module Language.Fixpoint.Types.Refinements (

  -- * Representing Terms
    SymConst (..)
  , Constant (..)
  , Bop (..)
  , Brel (..)
  , Expr (..), Pred
  , GradInfo (..)
  , pattern PTrue, pattern PTop, pattern PFalse, pattern EBot
  , pattern ETimes, pattern ERTimes, pattern EDiv, pattern ERDiv
  , pattern EEq
  , KVar (..)
  , Subst (..)
  , KVSub (..)
  , Reft (..)
  , SortedReft (..)

  -- * Constructing Terms
  , eVar, elit
  , eProp
  , pAnd, pOr, pIte
  , (&.&), (|.|)
  , pExist
  , mkEApp
  , mkProp
  , intKvar
  , vv_

  -- * Generalizing Embedding with Typeclasses
  , Expression (..)
  , Predicate (..)
  , Subable (..)
  , Reftable (..)

  -- * Constructors
  , reft                    -- "smart
  , trueSortedReft          -- trivial reft
  , trueReft, falseReft     -- trivial reft
  , exprReft                -- singleton: v == e
  , notExprReft             -- singleton: v /= e
  , uexprReft               -- singleton: v ~~ e
  , symbolReft              -- singleton: v == x
  , usymbolReft             -- singleton: v ~~ x
  , propReft                -- singleton: v <=> p
  , predReft                -- any pred : p
  , reftPred
  , reftBind

  -- * Predicates
  , isFunctionSortedReft, functionSort
  , isNonTrivial
  , isContraPred
  , isTautoPred
  , isSingletonExpr 
  , isSingletonReft
  , isFalse

  -- * Destructing
  , flattenRefas
  , conjuncts
  , eApps
  , eAppC
  , splitEApp
  , splitPAnd
  , reftConjuncts

  -- * Transforming
  , mapPredReft
  , pprintReft

  , debruijnIndex

  -- * Gradual Type Manipulation
  , pGAnds, pGAnd
  , HasGradual (..)
  , srcGradInfo

  ) where

import           Prelude hiding ((<>))
import qualified Data.Binary as B
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           Data.Hashable
import           GHC.Generics              (Generic)
import           Data.List                 (foldl', partition)
import           Data.String
import           Data.Text                 (Text)
import qualified Data.Text                 as T
import qualified Data.HashMap.Strict       as M
import           Control.DeepSeq
import           Data.Maybe                (isJust)
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Misc
import           Text.PrettyPrint.HughesPJ.Compat

-- import           Text.Printf               (printf)


instance (NFData s) => NFData (KVar s)
instance NFData SrcSpan
instance (NFData s) => NFData (Subst s)
instance NFData GradInfo
instance NFData s => NFData (Constant s)
instance NFData SymConst
instance NFData Brel
instance NFData Bop
instance (NFData s) => NFData (Expr s)
instance (NFData s) => NFData (Reft s)
instance (NFData s) => NFData (SortedReft s)

instance (Hashable k, Eq k, B.Binary k, B.Binary v) => B.Binary (M.HashMap k v) where
  put = B.put . M.toList
  get = M.fromList <$> B.get

instance (Eq a, Hashable a, B.Binary a, B.Binary s) => B.Binary (TCEmb s a) 
instance B.Binary SrcSpan
instance (B.Binary s) => B.Binary (KVar s)
instance (Eq s, Hashable s, B.Binary s) => B.Binary (Subst s)
instance B.Binary GradInfo
instance B.Binary s => B.Binary (Constant s)
instance B.Binary SymConst
instance B.Binary Brel
instance B.Binary Bop
instance (Eq s, B.Binary s, Hashable s) => B.Binary (Expr s)
instance (Hashable s, B.Binary s, Eq s) => B.Binary (Reft s)
instance (Eq s, B.Binary s, Hashable s) => B.Binary (SortedReft s)

reftConjuncts :: (IsListConName s, Eq s, Fixpoint s, Ord s) => Reft s -> [Reft s]
reftConjuncts (Reft (v, ra)) = [Reft (v, ra') | ra' <- ras']
  where
    ras'                     = if null ps then ks else ((pAnd ps) : ks)
    (ks, ps)                 = partition (\p -> isKvar p || isGradual p) $ refaConjuncts ra

isKvar :: Expr s -> Bool
isKvar (PKVar _ _) = True
isKvar _           = False

class HasGradual s a | a -> s where
  isGradual :: a -> Bool
  gVars     :: a -> [KVar s]
  gVars _ = [] 
  ungrad    :: a -> a
  ungrad x = x 

instance HasGradual s (Expr s) where
  isGradual (PGrad {}) = True
  isGradual (PAnd xs)  = any isGradual xs
  isGradual _          = False

  gVars (PGrad k _ _ _) = [k]
  gVars (PAnd xs)       = concatMap gVars xs
  gVars _               = []

  ungrad (PGrad {}) = PTrue
  ungrad (PAnd xs)  = PAnd (ungrad <$> xs )
  ungrad e          = e


instance HasGradual s (Reft s) where
  isGradual (Reft (_,r)) = isGradual r
  gVars (Reft (_,r))     = gVars r
  ungrad (Reft (x,r))    = Reft(x, ungrad r)

instance HasGradual s (SortedReft s) where
  isGradual = isGradual . sr_reft
  gVars     = gVars . sr_reft
  ungrad r  = r {sr_reft = ungrad (sr_reft r)}

refaConjuncts :: (Eq s) => Expr s -> [Expr s]
refaConjuncts p = [p' | p' <- conjuncts p, not $ isTautoPred p']

--------------------------------------------------------------------------------
-- | Kvars ---------------------------------------------------------------------
--------------------------------------------------------------------------------

newtype KVar s = KV { kv :: Symbol s }
               deriving (Eq, Ord, Data, Typeable, Generic)

instance IsString s => IsString (KVar s)

intKvar :: Integer -> KVar s
intKvar = KV . FS . intSymbol "k_"

instance (Show s) => Show (KVar s) where
  show (KV x) = "$" ++ show x

instance (Hashable s) => Hashable (KVar s)
instance Hashable Brel
instance Hashable Bop
instance Hashable SymConst
instance Hashable s => Hashable (Constant s)
instance Hashable GradInfo 
instance Hashable s => Hashable (Subst s)
instance Hashable s => Hashable (Expr s)

--------------------------------------------------------------------------------
-- | Substitutions -------------------------------------------------------------
--------------------------------------------------------------------------------
newtype Subst s = Su (M.HashMap (Symbol s) (Expr s))
                deriving (Eq, Data, Typeable, Generic)

instance (IsListConName s, Eq s, Fixpoint s, Ord s) => Show (Subst s) where
  show = showFix

instance (IsListConName s, Eq s, Fixpoint s, Ord s) => Fixpoint (Subst s) where
  toFix (Su m) = case hashMapToAscList m of
                   []  -> empty
                   xys -> hcat $ map (\(x,y) -> brackets $ toFix x <-> text ":=" <-> toFix y) xys

instance (IsListConName s, Eq s, Fixpoint s, Ord s) => PPrint (Subst s) where
  pprintTidy _ = toFix

data KVSub s = KVS
  { ksuVV    :: Symbol s
  , ksuSort  :: Sort s
  , ksuKVar  :: KVar s
  , ksuSubst :: Subst s
  } deriving (Eq, Data, Typeable, Generic, Show)

instance (IsListConName s, Eq s, Fixpoint s, PPrint s, Ord s) => PPrint (KVSub s) where
  pprintTidy k ksu = pprintTidy k (ksuVV ksu, ksuKVar ksu, ksuSubst ksu)

--------------------------------------------------------------------------------
-- | Expressions ---------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Uninterpreted constants that are embedded as  "constant symbol : Str"

data SymConst = SL !Text
              deriving (Eq, Ord, Show, Data, Typeable, Generic)

data Constant s = I !Integer
               | R !Double
               | L !Text !(Sort s)
               deriving (Eq, Ord, Show, Data, Typeable, Generic)

data Brel = Eq | Ne | Gt | Ge | Lt | Le | Ueq | Une
            deriving (Eq, Ord, Show, Data, Typeable, Generic)

data Bop  = Plus | Minus | Times | Div | Mod | RTimes | RDiv
            deriving (Eq, Ord, Show, Data, Typeable, Generic)
            -- NOTE: For "Mod" 2nd expr should be a constant or a var *)

data Expr s = ESym !SymConst
            | ECon !(Constant s)
            | EVar !(Symbol s)
            | EApp !(Expr s) !(Expr s)
            | ENeg !(Expr s)
            | EBin !Bop !(Expr s) !(Expr s)
            | EIte !(Expr s) !(Expr s) !(Expr s)
            | ECst !(Expr s) !(Sort s)
            | ELam !(Symbol s, Sort s)   !(Expr s)
            | ETApp !(Expr s) !(Sort s)
            | ETAbs !(Expr s) !(Symbol s)
            | PAnd   ![(Expr s)]
            | POr    ![(Expr s)]
            | PNot   !(Expr s)
            | PImp   !(Expr s) !(Expr s)
            | PIff   !(Expr s) !(Expr s)
            | PAtom  !Brel  !(Expr s) !(Expr s)
            | PKVar  !(KVar s) !(Subst s)
            | PAll   ![(Symbol s, Sort s)] !(Expr s)
            | PExist ![(Symbol s, Sort s)] !(Expr s)
            | PGrad  !(KVar s) !(Subst s) !GradInfo !(Expr s)
            | ECoerc !(Sort s) !(Sort s) !(Expr s)  
            deriving (Eq, Show, Data, Typeable, Generic)

type Pred s = Expr s

pattern PTrue         = PAnd []
pattern PTop          = PAnd []
pattern PFalse        = POr  []
pattern EBot          = POr  []
pattern EEq e1 e2     = PAtom Eq    e1 e2
pattern ETimes e1 e2  = EBin Times  e1 e2
pattern ERTimes e1 e2 = EBin RTimes e1 e2
pattern EDiv e1 e2    = EBin Div    e1 e2
pattern ERDiv e1 e2   = EBin RDiv   e1 e2


data GradInfo = GradInfo {gsrc :: SrcSpan, gused :: Maybe SrcSpan}
          deriving (Eq, Show, Data, Typeable, Generic)

srcGradInfo :: SourcePos -> GradInfo
srcGradInfo src = GradInfo (SS src src) Nothing

mkEApp :: LocSymbol s -> [Expr s] -> Expr s
mkEApp = eApps . EVar . dropLoc

eApps :: Expr s -> [Expr s] -> Expr s
eApps f es  = foldl' EApp f es

splitEApp :: Expr s -> (Expr s, [Expr s])
splitEApp = go []
  where
    go acc (EApp f e) = go (e:acc) f
    go acc e          = (e, acc)

splitPAnd :: Expr s -> [Expr s]
splitPAnd (PAnd es) = concatMap splitPAnd es
splitPAnd e         = [e]

eAppC :: Sort s -> Expr s -> Expr s -> Expr s
eAppC s e1 e2 = ECst (EApp e1 e2) s

--------------------------------------------------------------------------------
debruijnIndex :: Expr s -> Int
debruijnIndex = go
  where
    go (ELam _ e)      = 1 + go e
    go (ECst e _)      = go e
    go (EApp e1 e2)    = go e1 + go e2
    go (ESym _)        = 1
    go (ECon _)        = 1
    go (EVar _)        = 1
    go (ENeg e)        = go e
    go (EBin _ e1 e2)  = go e1 + go e2
    go (EIte e e1 e2)  = go e + go e1 + go e2
    go (ETAbs e _)     = go e
    go (ETApp e _)     = go e
    go (PAnd es)       = foldl (\n e -> n + go e) 0 es
    go (POr es)        = foldl (\n e -> n + go e) 0 es
    go (PNot e)        = go e
    go (PImp e1 e2)    = go e1 + go e2
    go (PIff e1 e2)    = go e1 + go e2
    go (PAtom _ e1 e2) = go e1 + go e2
    go (PAll _ e)      = go e
    go (PExist _ e)    = go e
    go (PKVar _ _)     = 1
    go (PGrad _ _ _ e) = go e
    go (ECoerc _ _ e)  = go e

-- | Parsed refinement of @FixSymbol@ as @Expr@
--   e.g. in '{v: _ | e }' v is the @FixSymbol@ and e the @Expr@
newtype Reft s = Reft (Symbol s, Expr s)
               deriving (Eq, Data, Typeable, Generic)

data SortedReft s = RR { sr_sort :: !(Sort s), sr_reft :: !(Reft s) }
                  deriving (Eq, Data, Typeable, Generic)

elit :: Located (Symbol s) -> Sort s -> Expr s
elit l s = ECon $ L (symbolText . symbol $ val l) s

instance (Eq s, Fixpoint s, IsListConName s) => Fixpoint (Constant s) where
  toFix (I i)   = toFix i
  toFix (R i)   = toFix i
  toFix (L s t) = parens $ text "lit" <+> text "\"" <-> toFix s <-> text "\"" <+> toFix t

--------------------------------------------------------------------------------
-- | String Constants ----------------------------------------------------------
--------------------------------------------------------------------------------

-- | Replace all symbol-representations-of-string-literals with string-literal
--   Used to transform parsed output from fixpoint back into fq.

instance FixSymbolic SymConst where
  symbol = encodeSymConst

encodeSymConst        :: SymConst -> FixSymbol
encodeSymConst (SL s) = litSymbol $ symbol s

-- _decodeSymConst :: FixSymbol -> Maybe SymConst
-- _decodeSymConst = fmap (SL . symbolText) . unLitSymbol

instance Fixpoint SymConst where
  toFix  = toFix . encodeSymConst

instance (Fixpoint s) => Fixpoint (KVar s) where
  toFix (KV k) = text "$" <-> toFix k

instance Fixpoint Brel where
  toFix Eq  = text "="
  toFix Ne  = text "!="
  toFix Ueq = text "~~"
  toFix Une = text "!~"
  toFix Gt  = text ">"
  toFix Ge  = text ">="
  toFix Lt  = text "<"
  toFix Le  = text "<="

instance Fixpoint Bop where
  toFix Plus   = text "+"
  toFix Minus  = text "-"
  toFix RTimes = text "*."
  toFix Times  = text "*"
  toFix Div    = text "/"
  toFix RDiv   = text "/."
  toFix Mod    = text "mod"

instance (IsListConName s, Fixpoint s, Eq s, Ord s) => Fixpoint (Expr s) where
  toFix (ESym c)       = toFix $ encodeSymConst c
  toFix (ECon c)       = toFix c
  toFix (EVar s)       = toFix s
  toFix e@(EApp _ _)   = parens $ hcat $ punctuate " " $ toFix <$> (f:es) where (f, es) = splitEApp e
  toFix (ENeg e)       = parens $ text "-"  <+> parens (toFix e)
  toFix (EBin o e1 e2) = parens $ toFix e1  <+> toFix o <+> toFix e2
  toFix (EIte p e1 e2) = parens $ text "if" <+> toFix p <+> text "then" <+> toFix e1 <+> text "else" <+> toFix e2
  -- toFix (ECst e _so)   = toFix e
  toFix (ECst e so)    = parens $ toFix e   <+> text " : " <+> toFix so
  -- toFix (EBot)         = text "_|_"
  -- toFix PTop           = text "???"
  toFix PTrue          = text "true"
  toFix PFalse         = text "false"
  toFix (PNot p)       = parens $ text "~" <+> parens (toFix p)
  toFix (PImp p1 p2)   = parens $ toFix p1 <+> text "=>" <+> toFix p2
  toFix (PIff p1 p2)   = parens $ toFix p1 <+> text "<=>" <+> toFix p2
  toFix (PAnd ps)      = text "&&" <+> toFix ps
  toFix (POr  ps)      = text "||" <+> toFix ps
  toFix (PAtom r e1 e2)  = parens $ toFix e1 <+> toFix r <+> toFix e2
  toFix (PKVar k su)     = toFix k <-> toFix su
  toFix (PAll xts p)     = "forall" <+> (toFix xts
                                        $+$ ("." <+> toFix p))
  toFix (PExist xts p)   = "exists" <+> (toFix xts
                                        $+$ ("." <+> toFix p))
  toFix (ETApp e s)      = text "tapp" <+> toFix e <+> toFix s
  toFix (ETAbs e s)      = text "tabs" <+> toFix e <+> toFix s
  toFix (PGrad k _ _ e)  = toFix e <+> text "&&" <+> toFix k -- text "??" -- <+> toFix k <+> toFix su
  toFix (ECoerc a t e)   = parens (text "coerce" <+> toFix a <+> text "~" <+> toFix t <+> text "in" <+> toFix e)
  toFix (ELam (x,s) e)   = text "lam" <+> toFix x <+> ":" <+> toFix s <+> "." <+> toFix e

  simplify (PAnd [])     = PTrue
  simplify (POr  [])     = PFalse
  simplify (PAnd [p])    = simplify p
  simplify (POr  [p])    = simplify p

  simplify (PGrad k su i e)
    | isContraPred e      = PFalse
    | otherwise           = PGrad k su i (simplify e)

  simplify (PAnd ps)
    | any isContraPred ps = PFalse
    | otherwise           = PAnd $ filter (not . isTautoPred) $ map simplify ps

  simplify (POr  ps)
    | any isTautoPred ps = PTrue
    | otherwise          = POr  $ filter (not . isContraPred) $ map simplify ps

  simplify p
    | isContraPred p     = PFalse
    | isTautoPred  p     = PTrue
    | otherwise          = p

isContraPred   :: (Eq s) => Expr s -> Bool
isContraPred z = eqC z || (z `elem` contras)
  where
    contras    = [PFalse]

    eqC (PAtom Eq (ECon x) (ECon y))
               = x /= y
    eqC (PAtom Ueq (ECon x) (ECon y))
               = x /= y
    eqC (PAtom Ne x y)
               = x == y
    eqC (PAtom Une x y)
               = x == y
    eqC _      = False

isTautoPred   :: (Eq s) => Expr s -> Bool
isTautoPred z  = z == PTop || z == PTrue || eqT z
  where
    eqT (PAnd [])
               = True
    eqT (PAtom Le x y)
               = x == y
    eqT (PAtom Ge x y)
               = x == y
    eqT (PAtom Eq x y)
               = x == y
    eqT (PAtom Ueq x y)
               = x == y
    eqT (PAtom Ne (ECon x) (ECon y))
               = x /= y
    eqT (PAtom Une (ECon x) (ECon y))
               = x /= y
    eqT _      = False

isEq  :: Brel -> Bool
isEq r          = r == Eq || r == Ueq

instance (IsListConName s, Eq s, Fixpoint s) => PPrint (Constant s) where
  pprintTidy _ = toFix

instance PPrint Brel where
  pprintTidy _ Eq = "=="
  pprintTidy _ Ne = "/="
  pprintTidy _ r  = toFix r

instance PPrint Bop where
  pprintTidy _  = toFix

instance (IsListConName s, Eq s, Fixpoint s) => PPrint (Sort s) where
  pprintTidy _ = toFix

instance (IsListConName s, Eq s, Fixpoint s, PPrint a) => PPrint (TCEmb s a) where 
  pprintTidy k = pprintTidy k . tceToList 

instance (PPrint s) => PPrint (KVar s) where
  pprintTidy _ (KV x) = text "$" <-> pprint x

instance PPrint SymConst where
  pprintTidy _ (SL x) = doubleQuotes $ text $ T.unpack x

-- | Wrap the enclosed 'Doc' in parentheses only if the condition holds.
parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

-- NOTE: The following Expr and Pred printers use pprintPrec to print
-- expressions with minimal parenthesization. The precedence rules are somewhat
-- fragile, and it would be nice to have them directly tied to the parser, but
-- the general idea is (from lowest to highest precedence):
--
-- 1 - if-then-else
-- 2 - => and <=>
-- 3 - && and ||
-- 4 - ==, !=, <, <=, >, >=
-- 5 - mod
-- 6 - + and -
-- 7 - * and /
-- 8 - function application
--
-- Each printer `p` checks whether the precedence of the context is greater than
-- its own precedence. If so, the printer wraps itself in parentheses. Then it
-- sets the contextual precedence for recursive printer invocations to
-- (prec p + 1).

opPrec :: Bop -> Int
opPrec Mod    = 5
opPrec Plus   = 6
opPrec Minus  = 6
opPrec Times  = 7
opPrec RTimes = 7
opPrec Div    = 7
opPrec RDiv   = 7

instance (IsListConName s, Eq s, Fixpoint s, PPrint s, Ord s) => PPrint (Expr s) where
  pprintPrec _ k (ESym c)        = pprintTidy k c
  pprintPrec _ k (ECon c)        = pprintTidy k c
  pprintPrec _ k (EVar s)        = pprintTidy k s
  -- pprintPrec _ (EBot)          = text "_|_"
  pprintPrec z k (ENeg e)        = parensIf (z > zn) $
                                   "-" <-> pprintPrec (zn + 1) k e
    where zn = 2
  pprintPrec z k (EApp f es)     = parensIf (z > za) $
                                   pprintPrec za k f <+> pprintPrec (za+1) k es
    where za = 8
  pprintPrec z k (EBin o e1 e2)  = parensIf (z > zo) $
                                   pprintPrec (zo+1) k e1 <+>
                                   pprintTidy k o         <+>
                                   pprintPrec (zo+1) k e2
    where zo = opPrec o
  pprintPrec z k (EIte p e1 e2)  = parensIf (z > zi) $
                                   "if"   <+> pprintPrec (zi+1) k p  <+>
                                   "then" <+> pprintPrec (zi+1) k e1 <+>
                                   "else" <+> pprintPrec (zi+1) k e2
    where zi = 1

  -- RJ: DO NOT DELETE!
  --  pprintPrec _ k (ECst e so)     = parens $ pprint e <+> ":" <+> {- const (text "...") -} (pprintTidy k so)
  pprintPrec z k (ECst e _)      = pprintPrec z k e
  pprintPrec _ _ PTrue           = trueD
  pprintPrec _ _ PFalse          = falseD
  pprintPrec z k (PNot p)        = parensIf (z > zn) $
                                   "not" <+> pprintPrec (zn+1) k p
    where zn = 8
  pprintPrec z k (PImp p1 p2)    = parensIf (z > zi) $
                                   (pprintPrec (zi+1) k p1) <+>
                                   "=>"                     <+>
                                   (pprintPrec (zi+1) k p2)
    where zi = 2
  pprintPrec z k (PIff p1 p2)    = parensIf (z > zi) $
                                   (pprintPrec (zi+1) k p1) <+>
                                   "<=>"                    <+>
                                   (pprintPrec (zi+1) k p2)
    where zi = 2
  pprintPrec z k (PAnd ps)       = parensIf (z > za) $
                                   pprintBin (za + 1) k trueD andD ps
    where za = 3
  pprintPrec z k (POr  ps)       = parensIf (z > zo) $
                                   pprintBin (zo + 1) k falseD orD ps
    where zo = 3
  pprintPrec z k (PAtom r e1 e2) = parensIf (z > za) $
                                   pprintPrec (za+1) k e1 <+>
                                   pprintTidy k r         <+>
                                   pprintPrec (za+1) k e2
    where za = 4
  pprintPrec _ k (PAll xts p)    = pprintQuant k "forall" xts p
  pprintPrec _ k (PExist xts p)  = pprintQuant k "exists" xts p
  pprintPrec _ k (ELam (x,t) e)  = "lam" <+> toFix x <+> ":" <+> toFix t <+> text "." <+> pprintTidy k e
  pprintPrec _ k (ECoerc a t e)  = parens $ "coerce" <+> toFix a <+> "~" <+> toFix t <+> text "in" <+> pprintTidy k e
  pprintPrec _ _ p@(PKVar {})    = toFix p
  pprintPrec _ _ (ETApp e s)     = "ETApp" <+> toFix e <+> toFix s
  pprintPrec _ _ (ETAbs e s)     = "ETAbs" <+> toFix e <+> toFix s
  pprintPrec z k (PGrad x _ _ e) = pprintPrec z k e <+> "&&" <+> toFix x -- "??"

pprintQuant :: (IsListConName s, Eq s, Fixpoint s, PPrint s, Ord s) => Tidy -> Doc -> [(Symbol s, Sort s)] -> Expr s -> Doc
pprintQuant k d xts p = (d <+> toFix xts)
                        $+$
                        ("  ." <+> pprintTidy k p)

trueD, falseD, andD, orD :: Doc
trueD  = "true"
falseD = "false"
andD   = "&&"
orD    = "||"

pprintBin :: (PPrint a) => Int -> Tidy -> Doc -> Doc -> [a] -> Doc
pprintBin _ _ b _ [] = b
pprintBin z k _ o xs = vIntersperse o $ pprintPrec z k <$> xs

vIntersperse :: Doc -> [Doc] -> Doc
vIntersperse _ []     = empty
vIntersperse _ [d]    = d
vIntersperse s (d:ds) = vcat (d : ((s <+>) <$> ds))

pprintReft :: (IsListConName s, Eq s, Fixpoint s, PPrint s, Ord s) => Tidy -> Reft s -> Doc
pprintReft k (Reft (_,ra)) = pprintBin z k trueD andD flat
  where
    flat = flattenRefas [ra]
    z    = if length flat > 1 then 3 else 0

------------------------------------------------------------------------
-- | Generalizing FixSymbol, Expression, Predicate into Classes -----------
------------------------------------------------------------------------

-- | Values that can be viewed as Constants

-- | Values that can be viewed as Expressions

class Expression s a where
  expr   :: a -> Expr s

-- | Values that can be viewed as Predicates

class Predicate s a where
  prop   :: a -> Expr s

instance Expression s (SortedReft s) where
  expr (RR _ r) = expr r

instance Expression s (Reft s) where
  expr (Reft(_, e)) = e

instance Expression s (Expr s) where
  expr = id

-- | The symbol may be an encoding of a SymConst.

instance Expression s FixSymbol where
  expr s = eVar s

instance Expression s (Symbol s) where
  expr s = EVar s

instance Expression s Text where
  expr = ESym . SL

instance Expression s Integer where
  expr = ECon . I

instance Expression s Int where
  expr = expr . toInteger

instance Predicate s FixSymbol where
  prop = eProp

instance Predicate s (Expr s) where
  prop = id

instance Predicate s Bool where
  prop True  = PTrue
  prop False = PFalse

instance Expression s a => Expression s (Located a) where
  expr   = expr . val

eVar ::  (Expression s a, FixSymbolic a) => a -> Expr s
eVar = EVar . FS . symbol

eProp :: (Expression s a, FixSymbolic a) => a -> Expr s
eProp = mkProp . eVar

isSingletonExpr :: (Eq s) => Symbol s -> Expr s -> Maybe (Expr s)
isSingletonExpr v (PAtom r e1 e2)
  | e1 == EVar v && isEq r = Just e2
  | e2 == EVar v && isEq r = Just e1
isSingletonExpr v (PIff e1 e2) 
  | e1 == EVar v           = Just e2
  | e2 == EVar v           = Just e1
isSingletonExpr _ _        = Nothing

pAnd, pOr     :: (IsListConName s, Ord s, Eq s, Fixpoint s) => ListNE (Pred s) -> Pred s
pAnd          = simplify . PAnd
pOr           = simplify . POr

(&.&) :: (IsListConName s, Eq s, Fixpoint s, Ord s) => Pred s -> Pred s -> Pred s
(&.&) p q = pAnd [p, q]

(|.|) :: (IsListConName s, Eq s, Fixpoint s, Ord s) => Pred s -> Pred s -> Pred s
(|.|) p q = pOr [p, q]

pIte :: (IsListConName s, Eq s, Fixpoint s, Ord s) => Pred s -> Expr s -> Expr s -> Expr s
pIte p1 p2 p3 = pAnd [p1 `PImp` p2, (PNot p1) `PImp` p3]

pExist :: [(Symbol s, Sort s)] -> Pred s -> Pred s
pExist []  p = p
pExist xts p = PExist xts p

mkProp :: Expr s -> Pred s
mkProp = id -- EApp (EVar propConName)

--------------------------------------------------------------------------------
-- | Predicates ----------------------------------------------------------------
--------------------------------------------------------------------------------

isSingletonReft :: (Eq s) => Reft s -> Maybe (Expr s)
isSingletonReft (Reft (v, ra)) = firstMaybe (isSingletonExpr v) $ conjuncts ra

relReft :: forall a s. (Expression s a) => Brel -> a -> Reft s
relReft r e   = Reft (vv_, PAtom r (eVar (vv_ @s))  (expr e))

exprReft, notExprReft, uexprReft ::  (Expression s a) => a -> Reft s
exprReft      = relReft Eq
notExprReft   = relReft Ne
uexprReft     = relReft Ueq

propReft      ::  forall s a. (Predicate s a) => a -> Reft s
propReft p    = Reft (vv_, PIff (eProp (vv_ @s)) (prop p))

predReft      :: (Predicate s a) => a -> Reft s
predReft p    = Reft (vv_, prop p)

reft :: Symbol s -> Expr s -> Reft s
reft v p = Reft (v, p)

mapPredReft :: (Expr s -> Expr s) -> Reft s -> Reft s
mapPredReft f (Reft (v, p)) = Reft (v, f p)

---------------------------------------------------------------
-- | Refinements ----------------------------------------------
---------------------------------------------------------------

isFunctionSortedReft :: SortedReft s -> Bool
isFunctionSortedReft = isJust . functionSort . sr_sort

isNonTrivial :: forall s r. Reftable s r => r -> Bool
isNonTrivial = not . isTauto @s @r

reftPred :: Reft s -> Expr s
reftPred (Reft (_, p)) = p

reftBind :: Reft s -> Symbol s
reftBind (Reft (x, _)) = x

------------------------------------------------------------
-- | Gradual Type Manipulation  ----------------------------
------------------------------------------------------------
pGAnds :: (IsListConName s, Fixpoint s, Eq s, Ord s) => [Expr s] -> Expr s
pGAnds = foldl pGAnd PTrue

pGAnd :: (IsListConName s, Fixpoint s, Eq s, Ord s) => Expr s -> Expr s -> Expr s
pGAnd (PGrad k su i p) q = PGrad k su i (pAnd [p, q])
pGAnd p (PGrad k su i q) = PGrad k su i (pAnd [p, q])
pGAnd p q              = pAnd [p,q]

------------------------------------------------------------
-- | Generally Useful Refinements --------------------------
------------------------------------------------------------

symbolReft    :: forall a s. (Expression s a, FixSymbolic a) => a -> Reft s
symbolReft    = (exprReft :: Expr s -> Reft s) . (eVar :: a -> Expr s)

usymbolReft   :: forall a s. (Expression s a, FixSymbolic a) => a -> Reft s
usymbolReft   = (uexprReft :: Expr s -> Reft s) . (eVar :: a -> Expr s)

vv_ :: Symbol s
vv_ = FS $ vv Nothing

trueSortedReft :: Sort s -> SortedReft s
trueSortedReft = (`RR` trueReft)

trueReft, falseReft :: Reft s
trueReft  = Reft (vv_, PTrue)
falseReft = Reft (vv_, PFalse)

flattenRefas :: [Expr s] -> [Expr s]
flattenRefas        = concatMap flatP
  where
    flatP (PAnd ps) = concatMap flatP ps
    flatP p         = [p]

conjuncts :: (Eq s) => Expr s -> [Expr s]
conjuncts (PAnd ps) = concatMap conjuncts ps
conjuncts p
  | isTautoPred p   = []
  | otherwise       = [p]


-------------------------------------------------------------------------
-- | TODO: This doesn't seem to merit a TC ------------------------------
-------------------------------------------------------------------------

class Falseable a where
  isFalse :: a -> Bool

instance Falseable (Expr s) where
  isFalse (PFalse) = True
  isFalse _        = False

instance Falseable (Reft s) where
  isFalse (Reft (_, ra)) = isFalse ra

-------------------------------------------------------------------------
-- | Class Predicates for Valid Refinements -----------------------------
-------------------------------------------------------------------------

class (Eq s, Hashable s) =>  Subable s a where
  syms   :: a -> [Symbol s]                   -- ^ free symbols of a
  substa :: (Symbol s -> Symbol s) -> a -> a
  -- substa f  = substf (EVar . f)

  substf :: (Symbol s -> Expr s) -> a -> a
  subst  :: Subst s -> a -> a
  subst1 :: a -> (Symbol s, Expr s) -> a
  subst1 y (x, e) = subst (Su $ M.fromList [(x,e)]) y

instance Subable s a => Subable s (Located a) where
  syms (Loc _ _ x)   = syms @s @a x
  substa f (Loc l l' x) = Loc l l' (substa @s @a f x)
  substf f (Loc l l' x) = Loc l l' (substf f x)
  subst su (Loc l l' x) = Loc l l' (subst su x)


class (Monoid r, Subable s r) => Reftable s r where
  isTauto :: r -> Bool
  ppTy    :: r -> Doc -> Doc

  top     :: r -> r
  top _   =  mempty

  bot     :: r -> r

  meet    :: r -> r -> r
  meet    = mappend

  toReft  :: r -> Reft s
  ofReft  :: Reft s -> r
  params  :: r -> [Symbol s]          -- ^ parameters for Reft, vv + others
