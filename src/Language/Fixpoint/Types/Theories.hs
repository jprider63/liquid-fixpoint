{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE DeriveDataTypeable         #-}

-- | This module contains the types defining an SMTLIB2 interface.

module Language.Fixpoint.Types.Theories (

    -- * Serialized Representation
      Raw

    -- * Theory FixSymbol
    , TheorySymbol (..)
    , Sem (..)

    -- * Theory Sorts
    , SmtSort (..)
    , sortSmtSort
    , isIntSmtSort

    -- * FixSymbol Environments
    , SymEnv (..)
    , symEnv
    , symEnvSort
    , symEnvTheory
    , insertSymEnv
    , insertsSymEnv
    , symbolAtName
    , symbolAtSmtName


    ) where


import           Data.Generics             (Data)
import           Data.Semigroup            (Semigroup (..))
import           Data.Typeable             (Typeable)
import           Data.Hashable
import           GHC.Generics              (Generic)
import           Control.DeepSeq
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Types.Environments
import           Language.Fixpoint.Types.Spans (Loc)

import           Text.PrettyPrint.HughesPJ.Compat
import qualified Data.List                as L 
import qualified Data.Text.Lazy           as LT
import qualified Data.Binary              as B
import qualified Data.HashMap.Strict      as M
import qualified Language.Fixpoint.Misc   as Misc 

--------------------------------------------------------------------------------
-- | 'Raw' is the low-level representation for SMT values
--------------------------------------------------------------------------------
type Raw          = LT.Text

--------------------------------------------------------------------------------
-- | 'SymEnv' is used to resolve the 'Sort' and 'Sem' of each 'FixSymbol'
--------------------------------------------------------------------------------
data SymEnv s = SymEnv
  { seSort    :: !(SEnv s (Sort s))              -- ^ Sorts of *all* defined symbols
  , seTheory  :: !(SEnv s (TheorySymbol s))      -- ^ Information about theory-specific Symbols
  , seData    :: !(SEnv s (DataDecl s))          -- ^ User-defined data-declarations
  , seLits    :: !(SEnv s (Sort s))              -- ^ Distinct Constant symbols
  , seAppls   :: !(M.HashMap (FuncSort s) Int) -- ^ Types at which `apply` was used;
                                           --   see [NOTE:apply-monomorphization]
  }
  deriving (Eq, Show, Data, Typeable, Generic)

{- type FuncSort = {v:Sort s | isFFunc v} @-}
type FuncSort s = (SmtSort s, SmtSort s)

instance (NFData s) => NFData   (SymEnv s)
instance (Hashable s, B.Binary s, Eq s) => B.Binary (SymEnv s)

instance (Eq s, Hashable s) => Semigroup (SymEnv s) where
  e1 <> e2 = SymEnv { seSort   = seSort   e1 <> seSort   e2
                    , seTheory = seTheory e1 <> seTheory e2
                    , seData   = seData   e1 <> seData   e2
                    , seLits   = seLits   e1 <> seLits   e2
                    , seAppls  = seAppls  e1 <> seAppls  e2
                    }

instance (Eq s, Hashable s) => Monoid (SymEnv s) where
  mempty        = SymEnv emptySEnv emptySEnv emptySEnv emptySEnv mempty
  mappend       = (<>)

symEnv :: (Loc s, IsListConName s, Hashable s, Eq s, Ord s) => SEnv s (Sort s) -> SEnv s (TheorySymbol s) -> [DataDecl s] -> SEnv s (Sort s) -> [Sort s] -> SymEnv s
symEnv xEnv fEnv ds ls ts = SymEnv xEnv' fEnv dEnv ls sortMap
  where
    xEnv'                 = unionSEnv xEnv wiredInEnv
    dEnv                  = fromListSEnv [(FS $ symbol d, d) | d <- ds]
    sortMap               = M.fromList (zip smts [0..])
    smts                  = funcSorts dEnv ts 

-- | These are "BUILT-in" polymorphic functions which are
--   UNININTERPRETED but POLYMORPHIC, hence need to go through
--   the apply-defunc stuff.

wiredInEnv ::(Eq s, Hashable s) => M.HashMap (Symbol s) (Sort s)
wiredInEnv = M.fromList [(FS toIntName, mkFFunc 1 [FVar 0, FInt])]


-- | 'smtSorts' attempts to compute a list of all the input-output sorts
--   at which applications occur. This is a gross hack; as during unfolding
--   we may create _new_ terms with wierd new sorts. Ideally, we MUST allow
--   for EXTENDING the apply-sorts with those newly created terms.
--   the solution is perhaps to *preface* each VC query of the form
--
--      push
--      assert p
--      check-sat
--      pop
--
--   with the declarations needed to make 'p' well-sorted under SMT, i.e.
--   change the above to
--
--      declare apply-sorts
--      push
--      assert p
--      check-sat
--      pop
--
--   such a strategy would NUKE the entire apply-sort machinery from the CODE base.
--   [TODO]: dynamic-apply-declaration

funcSorts :: (IsListConName s, Loc s, Hashable s, Ord s) => SEnv s (DataDecl s) -> [Sort s] -> [FuncSort s]
funcSorts dEnv ts = [ (t1, t2) | t1 <- smts, t2 <- smts]
  where
    smts         = Misc.sortNub $ concat [ [tx t1, tx t2] | FFunc t1 t2 <- ts]
    tx           = applySmtSort dEnv


symEnvTheory :: (Hashable s, Eq s) => Symbol s -> SymEnv s -> Maybe (TheorySymbol s)
symEnvTheory x env = lookupSEnv x (seTheory env)

symEnvSort :: (Hashable s, Eq s) => Symbol s -> SymEnv s -> Maybe (Sort s)
symEnvSort   x env = lookupSEnv x (seSort env)

insertSymEnv :: (Eq s, Hashable s) => Symbol s -> Sort s -> SymEnv s -> SymEnv s
insertSymEnv x t env = env { seSort = insertSEnv x t (seSort env) }

insertsSymEnv :: (Eq s, Hashable s) => SymEnv s -> [(Symbol s, Sort s)] -> SymEnv s
insertsSymEnv = L.foldl' (\env (x, s) -> insertSymEnv x s env) 

symbolAtName :: (Loc s, IsListConName s, Eq s, Hashable s, PPrint a, Fixpoint s) => Symbol s -> SymEnv s -> a -> Sort s -> Symbol s
symbolAtName mkSym env e = symbolAtSmtName mkSym env e . ffuncSort env

symbolAtSmtName :: (Hashable s, PPrint a, Eq s, Fixpoint s) => Symbol s -> SymEnv s -> a -> FuncSort s -> Symbol s
symbolAtSmtName mkSym env e = FS . intSymbol (symbol mkSym) . funcSortIndex env e

funcSortIndex :: (Hashable s, PPrint a, Eq s, Fixpoint s) => SymEnv s -> a -> FuncSort s -> Int
funcSortIndex env e z = M.lookupDefault err z (seAppls env)
  where
    err               = panic ("Unknown func-sort: " ++ showpp z ++ " for " ++ showpp e)

ffuncSort :: (IsListConName s, Loc s, Eq s, Hashable s) => SymEnv s -> Sort s -> FuncSort s
ffuncSort env t      = {- tracepp ("ffuncSort " ++ showpp (t1,t2)) -} (tx t1, tx t2)
  where
    tx               = applySmtSort (seData env) 
    (t1, t2)         = args t
    args (FFunc a b) = (a, b)
    args _           = (FInt, FInt)

applySmtSort :: (Loc s, IsListConName s, Hashable s, Eq s) => SEnv s (DataDecl s) -> Sort s -> SmtSort s
applySmtSort = sortSmtSort False

isIntSmtSort :: (Loc s, IsListConName s, Eq s, Hashable s) => SEnv s (DataDecl s) -> Sort s -> Bool
isIntSmtSort env s = SInt == applySmtSort env s

--------------------------------------------------------------------------------
-- | 'TheorySymbol' represents the information about each interpreted 'FixSymbol'
--------------------------------------------------------------------------------
data TheorySymbol s  = Thy
  { tsSym    :: !(Symbol s)          -- ^ name
  , tsRaw    :: !Raw             -- ^ serialized SMTLIB2 name
  , tsSort   :: !(Sort s)            -- ^ sort
  , tsInterp :: !Sem             -- ^ TRUE = defined (interpreted), FALSE = declared (uninterpreted)
  }
  deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance NFData Sem
instance (NFData s) => NFData (TheorySymbol s)
instance (B.Binary s) => B.Binary (TheorySymbol s)

instance PPrint Sem where
  pprintTidy _ = text . show

instance (IsListConName s, PPrint s, Eq s, Fixpoint s) => Fixpoint (TheorySymbol s) where
  toFix (Thy x _ t d) = text "TheorySymbol" <+> pprint (x, t) <+> parens (pprint d)

instance (IsListConName s, PPrint s, Eq s, Fixpoint s) => PPrint (TheorySymbol s) where
  pprintTidy k (Thy x _ t d) = text "TheorySymbol" <+> pprintTidy k (x, t) <+> parens (pprint d)

--------------------------------------------------------------------------------
-- | 'Sem' describes the SMT semantics for a given symbol
--------------------------------------------------------------------------------

data Sem
  = Uninterp      -- ^ for UDF: `len`, `height`, `append`
  | Ctor         -- ^ for ADT constructor and tests: `cons`, `nil`
  | Test          -- ^ for ADT tests : `is$cons`
  | Field         -- ^ for ADT field: `hd`, `tl`
  | Theory        -- ^ for theory ops: mem, cup, select
  deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance B.Binary Sem


--------------------------------------------------------------------------------
-- | A Refinement of 'Sort' that describes SMTLIB Sorts
--------------------------------------------------------------------------------
data SmtSort s
  = SInt
  | SBool
  | SReal
  | SString
  | SSet
  | SMap
  | SBitVec !Int
  | SVar    !Int
  | SData   !(FTycon s) ![SmtSort s]
  -- HKT | SApp            ![SmtSort s]           -- ^ Representing HKT
  deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance (Hashable s) => Hashable (SmtSort s)
instance (NFData s) => NFData   (SmtSort s)
instance (B.Binary s) => B.Binary (SmtSort s)

-- | The 'poly' parameter is True when we are *declaring* sorts,
--   and so we need to leave type variables be; it is False when
--   we are declaring variables etc., and there, we serialize them
--   using `Int` (though really, there SHOULD BE NO floating tyVars...
--   'smtSort True  msg t' serializes a sort 't' using type variables,
--   'smtSort False msg t' serializes a sort 't' using 'Int' instead of tyvars.

sortSmtSort :: (Loc s, IsListConName s, Hashable s, Eq s) => Bool -> SEnv s (DataDecl s) -> Sort s -> SmtSort s
sortSmtSort poly env t  = {- tracepp ("sortSmtSort s: " ++ showpp t) $ -} go . unAbs $ t
  where
    go (FFunc _ _)    = SInt
    go FInt           = SInt
    go FReal          = SReal
    go t
      | t == boolSort = SBool
      | isString t    = SString 
    go (FVar i)
      | poly          = SVar i
      | otherwise     = SInt
    go t              = fappSmtSort poly env ct ts where (ct:ts) = unFApp t

fappSmtSort :: (Loc s, IsListConName s, Hashable s, Eq s) => Bool -> SEnv s (DataDecl s) -> Sort s -> [Sort s] -> SmtSort s
fappSmtSort poly env = go
  where
-- HKT    go t@(FVar _) ts            = SApp (sortSmtSort s poly env <$> (t:ts))
    go (FTC c) _
      | setConName == symbol c  = SSet
    go (FTC c) _
      | mapConName == symbol c  = SMap
    go (FTC bv) [FTC s]
      | bitVecName == symbol bv
      , Just n <- sizeBv s      = SBitVec n
    go s []
      | isString s              = SString
    go (FTC c) ts
      | Just n <- tyArgs c env
      , let i = n - length ts   = SData c ((sortSmtSort poly env <$> ts) ++ pad i)
    go _ _                      = SInt

    pad i | poly                = []
          | otherwise           = replicate i SInt

tyArgs :: (FixSymbolic x, Hashable s, Eq s) => x -> SEnv s (DataDecl s) -> Maybe Int
tyArgs x env = ddVars <$> lookupSEnv (FS $ symbol x) env

instance (Fixpoint s) => PPrint (SmtSort s) where
  pprintTidy _ SInt         = text "Int"
  pprintTidy _ SBool        = text "Bool"
  pprintTidy _ SReal        = text "Real"
  pprintTidy _ SString      = text "Str"
  pprintTidy _ SSet         = text "Set"
  pprintTidy _ SMap         = text "Map"
  pprintTidy _ (SBitVec n)  = text "BitVec" <+> int n
  pprintTidy _ (SVar i)     = text "@" <-> int i
--  HKT pprintTidy k (SApp ts)    = ppParens k (pprintTidy k tyAppName) ts
  pprintTidy k (SData c ts) = ppParens k (pprintTidy k c)         ts

ppParens :: (PPrint d) => Tidy -> Doc -> [d] -> Doc
ppParens k d ds = parens $ Misc.intersperse (text "") (d : (pprintTidy k <$> ds))
