{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | This module contains the types defining an SMTLIB2 interface.

module Language.Fixpoint.Smt.Types (

    -- * Serialized Representation
    --    symbolBuilder

    -- * Commands
      Command  (..)

    -- * Responses
    , Response (..)

    -- * Typeclass for SMTLIB2 conversion
    , SMTLIB2 (..)
    , runSmt2

    -- * SMTLIB2 Process Context
    , Context (..)

    ) where

import           Language.Fixpoint.Types
import qualified Data.Text                as T
import qualified Data.Text.Lazy.Builder   as LT
import           Text.PrettyPrint.HughesPJ

import           System.IO                (Handle)
import           System.Process
-- import           Language.Fixpoint.Misc   (traceShow)

--------------------------------------------------------------------------------
-- | Types ---------------------------------------------------------------------
--------------------------------------------------------------------------------

-- symbolBuilder :: Symbol s -> LT.Builder
-- symbolBuilder = LT.fromText . symbolSafeText

-- | Commands issued to SMT engine
data Command s    = Push
                  | Pop
                  | CheckSat
                  | DeclData ![DataDecl s]
                  | Declare  !(Symbol s) [SmtSort s] !(SmtSort s)
                  | Define   !(Sort s)
                  | Assert   !(Maybe Int) !(Expr s)
                  | AssertAx !(Triggered (Expr s))
                  | Distinct [Expr s] -- {v:[Expr] | 2 <= len v}
                  | GetValue [Symbol s]
                  | CMany    [Command s]
                  deriving (Eq, Show)

instance (Eq s, PPrint s, Fixpoint s, Ord s) => PPrint (Command s) where
  pprintTidy _ = ppCmd

ppCmd :: (Eq s, PPrint s, Fixpoint s, Ord s) => Command s -> Doc
ppCmd Push             = text "Push"
ppCmd Pop              = text "Pop"
ppCmd CheckSat         = text "CheckSat"
ppCmd (DeclData d)     = text "Data" <+> pprint d
ppCmd (Declare x [] t) = text "Declare" <+> pprint x <+> text ":" <+> pprint t
ppCmd (Declare x ts t) = text "Declare" <+> pprint x <+> text ":" <+> parens (pprint ts) <+> pprint t 
ppCmd (Define {})   = text "Define ..."
ppCmd (Assert _ e)  = text "Assert" <+> pprint e
ppCmd (AssertAx _)  = text "AssertAxiom ..."
ppCmd (Distinct {}) = text "Distinct ..."
ppCmd (GetValue {}) = text "GetValue ..."
ppCmd (CMany {})    = text "CMany ..."

-- | Responses received from SMT engine
data Response s   = Ok
                  | Sat
                  | Unsat
                  | Unknown
                  | Values [(Symbol s, T.Text)]
                  | Error !T.Text
                  deriving (Eq, Show)

-- | Information about the external SMT process
data Context s = Ctx
  { ctxPid     :: !ProcessHandle
  , ctxCin     :: !Handle
  , ctxCout    :: !Handle
  , ctxLog     :: !(Maybe Handle)
  , ctxVerbose :: !Bool
  , ctxSymEnv  :: !(SymEnv s)
  }

--------------------------------------------------------------------------------
-- | AST Conversion: Types that can be serialized ------------------------------
--------------------------------------------------------------------------------

class SMTLIB2 s a where
  smt2 :: SymEnv s -> a -> LT.Builder

runSmt2 :: (SMTLIB2 s a) => SymEnv s -> a -> LT.Builder
runSmt2 = smt2
