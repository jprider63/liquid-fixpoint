{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DeriveGeneric         #-}

module Language.Fixpoint.Smt.Bitvector
       ( -- * Constructor
         Bv (..)

         -- * Sizes
       , BvSize (..)

         -- * Operators
       , BvOp (..)

         -- * BitVector Sort Constructor
       , mkSort

         -- * BitVector Expression Constructor
       , eOp

         -- * BitVector Type Constructor
       , bvTyCon

       ) where

import           Data.Generics           (Data)
import qualified Data.Text               as T
import           Data.Typeable           (Typeable)
import           GHC.Generics            (Generic)
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types

data Bv     = Bv !BvSize !String

data BvSize = S32   | S64
              deriving (Eq, Ord, Show, Data, Typeable, Generic)

data BvOp   = BvAnd | BvOr
              deriving (Eq, Ord, Show, Data, Typeable, Generic)

-- | Construct the bitvector `Sort` from its `BvSize`
mkSort :: (Eq s) => BvSize -> Sort s
mkSort s = fApp (fTyconSort bvTyCon) [ fTyconSort (sizeTyCon s) ]

bvTyCon :: (Eq s) =>  FTycon s
bvTyCon = symbolFTycon $ dummyLoc (FS bitVecName)

sizeTyCon    :: (Eq s) => BvSize -> FTycon s
sizeTyCon    = symbolFTycon . dummyLoc . sizeName

sizeName :: BvSize -> Symbol s
sizeName S32 = FS size32Name
sizeName S64 = FS size64Name

-- | Construct an `Expr` using a raw string, e.g. (Bv S32 "#x02000000")
instance (Eq s) =>  Expression s Bv where
  expr (Bv sz v) = ECon $ L (T.pack v) (mkSort sz)

-- | Apply some bitvector operator to a list of arguments
eOp :: BvOp -> [Expr s] -> Expr s
eOp b es = foldl EApp (EVar $ opName b) es

opName :: BvOp -> Symbol s
opName BvAnd = FS bvAndName
opName BvOr  = FS bvOrName


-- sizeSort     = (`FApp` [fObj $ dummyLoc $ symbol "obj"]) . sizeTC
-- s32TyCon     = symbolFTycon $ dummyLoc size32Name
-- s64TyCon     = symbolFTycon $ dummyLoc size64Name
