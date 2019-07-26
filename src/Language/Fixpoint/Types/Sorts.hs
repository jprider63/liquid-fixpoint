{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE MultiWayIf                 #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE StandaloneDeriving         #-}

-- | This module contains the data types, operations and
--   serialization functions for representing Fixpoint's
--   implication (i.e. subtyping) and well-formedness
--   constraints in Haskell. The actual constraint
--   solving is done by the `fixpoint.native` which
--   is written in Ocaml.

module Language.Fixpoint.Types.Sorts (

  -- * Fixpoint Types
    Sort (..)
  , Sub (..)
  , FTycon

  , sortFTycon
  , intFTyCon
  , boolFTyCon
  , realFTyCon
  , numFTyCon
  , strFTyCon
  , setFTyCon
  , mapFTyCon -- TODO: hide these

  , basicSorts, intSort, realSort, boolSort, strSort, funcSort
  , setSort, bitVecSort, mapSort, charSort

  , listFTyCon
  , isListTC
  , sizeBv
  , isFirstOrder
  , mappendFTC
  , fTyconSymbol, symbolFTycon, fTyconSort, symbolNumInfoFTyCon
  , fTyconSelfSort
  , fApp
  , fAppTC
  , fObj
  , unFApp
  , unAbs

  , sortSubst
  , functionSort
  , mkFFunc
  , bkFFunc

  , isNumeric, isReal, isString, isPolyInst

  -- * User-defined ADTs
  , DataField (..)
  , DataCtor (..)
  , DataDecl (..)
  , muSort

  -- * Embedding Source types as Sorts
  , TCEmb, TCArgs (..)
  , tceLookup 
  , tceFromList 
  , tceToList
  , tceMember 
  , tceInsert
  , tceInsertWith
  , tceMap
  ) where

import qualified Data.Binary as B
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)

import           Data.Semigroup            (Semigroup (..))
import           Data.Hashable
import           Data.List                 (foldl')
import           Control.DeepSeq
import           Data.Maybe                (fromMaybe)
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Misc
import           Text.PrettyPrint.HughesPJ.Compat
import qualified Data.HashMap.Strict       as M
import qualified Data.List                 as L

data FTycon s  = TC (LocSymbol s) TCInfo deriving (Data, Typeable, Generic)
deriving instance (Ord s) => Ord (FTycon s)
deriving instance (Show s) => Show (FTycon s)



-- instance Show (FTycon s) where
--   show (TC s _) = show (val s)

instance FixSymbolic (FTycon s) where
  symbol (TC s _) = symbol s

instance Eq s => Eq (FTycon s) where
  -- (TC s _) == (TC s' _) = val s == val s'
  (TC s _) == (TC s' _) = s == s'

data TCInfo = TCInfo { tc_isNum :: Bool, tc_isReal :: Bool, tc_isString :: Bool }
  deriving (Eq, Ord, Show, Data, Typeable, Generic)

mappendFTC :: FTycon s -> FTycon s -> FTycon s
mappendFTC (TC x i1) (TC _ i2) = TC x (mappend i1 i2)

instance Semigroup TCInfo where
 TCInfo i1 i2 i3 <> TCInfo i1' i2' i3' = TCInfo (i1 || i1') (i2 || i2') (i3 || i3')

instance Monoid TCInfo where
  mempty  = TCInfo defNumInfo defRealInfo defStrInfo
  mappend = (<>)

defTcInfo, numTcInfo, realTcInfo, strTcInfo :: TCInfo
defTcInfo  = TCInfo defNumInfo defRealInfo defStrInfo
numTcInfo  = TCInfo True       defRealInfo defStrInfo
realTcInfo = TCInfo True       True        defStrInfo
strTcInfo  = TCInfo defNumInfo defRealInfo True

defNumInfo, defRealInfo, defStrInfo :: Bool
defNumInfo  = False
defRealInfo = False
defStrInfo  = False

charFTyCon, intFTyCon, boolFTyCon, realFTyCon, funcFTyCon, numFTyCon :: FTycon s
strFTyCon, listFTyCon, mapFTyCon, setFTyCon :: FTycon s
intFTyCon  = TC (FS (dummyLoc "int"      )) numTcInfo
boolFTyCon = TC (FS (dummyLoc "bool"     )) defTcInfo
realFTyCon = TC (FS (dummyLoc "real"     )) realTcInfo
numFTyCon  = TC (FS (dummyLoc "num"      )) numTcInfo
funcFTyCon = TC (FS (dummyLoc "function" )) defTcInfo
strFTyCon  = TC (FS (dummyLoc strConName)) strTcInfo
listFTyCon = TC (FS (dummyLoc listConName)) defTcInfo
charFTyCon = TC (FS (dummyLoc charConName)) defTcInfo
setFTyCon  = TC (FS (dummyLoc setConName)) defTcInfo
mapFTyCon  = TC (FS (dummyLoc mapConName)) defTcInfo

-- isListConName :: (Eq s) => LocSymbol s -> Bool
-- isListConName x = c == FS listConName || c == FS listLConName --"List"
--   where
--     c           = val x

isListTC :: (Eq s, IsListConName s) => FTycon s -> Bool
isListTC (TC z _) = isListConName z

sizeBv :: (Eq s, Loc s) => FTycon s -> Maybe Int
sizeBv tc
  | FS (Loc _ _ fs) <- s
  = if | fs == size64Name -> Just 64
       | fs == size32Name -> Just 32
       | otherwise -> Nothing
  | otherwise       = Nothing
  where
    s               = fTyconSymbol tc

fTyconSymbol :: FTycon s -> LocSymbol s
fTyconSymbol (TC s _) = s

symbolNumInfoFTyCon :: (Eq s, Loc s) => LocSymbol s -> Bool -> Bool -> FTycon s
symbolNumInfoFTyCon c isNum isReal
  | FS s <- c
  , isListConName s
  = TC (FS $ atLoc c listConName) tcinfo
  | otherwise
  = TC c tcinfo
  where
    tcinfo = defTcInfo { tc_isNum = isNum, tc_isReal = isReal}


symbolFTycon :: (Loc s, Eq s) => LocSymbol s -> FTycon s
symbolFTycon c = symbolNumInfoFTyCon c defNumInfo defRealInfo

fApp :: Sort s -> [Sort s] -> Sort s
fApp = foldl' FApp

fAppTC :: Eq s => FTycon s -> [Sort s] -> Sort s
fAppTC = fApp . fTyconSort

fTyconSelfSort :: Eq s => FTycon s -> Int -> Sort s
fTyconSelfSort c n = fAppTC c [FVar i | i <- [0..(n - 1)]]

-- | fApp' (FApp (FApp "Map" key) val) ===> ["Map", key, val]
--   That is, `fApp'` is used to split a type application into
--   the FTyCon and its args.

unFApp :: Sort s -> ListNE (Sort s)
unFApp = go []
  where
    go acc (FApp t1 t2) = go (t2 : acc) t1
    go acc t            = t : acc

unAbs :: Sort s -> Sort s
unAbs (FAbs _ s) = unAbs s
unAbs s          = s

fObj :: Eq s => LocSymbol s -> Sort s
fObj = fTyconSort . (`TC` defTcInfo)

sortFTycon :: Sort s -> Maybe (FTycon s)
sortFTycon FInt    = Just intFTyCon
sortFTycon FReal   = Just realFTyCon
sortFTycon FNum    = Just numFTyCon
sortFTycon (FTC c) = Just c
sortFTycon _       = Nothing


functionSort :: Sort s -> Maybe ([Int], [Sort s], Sort s)
functionSort s
  | null is && null ss
  = Nothing
  | otherwise
  = Just (is, ss, r)
  where
    (is, ss, r)            = go [] [] s
    go vs ss (FAbs i t)    = go (i:vs) ss t
    go vs ss (FFunc s1 s2) = go vs (s1:ss) s2
    go vs ss t             = (reverse vs, reverse ss, t)

--------------------------------------------------------------------------------
-- | Sorts ---------------------------------------------------------------------
--------------------------------------------------------------------------------
data Sort s = FInt
            | FReal
            | FNum                 -- ^ numeric kind for Num tyvars
            | FFrac                -- ^ numeric kind for Fractional tyvars
            | FObj  !(Symbol s)        -- ^ uninterpreted type
            -- YL: may need to switch to symbol instead
            | FVar  !Int           -- ^ fixpoint type variable. 
            | FFunc !(Sort s) !(Sort s)    -- ^ function
            | FAbs  !Int !(Sort s)     -- ^ type-abstraction
            | FTC   !(FTycon s)
            | FApp  !(Sort s) !(Sort s)    -- ^ constructed type
              deriving (Eq, Ord, Show, Data, Typeable, Generic)

data DataField s = DField
  { dfName :: !(LocSymbol s)          -- ^ Field Name
  , dfSort :: !(Sort s)               -- ^ Field Sort
  } deriving (Eq, Ord, Show, Data, Typeable, Generic)

data DataCtor s = DCtor
  { dcName   :: !(LocSymbol s)        -- ^ Ctor Name
  , dcFields :: ![DataField s]      -- ^ Ctor Fields
  } deriving (Eq, Ord, Show, Data, Typeable, Generic)

data DataDecl s = DDecl
  { ddTyCon :: !(FTycon s)            -- ^ Name of defined datatype
  , ddVars  :: !Int               -- ^ Number of type variables
  , ddCtors :: [DataCtor s]         -- ^ Datatype Ctors
  } deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance FixSymbolic (DataDecl s) where
  symbol = symbol . ddTyCon

instance FixSymbolic (DataField s) where
  symbol = symbol . dfName

instance FixSymbolic (DataCtor s) where
  symbol = symbol . dcName


muSort  :: Eq s => [DataDecl s] -> [DataDecl s]
muSort dds = mapSortDataDecl tx <$> dds
  where
    selfs = [(fTyconSelfSort c n, fTyconSort c) | DDecl c n _ <- dds]
    tx t  = fromMaybe t $ L.lookup t selfs 

    mapSortDataDecl f  dd = dd { ddCtors  = mapSortDataCTor f  <$> ddCtors  dd }
    mapSortDataCTor f  ct = ct { dcFields = mapSortDataField f <$> dcFields ct }
    mapSortDataField f df = df { dfSort   = f $ dfSort df }

isFirstOrder, isFunction :: Sort s -> Bool
isFirstOrder (FFunc sx s) = not (isFunction sx) && isFirstOrder s
isFirstOrder (FAbs _ s)   = isFirstOrder s
isFirstOrder (FApp s1 s2) = (not $ isFunction s1) && (not $ isFunction s2)
isFirstOrder _            = True

isFunction (FAbs _ s)  = isFunction s
isFunction (FFunc _ _) = True
isFunction _           = False

isNumeric :: Sort s -> Bool
isNumeric FInt           = True
isNumeric (FApp s _)     = isNumeric s
isNumeric (FTC (TC _ i)) = tc_isNum i
isNumeric (FAbs _ s)     = isNumeric s
isNumeric _              = False

isReal :: Sort s -> Bool
isReal FReal          = True
isReal (FApp s _)     = isReal s
isReal (FTC (TC _ i)) = tc_isReal i
isReal (FAbs _ s)     = isReal s
isReal _              = False


isString :: (IsListConName s, Eq s) => Sort s -> Bool
isString (FApp l c)     = (isList l && isChar c) || isString l
isString (FTC (TC c i)) = (c == FS strConName || tc_isString i)
isString (FAbs _ s)     = isString s
isString _              = False

isList :: (IsListConName s, Eq s) => Sort s -> Bool
isList (FTC c) = isListTC c
isList _       = False

isChar :: Eq s => Sort s -> Bool
isChar (FTC c) = c == charFTyCon
isChar _       = False

{-@ FFunc :: Nat -> ListNE (Sort s) -> Sort s @-}

mkFFunc :: Int -> [Sort s] -> Sort s
mkFFunc i ss     = go [0..i-1] ss
  where
    go [] [s]    = s
    go [] (s:ss) = FFunc s $ go [] ss
    go (i:is) ss = FAbs  i $ go is ss
    go _ _       = error "cannot happen"

   -- foldl (flip FAbs) (foldl1 (flip FFunc) ss) [0..i-1]

bkFFunc :: Sort s -> Maybe (Int, [Sort s])
bkFFunc t    = (maximum (0 : as),) <$> bkFun t'
  where
    (as, t') = bkAbs t

bkAbs :: Sort s -> ([Int], Sort s)
bkAbs (FAbs i t) = (i:is, t') where (is, t') = bkAbs t
bkAbs t          = ([], t)

bkFun :: Sort s -> Maybe [Sort s]
bkFun z@(FFunc _ _)  = Just (go z)
  where
    go (FFunc t1 t2) = t1 : go t2
    go t             = [t]
bkFun _              = Nothing

isPolyInst :: Sort s -> Sort s -> Bool
isPolyInst s t = isPoly s && not (isPoly t)

isPoly :: Sort s -> Bool
isPoly (FAbs {}) = True
isPoly _         = False


instance Hashable s => Hashable (FTycon s) where
  hashWithSalt i (TC s _) = hashWithSalt i s

instance Loc s => Loc (FTycon s) where
  srcSpan (TC c _) = srcSpan c

instance Hashable s => Hashable (Sort s)

newtype Sub s = Sub [(Int, Sort s)] deriving (Generic)

instance (IsListConName s, Eq s, Fixpoint s) => Fixpoint (Sort s) where
  toFix = toFixSort

toFixSort :: (IsListConName s, Fixpoint s, Eq s) => Sort s -> Doc
toFixSort (FVar i)     = text "@" <-> parens (toFix i)
toFixSort FInt         = text "int"
toFixSort FReal        = text "real"
toFixSort FFrac        = text "frac"
toFixSort (FObj x)     = toFix x
toFixSort FNum         = text "num"
toFixSort t@(FAbs _ _) = toFixAbsApp t
toFixSort t@(FFunc _ _)= toFixAbsApp t
toFixSort (FTC c)      = toFix c
toFixSort t@(FApp _ _) = toFixFApp (unFApp t)

toFixAbsApp :: (IsListConName s, Fixpoint s, Eq s) => Sort s -> Doc
toFixAbsApp t = text "func" <-> parens (toFix n <+> text "," <+> toFix ts)
  where
    Just (vs, ss, s) = functionSort t
    n                = length vs
    ts               = ss ++ [s]

toFixFApp            :: (IsListConName s, Fixpoint s, Eq s) => ListNE (Sort s) -> Doc
toFixFApp [t]        = toFixSort t
toFixFApp [FTC c, t]
  | isListTC c       = brackets $ toFixSort t
toFixFApp ts         = parens $ intersperse (text "") (toFixSort <$> ts)

instance Fixpoint s => Fixpoint (FTycon s) where
  toFix (TC s _)       = toFix s

instance (IsListConName s, Eq s, Fixpoint s) => Fixpoint (DataField s) where
  toFix (DField x t) = toFix x <+> text ":" <+> toFix t

instance (IsListConName s, Eq s, Fixpoint s) => Fixpoint (DataCtor s) where
  toFix (DCtor x flds) = toFix x <+> braces (intersperse comma (toFix <$> flds))

instance (IsListConName s, Eq s, Fixpoint s) => Fixpoint (DataDecl s) where
  toFix (DDecl tc n ctors) = vcat ([header] ++ body ++ [footer])
    where
      header               = {- text "data" <+> -} toFix tc <+> toFix n <+> text "= ["
      body                 = [nest 2 (text "|" <+> toFix ct) | ct <- ctors]
      footer               = text "]"

instance Fixpoint s => PPrint (FTycon s) where
  pprintTidy _ = toFix

instance (IsListConName s, Eq s, Fixpoint s) => PPrint (DataField s) where
  pprintTidy _ = toFix

instance (IsListConName s, Eq s, Fixpoint s) => PPrint (DataCtor s) where
  pprintTidy _ = toFix

instance (IsListConName s, Eq s, Fixpoint s) => PPrint (DataDecl s) where
  pprintTidy _ = toFix

-------------------------------------------------------------------------
-- | Exported Basic Sorts -----------------------------------------------
-------------------------------------------------------------------------

boolSort, intSort, realSort, strSort, charSort, funcSort :: Eq s => Sort s
boolSort = fTyconSort boolFTyCon
charSort = fTyconSort charFTyCon
strSort  = fTyconSort strFTyCon
intSort  = fTyconSort intFTyCon
realSort = fTyconSort realFTyCon
funcSort = fTyconSort funcFTyCon

setSort :: Sort s -> Sort s
setSort    = FApp (FTC setFTyCon)

bitVecSort :: (Loc s, Eq s) => Sort s
bitVecSort = FApp (FTC $ symbolFTycon' (FS bitVecName)) (FTC $ symbolFTycon' (FS size32Name))

mapSort :: (Loc s, Eq s) => Sort s -> Sort s -> Sort s
mapSort = FApp . FApp (FTC (symbolFTycon' (FS mapConName)))

symbolFTycon' :: (Loc s) => Eq s => Symbol s -> FTycon s
symbolFTycon' = symbolFTycon . dummyLoc'
  where dummyLoc' (FS s) = FS $ dummyLoc s
        dummyLoc' (AS s) = AS s

fTyconSort :: Eq s => FTycon s -> Sort s
fTyconSort c
  | c == intFTyCon  = FInt
  | c == realFTyCon = FReal
  | c == numFTyCon  = FNum
  | otherwise       = FTC c

basicSorts :: Eq s => [Sort s]
basicSorts = [FInt, boolSort] 

------------------------------------------------------------------------
sortSubst                  :: (Eq s, Hashable s) => M.HashMap (Symbol s) (Sort s) -> Sort s -> Sort s
------------------------------------------------------------------------
sortSubst θ t@(FObj s)    = fromMaybe t (M.lookup s θ)
sortSubst θ (FFunc t1 t2) = FFunc (sortSubst θ t1) (sortSubst θ t2)
sortSubst θ (FApp t1 t2)  = FApp  (sortSubst θ t1) (sortSubst θ t2)
sortSubst θ (FAbs i t)    = FAbs i (sortSubst θ t)
sortSubst _  t            = t

-- instance (B.Binary a) => B.Binary (TCEmb s a) 
instance B.Binary TCArgs 
instance B.Binary s => B.Binary (FTycon s)
instance B.Binary TCInfo
instance B.Binary s => B.Binary (Sort s)
instance B.Binary s => B.Binary (DataField s)
instance B.Binary s => B.Binary (DataCtor s)
instance B.Binary s => B.Binary (DataDecl s)
instance B.Binary s => B.Binary (Sub s)

instance NFData (FTycon s) where
  rnf (TC x i) = x `seq` i `seq` ()

instance (NFData a, NFData s) => NFData (TCEmb s a) 
instance NFData TCArgs 
instance NFData TCInfo
instance NFData s => NFData (Sort s)
instance NFData s => NFData (DataField s)
instance NFData s => NFData (DataCtor s)
instance NFData s => NFData (DataDecl s)
instance NFData s => NFData (Sub s)

instance (Show s, Eq s) => Semigroup (Sort s) where
  t1 <> t2
    | t1 == mempty  = t2
    | t2 == mempty  = t1
    | t1 == t2      = t1
    | otherwise     = errorstar $ "mappend-sort: conflicting sorts t1 =" ++ show t1 ++ " t2 = " ++ show t2

instance (Show s, Eq s) => Monoid (Sort s) where
  mempty  = FObj (FS "any")
  mappend = (<>)

-------------------------------------------------------------------------------
-- | Embedding stuff as Sorts 
-------------------------------------------------------------------------------
newtype TCEmb s a = TCE (M.HashMap a (Sort s, TCArgs)) 
  deriving (Eq, Show, Data, Typeable, Generic) 

data TCArgs = WithArgs | NoArgs 
  deriving (Eq, Ord, Show, Data, Typeable, Generic) 

tceInsertWith :: (Eq a, Hashable a) => (Sort s -> Sort s -> Sort s) -> a -> Sort s -> TCArgs -> TCEmb s a -> TCEmb s a
tceInsertWith f k t a (TCE m) = TCE (M.insertWith ff k (t, a) m)
  where 
    ff (t1, a1) (t2, a2)      = (f t1 t2, a1 <> a2)

instance Semigroup TCArgs where 
  NoArgs <> NoArgs = NoArgs
  _      <> _      = WithArgs

instance Monoid TCArgs where 
  mempty = NoArgs 
  mappend = (<>)

instance PPrint TCArgs where 
  pprintTidy _ WithArgs = "*"
  pprintTidy _ NoArgs   = ""

tceInsert :: (Eq a, Hashable a) => a -> Sort s -> TCArgs -> TCEmb s a -> TCEmb s a
tceInsert k t a (TCE m) = TCE (M.insert k (t, a) m)

tceLookup :: (Eq a, Hashable a) => a -> TCEmb s a -> Maybe (Sort s, TCArgs) 
tceLookup k (TCE m) = M.lookup k m

instance (Eq a, Hashable a) => Semigroup (TCEmb s a) where 
  (TCE m1) <> (TCE m2) = TCE (m1 <> m2)

instance (Eq a, Hashable a) => Monoid (TCEmb s a) where 
  mempty  = TCE mempty 
  mappend = (<>)


tceMap :: (Eq b, Hashable b) => (a -> b) -> TCEmb s a -> TCEmb s b
tceMap f = tceFromList . fmap (mapFst f) . tceToList 

tceFromList :: (Eq a, Hashable a) => [(a, (Sort s, TCArgs))] -> TCEmb s a
tceFromList = TCE . M.fromList 

tceToList :: TCEmb s a -> [(a, (Sort s, TCArgs))]
tceToList (TCE m) = M.toList m

tceMember :: (Eq a, Hashable a) => a -> TCEmb s a -> Bool 
tceMember k (TCE m) = M.member k m
