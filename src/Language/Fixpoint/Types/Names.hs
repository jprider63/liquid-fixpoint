{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE StandaloneDeriving #-}


-- | This module contains Haskell variables representing globally visible names.
--   Rather than have strings floating around the system, all constant names
--   should be defined here, and the (exported) variables should be used and
--   manipulated elsewhere.

module Language.Fixpoint.Types.Names (

  -- * Symbols
    Symbol
  , Symbol' (..)
  , FixSymbol
  , FixSymbolic (..)
  , LocSymbol
  , LocFixSymbol
  , LocText
  , IsListConName (..)
  , dropLoc
  , symbolicString
  , liftFixFun
  , encode

  -- * Conversion to/from Text
  , symbolSafeText
  , symbolSafeString
  , symbolText
  , symbolString
  , symbolBuilder
  , buildMany

  -- Predicates
  , isPrefixOfSym
  , isSuffixOfSym
  , isNonSymbol
  , isLitSymbol
  , isTestSymbol
  -- , isCtorSymbol
  , isNontrivialVV
  , isDummy

  -- * Destructors
  , stripPrefix
  , stripSuffix 
  , consSym
  , unconsSym
  , dropSym
  , headSym
  , lengthSym

  -- * Transforms
  , nonSymbol
  , vvCon
  , tidySymbol

  -- * Widely used prefixes
  , anfPrefix
  , tempPrefix
  , vv
  , symChars

  -- * Creating Symbols
  , dummySymbol
  , intSymbol
  , tempSymbol
  , gradIntSymbol

  -- * Wrapping Symbols
  , litSymbol
  , testSymbol
  , renameSymbol
  , kArgSymbol
  , existSymbol
  , suffixSymbol
  , mappendSym 

  -- * Unwrapping Symbols
  , unLitSymbol

  -- * Hardwired global names
  , dummyName
  , preludeName
  , boolConName
  , funConName
  , listConName
  , listLConName
  , tupConName
  , setConName
  , mapConName
  , strConName
  , charConName
  , nilName
  , consName
  , vvName
  , size32Name
  , size64Name
  , bitVecName
  , bvAndName
  , bvOrName
  , propConName
  -- HKT , tyAppName
  , isPrim
  , prims
  , mulFuncName
  , divFuncName

  -- * Casting function names
  , setToIntName, bitVecToIntName, mapToIntName, boolToIntName, realToIntName, toIntName
  , setApplyName, bitVecApplyName, mapApplyName, boolApplyName, realApplyName, intApplyName
  , applyName
  , coerceName

  , lambdaName
  , lamArgSymbol
  , isLamArgSymbol

) where

import           Control.DeepSeq             (NFData (..))
import           Control.Arrow               (second)
import           Data.Char                   (ord)
import           Data.Maybe                  (fromMaybe)
import           Data.Monoid                 ((<>))
import           Data.Generics               (Data)
import           Data.Hashable               (Hashable (..))
import qualified Data.HashSet                as S
import           Data.Interned
import           Data.Interned.Internal.Text
import           Data.String                 (IsString(..))
import qualified Data.Text                   as T
import qualified Data.Text.Lazy.Builder      as Builder
import           Data.Binary                 (Binary (..))
import           Data.Typeable               (Typeable)
import           GHC.Generics                (Generic)
import           Text.PrettyPrint.HughesPJ   (text)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Types.Errors (panic)

---------------------------------------------------------------
-- | Symbols --------------------------------------------------
---------------------------------------------------------------

deriving instance Data     InternedText
deriving instance Typeable InternedText
deriving instance Generic  InternedText

{- type SafeText = {v: T.Text | IsSafe v} @-}
type SafeText = T.Text

-- | Invariant: a `SafeText` is made up of:
--
--     ['0'..'9'] ++ ['a'...'z'] ++ ['A'..'Z'] ++ '$'
--
--   If the original text has ANY other chars, it is represented as:
--
--     lq$i
--
--   where i is a unique integer (for each text)

data FixSymbol
  = S { _symbolId      :: !Id
      , symbolRaw     :: !T.Text
      , symbolEncoded :: !T.Text
      } deriving (Data, Typeable, Generic)


data Symbol' fs s
  = FS fs -- ^ Fixpoint generated symbol
  | AS s         -- ^ (Abstract) Symbol from source language
  deriving (Data, Typeable, Generic, Functor)

type Symbol = Symbol' FixSymbol

deriving instance (Eq s, Eq fs) => Eq (Symbol' fs s)
deriving instance (Ord s, Ord fs) => Ord (Symbol' fs s)


-- | transforming FixSymbol while leaving source symbol unchanged
liftFixFun :: (FixSymbol -> FixSymbol) -> Symbol s -> Symbol s
liftFixFun f (FS s) = FS (f s)
liftFixFun _ a = a

instance Loc s => Loc (LocSymbol s) where
  srcSpan (FS s) = srcSpan s
  srcSpan (AS s) = srcSpan s

instance (Show fs, Show s) => Show (Symbol' fs s) where
  show (FS s) = show s
  show (AS as) = show as

-- instance IsString (Symbol s) where
--   fromString = FS . fromString

instance Eq FixSymbol where
  S i _ _ == S j _ _ = i == j

instance Ord FixSymbol where
  -- compare (S i _ _) (S j _ _) = compare i j
  -- compare s1 s2 = compare (symbolString s1) (symbolString s2)
  compare s1 s2 = compare (symbolText s1) (symbolText s2)

instance Interned FixSymbol where
  type Uninterned FixSymbol = T.Text
  newtype Description FixSymbol = DT T.Text deriving (Eq)
  describe     = DT
  identify i t = S i t (encode t)
  cache        = sCache

instance Uninternable FixSymbol where
  unintern (S _ t _) = t

instance Hashable (Description FixSymbol) where
  hashWithSalt s (DT t) = hashWithSalt s t

instance Hashable FixSymbol where
  -- NOTE: hash based on original text rather than id
  hashWithSalt s (S _ t _) = hashWithSalt s t


instance (Hashable s, Hashable fs) => Hashable (Symbol' fs s)

instance NFData FixSymbol where
  rnf (S {}) = ()

instance (NFData fs, NFData s) => NFData (Symbol' fs s)

instance Binary FixSymbol where
  get = textSymbol <$> get
  put = put . symbolText


instance (Binary s, Binary fs) => Binary (Symbol' fs s)

sCache :: Cache FixSymbol
sCache = mkCache
{-# NOINLINE sCache #-}

instance IsString FixSymbol where
  fromString = textSymbol . T.pack

instance IsString (Symbol s) where
  fromString = FS . textSymbol . T.pack

instance Show FixSymbol where
  show = show . symbolRaw

mappendSym :: FixSymbol -> FixSymbol -> FixSymbol
mappendSym s1 s2 = textSymbol $ mappend s1' s2'
    where
      s1'        = symbolText s1
      s2'        = symbolText s2

instance PPrint FixSymbol where
  pprintTidy _ = text . symbolString

instance (PPrint s, PPrint fs) => PPrint (Symbol' fs s) where
  pprintTidy t (FS fs) = pprintTidy t fs
  pprintTidy t (AS as) = pprintTidy t as

instance Fixpoint T.Text where
  toFix = text . T.unpack

{- | [NOTE: SymbolText]
	Use `symbolSafeText` if you want it to machine-readable,
        but `symbolText`     if you want it to be human-readable.
 -}

instance Fixpoint FixSymbol where
  toFix = toFix . checkedText -- symbolSafeText

instance (Fixpoint fs, Fixpoint s) => Fixpoint (Symbol' fs s) where
  toFix (FS s) = toFix s
  toFix (AS as) = toFix as
  

checkedText :: FixSymbol -> T.Text
checkedText x
  | Just (c, t') <- T.uncons t
  , okHd c && T.all okChr t'   = t
  | otherwise                  = symbolSafeText x
  where
    t     = symbolText x
    okHd  = (`S.member` alphaChars)
    okChr = (`S.member` symChars)

---------------------------------------------------------------------------
-- | Located Symbols -----------------------------------------------------
---------------------------------------------------------------------------

type LocSymbol = Symbol' (Located FixSymbol)

type LocFixSymbol = Located FixSymbol

type LocText   = Located T.Text

-- YL: Maybe we need a comonad dependency
-- should be defined as extract
dropLoc :: LocSymbol s -> Symbol s
dropLoc (FS s) = FS $ val s
dropLoc (AS s) = AS s

isDummy :: (FixSymbolic a) => a -> Bool
isDummy a = isPrefixOfSym (symbol dummyName) (symbol a)

instance FixSymbolic a => FixSymbolic (Located a) where
  symbol = symbol . val

---------------------------------------------------------------------------
-- | Decoding Symbols -----------------------------------------------------
---------------------------------------------------------------------------

symbolText :: FixSymbol -> T.Text
symbolText = symbolRaw

symbolString :: FixSymbol -> String
symbolString = T.unpack . symbolText

symbolSafeText :: FixSymbol -> SafeText
symbolSafeText = symbolEncoded

symbolSafeString :: FixSymbol -> String
symbolSafeString = T.unpack . symbolSafeText

---------------------------------------------------------------------------
-- | Encoding Symbols -----------------------------------------------------
---------------------------------------------------------------------------

-- INVARIANT: All strings *must* be built from here

textSymbol :: T.Text -> FixSymbol
textSymbol = intern

encode :: T.Text -> SafeText
encode t
  | isFixKey t     = T.append "key$" t
  | otherwise      = encodeUnsafe t

isFixKey :: T.Text -> Bool
isFixKey x = S.member x keywords

encodeUnsafe :: T.Text -> T.Text
encodeUnsafe = joinChunks . splitChunks . prefixAlpha

prefixAlpha :: T.Text -> T.Text
prefixAlpha t
  | isAlpha0 t = t
  | otherwise  = T.append "fix$" t

isAlpha0 :: T.Text -> Bool
isAlpha0 t = case T.uncons t of
               Just (c, _) -> S.member c alphaChars
               Nothing     -> False

joinChunks :: (T.Text, [(Char, SafeText)]) -> SafeText
joinChunks (t, [] ) = t
joinChunks (t, cts) = T.concat $ padNull t : (tx <$> cts)
  where
    tx (c, ct)      = mconcat ["$", c2t c, "$", ct]
    c2t             = T.pack . show . ord

padNull :: T.Text -> T.Text
padNull t
  | T.null t  = "z$"
  | otherwise = t

splitChunks :: T.Text -> (T.Text, [(Char, SafeText)])
splitChunks t = (h, go tl)
  where
    (h, tl)   = T.break isUnsafeChar t
    go !ut    = case T.uncons ut of
                  Nothing       -> []
                  Just (c, ut') -> let (ct, utl) = T.break isUnsafeChar ut'
                                   in (c, ct) : go utl

isUnsafeChar :: Char -> Bool
isUnsafeChar = not . (`S.member` okSymChars)


keywords :: S.HashSet T.Text
keywords   = S.fromList [ "env"
                        , "id"
                        , "tag"
                        , "qualif"
                        , "constant"
                        , "cut"
                        , "bind"
                        , "constraint"
                        , "lhs"
                        , "rhs"
                        , "NaN"
                        , "min"
                        , "map"
                        ]

-- | RJ: We allow the extra 'unsafeChars' to allow parsing encoded symbols.
--   e.g. the raw string "This#is%$inval!d" may get encoded as "enc%12"
--   and serialized as such in the fq/bfq file. We want to allow the parser
--   to then be able to read the above back in.

alphaChars :: S.HashSet Char
alphaChars = S.fromList $ ['a' .. 'z'] ++ ['A' .. 'Z']

numChars :: S.HashSet Char
numChars = S.fromList ['0' .. '9']

safeChars :: S.HashSet Char
safeChars = alphaChars `mappend`
            numChars   `mappend`
            S.fromList ['_', '.']

symChars :: S.HashSet Char
symChars =  safeChars `mappend`
            S.fromList ['%', '#', '$', '\'']

okSymChars :: S.HashSet Char
okSymChars = safeChars

isPrefixOfSym :: FixSymbol -> FixSymbol -> Bool
isPrefixOfSym (symbolText -> p) (symbolText -> x) = p `T.isPrefixOf` x

isSuffixOfSym :: FixSymbol -> FixSymbol -> Bool
isSuffixOfSym (symbolText -> p) (symbolText -> x) = p `T.isSuffixOf` x


headSym :: FixSymbol -> Char
headSym (symbolText -> t) = T.head t

consSym :: Char -> FixSymbol -> FixSymbol
consSym c (symbolText -> s) = symbol $ T.cons c s

unconsSym :: FixSymbol -> Maybe (Char, FixSymbol)
unconsSym (symbolText -> s) = second symbol <$> T.uncons s

-- singletonSym :: Char -> FixSymbol -- Yuck
-- singletonSym = (`consSym` "")

lengthSym :: FixSymbol -> Int
lengthSym (symbolText -> t) = T.length t

dropSym :: Int -> FixSymbol -> FixSymbol
dropSym n (symbolText -> t) = symbol $ T.drop n t

stripPrefix :: FixSymbol -> FixSymbol -> Maybe FixSymbol
stripPrefix p x = symbol <$> T.stripPrefix (symbolText p) (symbolText x)

stripSuffix :: FixSymbol -> FixSymbol -> Maybe FixSymbol
stripSuffix p x = symbol <$> T.stripSuffix (symbolText p) (symbolText x)


--------------------------------------------------------------------------------
-- | Use this **EXCLUSIVELY** when you want to add stuff in front of a FixSymbol
--------------------------------------------------------------------------------
suffixSymbol :: FixSymbol -> FixSymbol -> FixSymbol
suffixSymbol  x y = x `mappendSym` symSepName `mappendSym` y

vv                  :: Maybe Integer -> FixSymbol
-- vv (Just i)         = symbol $ symbolSafeText vvName `T.snoc` symSepName `mappend` T.pack (show i)
vv (Just i)         = intSymbol vvName i
vv Nothing          = vvName

isNontrivialVV      :: FixSymbol -> Bool
isNontrivialVV      = not . (vv Nothing ==)

vvCon, dummySymbol :: FixSymbol
vvCon       = vvName `suffixSymbol` "F"
dummySymbol = dummyName

-- ctorSymbol :: FixSymbol -> FixSymbol
-- ctorSymbol s = ctorPrefix `mappendSym` s

-- isCtorSymbol :: FixSymbol -> Bool
-- isCtorSymbol = isPrefixOfSym ctorPrefix

-- | 'testSymbol c' creates the `is-c` symbol for the adt-constructor named 'c'.
testSymbol :: FixSymbol -> FixSymbol
testSymbol s = testPrefix `mappendSym` s

isTestSymbol :: FixSymbol -> Bool
isTestSymbol = isPrefixOfSym testPrefix

litSymbol :: FixSymbol -> FixSymbol
litSymbol s = litPrefix `mappendSym` s

isLitSymbol :: FixSymbol -> Bool
isLitSymbol = isPrefixOfSym litPrefix

unLitSymbol :: FixSymbol -> Maybe FixSymbol
unLitSymbol = stripPrefix litPrefix

intSymbol :: (Show a) => FixSymbol -> a -> FixSymbol
intSymbol x i = x `suffixSymbol` symbol (show i)

tempSymbol :: FixSymbol -> Integer -> FixSymbol
tempSymbol prefix = intSymbol (tempPrefix `mappendSym` prefix)

renameSymbol :: FixSymbol -> Int -> FixSymbol
renameSymbol prefix = intSymbol (renamePrefix `mappendSym` prefix)

kArgSymbol :: FixSymbol -> FixSymbol -> FixSymbol
kArgSymbol x k = (kArgPrefix `mappendSym` x) `suffixSymbol` k

existSymbol :: FixSymbol -> Integer -> FixSymbol
existSymbol prefix = intSymbol (existPrefix `mappendSym` prefix)

gradIntSymbol :: Integer -> FixSymbol
gradIntSymbol = intSymbol gradPrefix

tempPrefix, anfPrefix, renamePrefix, litPrefix, gradPrefix :: FixSymbol
tempPrefix   = "lq_tmp$"
anfPrefix    = "lq_anf$"
renamePrefix = "lq_rnm$"
litPrefix    = "lit$"
gradPrefix   = "grad$"

testPrefix  :: FixSymbol
testPrefix   = "is$"

-- ctorPrefix  :: FixSymbol
-- ctorPrefix   = "mk$"

kArgPrefix, existPrefix :: FixSymbol
kArgPrefix   = "lq_karg$"
existPrefix  = "lq_ext$"

-------------------------------------------------------------------------
tidySymbol :: FixSymbol -> FixSymbol
-------------------------------------------------------------------------
tidySymbol = unSuffixSymbol . unSuffixSymbol . unPrefixSymbol kArgPrefix

unPrefixSymbol :: FixSymbol -> FixSymbol -> FixSymbol
unPrefixSymbol p s = fromMaybe s (stripPrefix p s)

unSuffixSymbol :: FixSymbol -> FixSymbol
unSuffixSymbol s@(symbolText -> t)
  = maybe s symbol $ T.stripSuffix symSepName $ fst $ T.breakOnEnd symSepName t

-- takeWhileSym :: (Char -> Bool) -> FixSymbol -> FixSymbol
-- takeWhileSym p (symbolText -> t) = symbol $ T.takeWhile p t


nonSymbol :: FixSymbol
nonSymbol = ""

isNonSymbol :: FixSymbol -> Bool
isNonSymbol = (== nonSymbol)

------------------------------------------------------------------------------
-- | Values that can be viewed as Symbols
------------------------------------------------------------------------------

class FixSymbolic a where
  symbol :: a -> FixSymbol

symbolicString :: (FixSymbolic a) => a -> String
symbolicString = symbolString . symbol

instance (FixSymbolic fs) => FixSymbolic (Symbol' fs s) where
  symbol (FS s) = symbol s
  symbol _ = panic "Coercing Symbol s into FixSymbol! Potential loss of GHC Information!"


instance FixSymbolic T.Text where
  symbol = textSymbol

instance FixSymbolic String where
  symbol = symbol . T.pack

instance FixSymbolic FixSymbol where
  symbol = id

symbolBuilder :: (FixSymbolic a) => a -> Builder.Builder
symbolBuilder = Builder.fromText . symbolSafeText . symbol

{-# INLINE buildMany #-}
buildMany :: [Builder.Builder] -> Builder.Builder
buildMany []     = mempty
buildMany [b]    = b
buildMany (b:bs) = b <> mconcat [ " " <> b | b <- bs ]

----------------------------------------------------------------------------
--------------- Global Name Definitions ------------------------------------
----------------------------------------------------------------------------

lambdaName :: FixSymbol
lambdaName = "smt_lambda"

lamArgPrefix :: FixSymbol
lamArgPrefix = "lam_arg"

lamArgSymbol :: Int -> FixSymbol
lamArgSymbol = intSymbol lamArgPrefix

isLamArgSymbol :: FixSymbol -> Bool
isLamArgSymbol = isPrefixOfSym lamArgPrefix

setToIntName, bitVecToIntName, mapToIntName, realToIntName, toIntName :: FixSymbol
setToIntName    = "set_to_int"
bitVecToIntName = "bitvec_to_int"
mapToIntName    = "map_to_int"
realToIntName   = "real_to_int"
toIntName       = "cast_as_int"

boolToIntName :: (IsString a) => a
boolToIntName   = "bool_to_int"

setApplyName, bitVecApplyName, mapApplyName, boolApplyName, realApplyName, intApplyName :: Int -> FixSymbol
setApplyName    = intSymbol "set_apply_"
bitVecApplyName = intSymbol "bitvec_apply"
mapApplyName    = intSymbol "map_apply_"
boolApplyName   = intSymbol "bool_apply_"
realApplyName   = intSymbol "real_apply_"
intApplyName    = intSymbol "int_apply_"

applyName :: FixSymbol
applyName = "apply"

coerceName :: FixSymbol
coerceName = "coerce"

preludeName, dummyName, boolConName, funConName :: FixSymbol
preludeName  = "Prelude"
dummyName    = "LIQUID$dummy"
boolConName  = "Bool"
funConName   = "->"


listConName, listLConName, tupConName, propConName, _hpropConName, vvName, setConName, mapConName :: FixSymbol
listConName  = "[]"
listLConName = "List"
tupConName   = "Tuple"
setConName   = "Set_Set"
mapConName   = "Map_t"
vvName       = "VV"
propConName  = "Prop"
_hpropConName = "HProp"

strConName, charConName :: (IsString a) => a
strConName   = "Str"
charConName  = "Char"
-- symSepName   :: Char
-- symSepName   = '#' -- DO NOT EVER CHANGE THIS

symSepName   :: (IsString a) => a
symSepName   = "##"

nilName, consName, size32Name, size64Name, bitVecName, bvOrName, bvAndName :: FixSymbol
nilName      = "nil"
consName     = "cons"
size32Name   = "Size32"
size64Name   = "Size64"
bitVecName   = "BitVec"
bvOrName     = "bvor"
bvAndName    = "bvand"

-- HKT tyAppName :: FixSymbol
-- HKT tyAppName    = "LF-App"

mulFuncName, divFuncName :: FixSymbol
mulFuncName  = "Z3_OP_MUL"
divFuncName  = "Z3_OP_DIV"

isPrim :: FixSymbol -> Bool 
isPrim x = S.member x prims 

prims :: S.HashSet FixSymbol
prims = S.fromList 
  [ propConName
  , _hpropConName
  , vvName
  , "Pred"
  , "List"
  , "[]"
  , "bool"
  -- , "int"
  -- , "real"
  , setConName
  , charConName
  , "Set_sng"
  , "Set_cup"
  , "Set_cap"
  , "Set_dif"
  , "Set_emp"
  , "Set_empty"
  , "Set_mem"
  , "Set_sub"
  , mapConName
  , "Map_select"
  , "Map_store"
  , "Map_union"
  , "Map_default"
  , size32Name
  , size64Name
  , bitVecName
  , bvOrName
  , bvAndName
  , "FAppTy"
  , nilName
  , consName
  ]

-------------------------------------------------------------------------------
-- | Classes that need to be implemented by the source language symbol
-------------------------------------------------------------------------------


class IsListConName s where
  isListConName :: s -> Bool


instance IsListConName LocFixSymbol where
  isListConName x = c == listConName || c == listLConName --"List"
    where
      c           = val x

instance IsListConName s => IsListConName (LocSymbol s) where
  isListConName (FS s) = isListConName s
  isListConName (AS s) = isListConName s



{-
-------------------------------------------------------------------------------
-- | Memoized Decoding
-------------------------------------------------------------------------------

{-# NOINLINE symbolMemo #-}
symbolMemo :: IORef (M.HashMap Int T.Text)
symbolMemo = unsafePerformIO (newIORef M.empty)

{-# NOINLINE memoEncode #-}
memoEncode :: T.Text -> Int
memoEncode t = unsafePerformIO $
                 atomicModifyIORef symbolMemo $ \m ->
                    (M.insert i t m, i)
  where
    i        = internedTextId $ intern t

{-# NOINLINE memoDecode #-}
memoDecode :: Int -> T.Text
memoDecode i = unsafePerformIO $
                 safeLookup msg i <$> readIORef symbolMemo
               where
                 msg = "FixSymbol Decode Error: " ++ show i

-}
