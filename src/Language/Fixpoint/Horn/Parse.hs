
{-# LANGUAGE DeriveFunctor #-}

module Language.Fixpoint.Horn.Parse (hornP) where 

import           Language.Fixpoint.Parse
import qualified Language.Fixpoint.Types        as F 
import qualified Language.Fixpoint.Horn.Types   as H 
import           Text.Parsec       hiding (State)
import qualified Data.HashMap.Strict            as M
import           Data.Hashable

-------------------------------------------------------------------------------
hornP :: (F.Fixpoint s, Ord s, Show s, Hashable s) => Parser s (H.Query s (), [String])
-------------------------------------------------------------------------------
hornP = do
  hThings <- many hThingP
  pure (mkQuery hThings, [ o | HOpt o <- hThings ])

mkQuery :: (Hashable s, Eq s) => [HThing s a] -> H.Query s a
mkQuery things = H.Query
  { H.qQuals =        [ q | HQual q <- things ] 
  , H.qVars  =        [ k | HVar  k <- things ] 
  , H.qCstr  = H.CAnd [ c | HCstr c <- things ] 
  , H.qCon   = M.fromList  [ (x,t) | HCon x t <- things]
  , H.qDis   = M.fromList  [ (x,t) | HDis x t <- things]
  }

-- | A @HThing@ describes the kinds of things we may see, in no particular order
--   in a .smt2 query file.

data HThing s a
  = HQual !(F.Qualifier s)
  | HVar  !(H.Var s a)
  | HCstr !(H.Cstr s a)
  
  -- for uninterpred functions and ADT constructors
  | HCon  (F.Symbol s) (F.Sort s)
  | HDis  (F.Symbol s) (F.Sort s)

  | HOpt !String
  deriving (Functor)

hThingP :: (Hashable s, Show s, Ord s, F.Fixpoint s, Eq s) => Parser s (HThing s ())
hThingP  = parens body 
  where 
    body =  HQual <$> (reserved "qualif"     *> hQualifierP)
        <|> HCstr <$> (reserved "constraint" *> hCstrP)
        <|> HVar  <$> (reserved "var"        *> hVarP)
        <|> HOpt  <$> (reserved "fixpoint"   *> stringLiteral)
        <|> HCon  <$> (reserved "constant"   *> symbolP) <*> sortP
        <|> HDis  <$> (reserved "distinct"   *> symbolP) <*> sortP

-------------------------------------------------------------------------------
hCstrP :: (F.Fixpoint s, Ord s, Show s, Hashable s) => Parser s (H.Cstr s ())
-------------------------------------------------------------------------------
hCstrP = parens body 
  where 
    body =  H.CAnd  <$> (reserved "and"    *> many1 hCstrP)
        <|> H.All   <$> (reserved "forall" *> hBindP)       <*> hCstrP 
        <|> H.Any   <$> (reserved "exists" *> hBindP)       <*> hCstrP 
        <|> H.Head  <$> hPredP                              <*> pure ()

hBindP :: (Hashable s, Show s, Ord s, F.Fixpoint s) => Parser s (H.Bind s)
hBindP   = parens $ do 
  (x, t) <- symSortP
  p      <- hPredP 
  return  $ H.Bind x t p
  
-------------------------------------------------------------------------------
hPredP :: (F.Fixpoint s, Ord s, Show s, Hashable s) => Parser s (H.Pred s)
-------------------------------------------------------------------------------
hPredP = parens body 
  where 
    body =  H.Var  <$> kvSymP                           <*> many1 symbolP
        <|> H.PAnd <$> (reserved "and" *> many1 hPredP)
        <|> H.Reft <$> predP 

kvSymP :: Parser s (F.Symbol s) 
kvSymP = char '$' *> symbolP 

-------------------------------------------------------------------------------
-- | Qualifiers
-------------------------------------------------------------------------------
hQualifierP :: (F.Fixpoint s, Ord s, Show s, Hashable s) => Parser s (F.Qualifier s)
hQualifierP = do
  pos    <- getPosition
  n      <- upperIdP
  params <- parens (many1 symSortP) 
  body   <- parens predP
  return  $ F.mkQual n (mkParam <$> params) body pos

mkParam :: (F.Symbol s, F.Sort s) -> F.QualParam s
mkParam (x, t) = F.QP x F.PatNone t

-------------------------------------------------------------------------------
-- | Horn Variables 
-------------------------------------------------------------------------------

hVarP :: (Eq s) => Parser s (H.Var s ())
hVarP = H.HVar <$> kvSymP <*> parens (many1 (parens sortP)) <*> pure ()

-------------------------------------------------------------------------------
-- | Helpers 
-------------------------------------------------------------------------------

symSortP :: (Eq s) => Parser s (F.Symbol s, F.Sort s)
symSortP = parens ((,) <$> symbolP <*> sortP)


