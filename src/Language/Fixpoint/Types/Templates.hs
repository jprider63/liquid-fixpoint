{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Fixpoint.Types.Templates (

  anything, Templates, makeTemplates, 

  isEmptyTemplates, isAnyTemplates,

  matchesTemplates, filterUnMatched

  )where

import Language.Fixpoint.Types.Refinements
import Language.Fixpoint.Types.Names
import Language.Fixpoint.Types.PrettyPrint
import Text.PrettyPrint.HughesPJ.Compat

data Templates s
  = TAll 
  | TExprs [Template s] 
  deriving Show


type Template s = ([Symbol s], Expr s)


class HasTemplates s a where 
  filterUnMatched :: Templates s -> a -> a 


instance (IsListConName s, Eq s, Fixpoint s, Ord s) => HasTemplates s (Expr s) where
  filterUnMatched temps e = pAnd $ filter (not . matchesTemplates temps) $ conjuncts e 

instance (IsListConName s, Eq s, Fixpoint s, Ord s) => HasTemplates s (Reft s) where
  filterUnMatched temps (Reft (x,e)) = Reft (x, filterUnMatched temps e)

matchesTemplates :: (Fixpoint s, Eq s) => Templates s -> Expr s -> Bool 
matchesTemplates TAll _ = True 
matchesTemplates (TExprs ts) e = any (`matchesTemplate` e) ts

matchesTemplate :: (Fixpoint s, Eq s) => Template s -> Expr s -> Bool 
matchesTemplate (xs, t@(EVar x)) e
  = x `elem` xs || e == t  
matchesTemplate (xs, EApp t1 t2) (EApp e1 e2) 
  = matchesTemplate (xs, t1) e1 && matchesTemplate (xs, t2) e2 
matchesTemplate (xs, ENeg t) (ENeg e) 
  = matchesTemplate (xs, t) e
matchesTemplate (xs, EBin b t1 t2) (EBin b' e1 e2) 
  = b == b' && matchesTemplate (xs, t1) e1 && matchesTemplate (xs, t2) e2 
matchesTemplate (xs, EIte t1 t2 t3) (EIte e1 e2 e3) 
  = matchesTemplate (xs, t1) e1 && matchesTemplate (xs, t2) e2 && matchesTemplate (xs, t3) e3 
matchesTemplate (xs, ECst t s) (ECst e s') 
  = s == s' && matchesTemplate (xs, t) e
matchesTemplate (xs, ELam b t) (ELam b' e) 
  = b == b' && matchesTemplate (xs, t) e
matchesTemplate (xs, ETApp t s) (ETApp e s') 
  = s == s' && matchesTemplate (xs, t) e
matchesTemplate (xs, ETAbs t s) (ETAbs e s') 
  = s == s' && matchesTemplate (xs, t) e
matchesTemplate (xs, PNot t) (PNot e) 
  = matchesTemplate (xs, t) e
matchesTemplate (xs, PAnd ts) (PAnd es) 
  = and $ zipWith (\t e -> matchesTemplate (xs, t) e) ts es 
matchesTemplate (xs, POr ts) (POr es) 
  = and $ zipWith (\t e -> matchesTemplate (xs, t) e) ts es 
matchesTemplate (xs, PImp t1 t2) (PImp e1 e2) 
  = matchesTemplate (xs, t1) e1 && matchesTemplate (xs, t2) e2 
matchesTemplate (xs, PIff t1 t2) (PIff e1 e2) 
  = matchesTemplate (xs, t1) e1 && matchesTemplate (xs, t2) e2 
matchesTemplate (xs, PAtom b t1 t2) (PAtom b' e1 e2) 
  = b == b' && matchesTemplate (xs, t1) e1 && matchesTemplate (xs, t2) e2 
matchesTemplate (xs, PAll s t) (PAll s' e) 
  = s == s' && matchesTemplate (xs, t) e
matchesTemplate (xs, PExist s t) (PExist s' e) 
  = s == s' && matchesTemplate (xs, t) e
matchesTemplate (xs, PGrad s1 s2 s3 t) (PGrad s1' s2' s3' e) 
  = s1 == s1' && s2 == s2' && s3 == s3' && matchesTemplate (xs, t) e
matchesTemplate (xs, ECoerc s1 s2 t) (ECoerc s1' s2' e) 
  = s1 == s1' && s2 == s2' && matchesTemplate (xs, t) e
matchesTemplate (_, t) e 
  = t == e 



makeTemplates :: [([Symbol s], Expr s)] -> Templates s
makeTemplates = TExprs 


isEmptyTemplates, isAnyTemplates :: Templates s -> Bool 
isEmptyTemplates (TExprs []) = True 
isEmptyTemplates _           = False 

isAnyTemplates TAll = True 
isAnyTemplates _    = False 

anything :: Templates s
anything = TAll

instance Semigroup (Templates s) where 
  TAll <> _ = TAll
  _ <> TAll = TAll
  TExprs i1 <> TExprs i2 = TExprs (i1 ++ i2)

instance Monoid (Templates s) where 
  mempty = TExprs [] 

instance (IsListConName s, Show s, Eq s, Fixpoint s, Ord s) => PPrint (Templates s) where
  pprintTidy _ = text . show 
