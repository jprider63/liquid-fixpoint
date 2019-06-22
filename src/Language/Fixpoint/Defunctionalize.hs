{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE OverloadedStrings    #-}

--------------------------------------------------------------------------------
-- | `defunctionalize` traverses the query to:
--      1. "normalize" lambda terms by renaming binders,
--      2. generate alpha- and beta-equality axioms for
--   The lambdas and redexes found in the query.
--
--   NOTE: `defunctionalize` should happen **BEFORE**
--   `elaborate` as the latter converts all actual `EApp`
--   into the (uninterpreted) `smt_apply`.
--   We cannot elaborate prior to `defunc` as we need the
--   `EApp` and `ELam` to determine the lambdas and redexes.
--------------------------------------------------------------------------------

module Language.Fixpoint.Defunctionalize 
  ( defunctionalize
  , Defunc(..)
  , defuncAny
  ) where 

import qualified Data.HashMap.Strict as M
import           Data.Hashable
import           Control.Monad.State
import           Language.Fixpoint.Misc            (fM, secondM, mapSnd)
import           Language.Fixpoint.Solver.Sanitize (symbolEnv)
import           Language.Fixpoint.Types        hiding (allowHO)
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.Visitor   (mapMExpr)
-- import Debug.Trace (trace)

defunctionalize :: (Hashable s, PPrint s, Fixpoint s, Ord s, Show s, Fixpoint a) => Config -> SInfo s a -> SInfo s a
defunctionalize cfg si = evalState (defunc si) (makeInitDFState cfg si)

defuncAny :: (Eq s, Hashable s, Defunc s a) => Config -> SymEnv s -> a -> a
defuncAny cfg env e = evalState (defunc e) (makeDFState cfg env emptyIBindEnv)


---------------------------------------------------------------------------------------------
-- | Expressions defunctionalization --------------------------------------------------------
---------------------------------------------------------------------------------------------
txExpr :: (Show s, Fixpoint s, Ord s, Hashable s) => Expr s -> DF s (Expr s)
txExpr e = do
  hoFlag <- gets dfHO
  if hoFlag then defuncExpr e else return e

defuncExpr :: (Hashable s, Ord s, Fixpoint s, Show s) => Expr s -> DF s (Expr s)
defuncExpr = mapMExpr reBind
         >=> mapMExpr (fM normalizeLams)

reBind :: (Show s, Fixpoint s, Ord s, Hashable s) => Expr s -> DF s (Expr s)
reBind (ELam (x, s) e) = ((\y -> ELam (y, s) (subst1 e (x, EVar y))) <$> freshSym s)
reBind e               = return e
shiftLam :: (Show s, Fixpoint s, Ord s, Hashable s) => Int -> Symbol s -> Sort s -> Expr s -> Expr s
shiftLam i x t e = ELam (FS x_i, t) (e `subst1` (x, x_i_t))
  where
    x_i          = lamArgSymbol i
    x_i_t        = ECst (EVar (FS x_i)) t

-- normalize lambda arguments [TODO: example]

normalizeLams :: (Show s, Fixpoint s, Ord s, Hashable s) => Expr s -> Expr s
normalizeLams e = snd $ normalizeLamsFromTo 1 e

normalizeLamsFromTo :: (Hashable s, Ord s, Fixpoint s, Show s) => Int -> Expr s -> (Int, Expr s)
normalizeLamsFromTo i   = go
  where
    go (ELam (y, sy) e) = (i + 1, shiftLam i y sy e') where (i, e') = go e
                          -- let (i', e') = go e
                          --    y'       = lamArgSymbol i'  -- SHIFTLAM
                          -- in (i' + 1, ELam (y', sy) (e' `subst1` (y, EVar y')))
    go (EApp e1 e2)     = let (i1, e1') = go e1
                              (i2, e2') = go e2
                          in (max i1 i2, EApp e1' e2')
    go (ECst e s)       = mapSnd (`ECst` s) (go e)
    go (PAll bs e)      = mapSnd (PAll bs) (go e)
    go e                = (i, e)


--------------------------------------------------------------------------------
-- | Containers defunctionalization --------------------------------------------
--------------------------------------------------------------------------------

class Defunc s a | a -> s where
  defunc :: a -> DF s a

instance (PPrint s, Ord s, Fixpoint s, Show s, Hashable s, Eq s, Defunc s (c a), TaggedC s c a) => Defunc s (GInfo s c a) where
  defunc fi = do
    cm'    <- defunc $ cm    fi
    ws'    <- defunc $ ws    fi
    -- NOPROP setBinds $ mconcat ((senv <$> M.elems (cm fi)) ++ (wenv <$> M.elems (ws fi)))
    gLits' <- defunc $ gLits fi
    dLits' <- defunc $ dLits fi
    bs'    <- defunc $ bs    fi
    ass'   <- defunc $ asserts fi
    -- NOPROP quals' <- defunc $ quals fi
    return $ fi { cm      = cm'
                , ws      = ws'
                , gLits   = gLits'
                , dLits   = dLits'
                , bs      = bs'
                , asserts = ass'
                }

instance (Defunc s a) => Defunc s (Triggered a) where
  defunc (TR t e) = TR t <$> defunc e

instance (Show s, Fixpoint s, Ord s, Hashable s, Eq s) => Defunc s (SimpC s a) where
  defunc sc = do crhs' <- defunc $ _crhs sc
                 return $ sc {_crhs = crhs'}

instance (Show s, Fixpoint s, Ord s, Hashable s, Eq s) => Defunc s (WfC s a) where
  defunc wf@(WfC {}) = do
    let (x, t, k) = wrft wf
    t' <- defunc t
    return $ wf { wrft = (x, t', k) }
  defunc wf@(GWfC {}) = do
    let (x, t, k) = wrft wf
    t' <- defunc t
    e' <- defunc $ wexpr wf
    return $ wf { wrft = (x, t', k), wexpr = e' }

instance (Hashable s, Ord s, Fixpoint s, Show s, Eq s) => Defunc s (SortedReft s) where
  defunc (RR s r) = RR s <$> defunc r

instance (Show s, Fixpoint s, Ord s, Hashable s, Eq s) => Defunc s (Symbol s, SortedReft s) where
  defunc (x, sr) = (x,) <$> defunc sr

instance Defunc s (Symbol s, Sort s) where
  defunc (x, t) = (x,) <$> defunc t

instance (Show s, Fixpoint s, Ord s, Hashable s, Eq s) => Defunc s (Reft s) where
  defunc (Reft (x, e)) = Reft . (x,) <$> defunc e

instance (Hashable s, Ord s, Fixpoint s, Show s, Eq s) => Defunc s (Expr s) where
  defunc = txExpr

instance (Hashable s, Eq s, Defunc s a) => Defunc s (SEnv s a) where
  defunc = mapMSEnv defunc

instance (Hashable s, Ord s, Fixpoint s, Show s, Eq s) => Defunc s (BindEnv s) where
  defunc bs = do dfbs <- gets dfBEnv
                 let f (i, xs) = if i `memberIBindEnv` dfbs
                                       then  (i,) <$> defunc xs
                                       else  (i,) <$> matchSort xs
                 mapWithKeyMBindEnv f bs
   where
    -- The refinement cannot be elaborated thus defunc-ed because
    -- the bind does not appear in any contraint,
    -- thus unique binders does not perform properly
    -- The sort should be defunc, to ensure same sort on double binders
    matchSort (x, RR s r) = ((x,) . (`RR` r)) <$> defunc s

-- Sort defunctionalization [should be done by elaboration]
instance Defunc s (Sort s) where
  defunc = return

instance (Defunc s a) => Defunc s [a] where
  defunc = mapM defunc

instance (Defunc s a, Eq k, Hashable k) => Defunc s (M.HashMap k a) where
  defunc m = M.fromList <$> mapM (secondM defunc) (M.toList m)

type DF   s = State (DFST s)

data DFST s = DFST
  { dfFresh :: !Int
  , dfEnv   :: !(SymEnv s)
  , dfBEnv  :: !IBindEnv
  , dfHO    :: !Bool        -- ^ allow higher order thus defunctionalize
  , dfLams  :: ![Expr s]      -- ^ lambda expressions appearing in the expressions
  , dfRedex :: ![Expr s]      -- ^ redexes appearing in the expressions
  , dfBinds :: !(SEnv s (Sort s)) -- ^ sorts of new lambda-binders
  }

makeDFState :: (Hashable s, Eq s) => Config -> SymEnv s -> IBindEnv -> DFST s
makeDFState cfg env ibind = DFST
  { dfFresh = 0
  , dfEnv   = env
  , dfBEnv  = ibind
  , dfHO    = allowHO cfg  || defunction cfg
  -- INVARIANT: lambads and redexes are not defunctionalized
  , dfLams  = []
  , dfRedex = []
  , dfBinds = mempty
  }

makeInitDFState :: (Show s, Ord s, Fixpoint s, PPrint s, Hashable s) => Config -> SInfo s a -> DFST s
makeInitDFState cfg si
  = makeDFState cfg
      (symbolEnv cfg si)
      (mconcat ((senv <$> M.elems (cm si)) ++ (wenv <$> M.elems (ws si))))

--------------------------------------------------------------------------------
-- | Low level monad manipulation ----------------------------------------------
--------------------------------------------------------------------------------
freshSym :: (Hashable s, Eq s) => Sort s -> DF s (Symbol s)
freshSym t = do
  n    <- gets dfFresh
  let x = intSymbol "lambda_fun_" n
  modify $ \s -> s {dfFresh = n + 1, dfBinds = insertSEnv (FS x) t (dfBinds s)}
  return (FS x)


-- | getLams and getRedexes return the (previously seen) lambdas and redexes,
--   after "closing" them by quantifying out free vars corresponding to the
--   fresh binders in `dfBinds`.
