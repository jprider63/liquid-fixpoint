{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE PatternGuards      #-}

module Language.Fixpoint.Solver.Solution
        ( -- * Create and Update Solution
          init, update

          -- * Lookup Solution
        , lhsPred
        , noKvars

          -- * Debug
        , elimSolGraph
        , solutionGraph
        )
where

import           Control.Parallel.Strategies
import           Control.Arrow (second)
import qualified Data.HashSet                   as S
import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import           Data.Maybe                     (maybeToList, isNothing)
import           Data.Monoid                    ((<>))
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.PrettyPrint ()
import           Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.SortCheck          as So
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types              as F
import           Language.Fixpoint.Types.Constraints hiding (ws, bs)
import           Language.Fixpoint.Graph
import           Prelude                        hiding (init, lookup)

-- DEBUG
-- import Text.Printf (printf)
-- import           Debug.Trace (trace)

--------------------------------------------------------------------------------
-- | Expanded or Instantiated Qualifier ----------------------------------------
--------------------------------------------------------------------------------

-- mkJVar :: F.Expr -> QBind
-- mkJVar p = [F.EQL dummyQual p []]

-- dummyQual :: F.Qualifier
-- dummyQual = F.Q F.nonSymbol [] F.PFalse (F.dummyPos "")

--------------------------------------------------------------------------------
-- | Update Solution -----------------------------------------------------------
--------------------------------------------------------------------------------
update :: Solution -> [F.KVar] -> [(F.KVar, F.EQual)] -> (Bool, Solution)
-------------------------------------------------------------------------
update s ks kqs = {- tracepp msg -} (or bs, s')
  where
    kqss        = groupKs ks kqs
    (bs, s')    = folds update1 s kqss
    -- msg         = printf "ks = %s, s = %s" (showpp ks) (showpp s)

folds   :: (a -> b -> (c, a)) -> a -> [b] -> ([c], a)
folds f b = L.foldl' step ([], b)
  where
     step (cs, acc) x = (c:cs, x')
       where
         (c, x')      = f acc x

groupKs :: [F.KVar] -> [(F.KVar, F.EQual)] -> [(F.KVar, QBind)]
groupKs ks kqs = M.toList $ groupBase m0 kqs
  where
    m0         = M.fromList $ (,[]) <$> ks

update1 :: Solution -> (F.KVar, QBind) -> (Bool, Solution)
update1 s (k, qs) = (change, solInsert k qs s)
  where
    oldQs         = solLookup s k
    change        = length oldQs /= length qs

--------------------------------------------------------------------
-- | Initial Solution (from Qualifiers and WF constraints) ---------
--------------------------------------------------------------------
init :: F.SInfo a -> S.HashSet F.KVar -> Solution
--------------------------------------------------------------------
init si ks = F.solFromList keqs []
  where
    keqs   = map (refine si qs) ws `using` parList rdeepseq
    qs     = F.quals si
    ws     = [ w | (k, w) <- M.toList (F.ws si), k `S.member` ks]
--    ws     = M.elems $ F.ws si

--------------------------------------------------------------------
refine :: F.SInfo a
       -> [F.Qualifier]
       -> F.WfC a
       -> (F.KVar, QBind)
--------------------------------------------------------------------
refine fi qs w = refineK env qs $ F.wrft w
  where
    env        = wenv <> genv
    wenv       = F.sr_sort <$> F.fromListSEnv (F.envCs (F.bs fi) (F.wenv w))
    genv       = F.lits fi

refineK :: F.SEnv F.Sort -> [F.Qualifier] -> (F.Symbol, F.Sort, F.KVar) -> (F.KVar, QBind)
refineK env qs (v, t, k) = {- tracepp msg -} (k, eqs')
   where
    eqs                  = instK env v t qs
    eqs'                 = filter (okInst env v t) eqs
    -- msg                  = printf "refineK: k = %s, eqs = %s" (showpp k) (showpp eqs)

--------------------------------------------------------------------
instK :: F.SEnv F.Sort
      -> F.Symbol
      -> F.Sort
      -> [F.Qualifier]
      -> QBind
--------------------------------------------------------------------
instK env v t = unique . concatMap (instKQ env v t)
  where
    unique = L.nubBy ((. F.eqPred) . (==) . F.eqPred)

instKQ :: F.SEnv F.Sort
       -> F.Symbol
       -> F.Sort
       -> F.Qualifier
       -> QBind
instKQ env v t q
  = do (su0, v0) <- candidates senv [(t, [v])] qt
       xs        <- match senv tyss [v0] (So.apply su0 <$> qts)
       return     $ F.eQual q (reverse xs)
    where
       qt : qts   = snd <$> F.q_params q
       tyss       = instCands env
       senv       = (`F.lookupSEnvWithDistance` env)

instCands :: F.SEnv F.Sort -> [(F.Sort, [F.Symbol])]
instCands env = filter isOk tyss
  where
    tyss      = groupList [(t, x) | (x, t) <- xts]
    isOk      = isNothing . F.functionSort . fst
    xts       = F.toListSEnv env

match :: So.Env -> [(F.Sort, [F.Symbol])] -> [F.Symbol] -> [F.Sort] -> [[F.Symbol]]
match env tyss xs (t : ts)
  = do (su, x) <- candidates env tyss t
       match env tyss (x : xs) (So.apply su <$> ts)
match _   _   xs []
  = return xs

--------------------------------------------------------------------------------
candidates :: So.Env -> [(F.Sort, [F.Symbol])] -> F.Sort -> [(So.TVSubst, F.Symbol)]
--------------------------------------------------------------------------------
candidates env tyss tx
  = [(su, y) | (t, ys) <- tyss
             , su      <- maybeToList $ So.unifyFast mono env tx t
             , y       <- ys                                   ]
  where
    mono = So.isMono tx

-----------------------------------------------------------------------
okInst :: F.SEnv F.Sort -> F.Symbol -> F.Sort -> F.EQual -> Bool
-----------------------------------------------------------------------
okInst env v t eq = isNothing tc
  where
    sr            = F.RR t (F.Reft (v, p))
    p             = F.eqPred eq
    tc            = So.checkSorted env sr


--------------------------------------------------------------------------------
-- | Predicate corresponding to LHS of constraint in current solution
--------------------------------------------------------------------------------
lhsPred :: F.SolEnv -> F.Solution -> F.SimpC a -> F.Expr
--------------------------------------------------------------------------------
lhsPred be s c = {- F.tracepp msg $ -} fst $ apply g s bs
  where
    g          = (ci, be, bs)
    bs         = F.senv c
    ci         = sid c
    -- msg        = "LhsPred for id = " ++ show (sid c)

type Cid         = Maybe Integer
type CombinedEnv = (Cid, F.SolEnv, F.IBindEnv)
type ExprInfo    = (F.Expr, KInfo)
type KVSub       = (F.KVar, F.Subst)

apply :: CombinedEnv -> Solution -> F.IBindEnv -> ExprInfo
apply g s bs  = (F.pAnd (pks : ps), kI)
  where
    (pks, kI) = applyKVars g s ks
    (ks, ps)  = mapEither exprKind es
    es        = concatMap (bindExprs g) (F.elemsIBindEnv bs)

exprKind :: F.Expr -> Either (F.KVar, F.Subst) F.Expr
exprKind (F.PKVar k su) = Left  (k, su)
exprKind p              = Right p

bindExprs :: CombinedEnv -> F.BindId -> [F.Expr]
bindExprs (_,be,_) i = [p `F.subst1` (v, F.eVar x) | F.Reft (v, p) <- rs ]
  where
    (x, sr)          = F.lookupBindEnv i (F.soeBinds be)
    rs               = F.reftConjuncts $ F.sr_reft sr


applyKVars :: CombinedEnv -> Solution -> [KVSub] -> ExprInfo
applyKVars g s = mrExprInfos (applyPack g s) F.pAnd mconcat . packKVars g

applyPack :: CombinedEnv -> Solution -> [KVSub] -> ExprInfo
applyPack g s kvs = case packable g s kvs of
  Nothing       -> applyKVars' g s kvs
  Just (p, kcs) -> applyPackCubes g s p kcs



packKVars :: CombinedEnv -> [KVSub] -> [[KVSub]]
packKVars = error "TODO:packKVars"

packable :: CombinedEnv -> Solution -> [KVSub] -> Maybe (F.Expr, [(KVSub, F.Cube)])
packable _g _s _kvs = error "TODO:packable"
-- applyKVars' g s = mrExprInfos (applyKVar g s) F.pAnd mconcat

applyPackCubes :: CombinedEnv -> Solution -> F.Expr -> [(KVSub, F.Cube)] -> ExprInfo
applyPackCubes g s p kcs = mrExprInfos (applyPackCube g s bs'') ppAnd mconcat kcs
  where
    ppAnd ps             = F.pAnd (p:ps)
    bs''                 = foldr1 F.intersectionIBindEnv bss
    bss                  = [ F.cuBinds c | (_, c) <- kcs ]

applyPackCube:: CombinedEnv -> Solution -> F.IBindEnv -> (KVSub, F.Cube) -> ExprInfo
applyPackCube g s bs'' kc = cubePredExc g s k su c bs'
  where
    ((k, su), c)          = kc
    bs'                   = F.diffIBindEnv bs bs''
    bs                    = F.cuBinds c

applyKVars' :: CombinedEnv -> Solution -> [KVSub] -> ExprInfo
applyKVars' g s = mrExprInfos (applyKVar g s) F.pAnd mconcat

applyKVar :: CombinedEnv -> Solution -> KVSub -> ExprInfo
applyKVar g s (k, su)
  | Just cs  <- M.lookup k (F.sHyp s)
  = hypPred g s k su cs
  | Just eqs <- M.lookup k (F.sMap s)
  = qBindPred su eqs -- TODO: don't initialize kvars that have a hyp solution
  | otherwise
  = errorstar $ "Unknown kvar: " ++ show k

hypPred :: CombinedEnv -> Solution -> F.KVar -> F.Subst -> F.Hyp  -> ExprInfo
hypPred g s k su = mrExprInfos (cubePred g s k su) F.pOr mconcatPlus


{- | `cubePred g s k su c` returns the predicate for

        (k . su)

      defined by using cube

        c := [b1,...,bn] |- (k . su')

      in the binder environment `g`.

        bs' := the subset of "extra" binders in [b1...bn] that are *not* in `g`
        p'  := the predicate corresponding to the "extra" binders

 -}

cubePred :: CombinedEnv -> Solution -> F.KVar -> F.Subst -> F.Cube -> ExprInfo
cubePred g s k su c = cubePredExc g s k su c bs'
  where
    bs'             = delCEnv bs g
    bs              = F.cuBinds c

-- | A variant of @cubePred@ which computes the predicate for the subset of
--   of binders cbs'' (which are the "delta" over those that are common over
--   a "pack" of kvars).

cubePredExc :: CombinedEnv -> Solution -> F.KVar -> F.Subst -> F.Cube -> F.IBindEnv -> ExprInfo
cubePredExc g s k su c bs' = (cubeP, extendKInfo kI (cuTag c))
  where
    cubeP           = F.PExist xts
                       $ F.pAnd [ psu
                                , F.PExist yts' $ F.pAnd [p', psu'] ]
    yts'            = symSorts g bs'
    g'              = addCEnv  g bs
    (p', kI)        = apply g' s bs'
    (_  , psu')     = substElim g' k su'
    (xts, psu)      = substElim g  k su
    su'             = F.cuSubst c
    bs              = F.cuBinds c

-- TODO: SUPER SLOW! Decorate all substitutions with Sorts in a SINGLE pass.

{- | @substElim@ returns the binders that must be existentially quantified,
     and the equality predicate relating the kvar-"parameters" and their
     actual values. i.e. given

        K[x1 := e1]...[xn := en]

     where e1 ... en have types t1 ... tn
     we want to quantify out

       x1:t1 ... xn:tn

     and generate the equality predicate && [x1 ~~ e1, ... , xn ~~ en]
     we use ~~ because the param and value may have different sorts, see:

        tests/pos/kvar-param-poly-00.hs

     Finally, we filter out binders if they are
     1. "free" in e1...en i.e. in the outer environment.
        (Hmm, that shouldn't happen...?)
     2. are binders corresponding to sorts (e.g. `a : num`, currently used
        to hack typeclasses current.)
 -}
substElim :: CombinedEnv -> F.KVar -> F.Subst -> ([(F.Symbol, F.Sort)], F.Pred)
substElim g _ (F.Su m) = (xts, p)
  where
    p      = F.pAnd [ F.PAtom F.Ueq (F.eVar x) e | (x, e, _) <- xets  ]
    xts    = [ (x, t)    | (x, _, t) <- xets, not (S.member x frees) ]
    xets   = [ (x, e, t) | (x, e)    <- xes, t <- sortOf e, not (isClass t) ]
    xes    = M.toList m
    env    = combinedSEnv g
    frees  = S.fromList (concatMap (F.syms . snd) xes)
    sortOf = maybeToList . So.checkSortExpr env

isClass :: F.Sort -> Bool
isClass F.FNum  = True
isClass F.FFrac = True
isClass _       = False

--badExpr :: CombinedEnv -> F.KVar -> F.Expr -> a
--badExpr g@(i,_,_) k e
  -- = errorstar $ "substSorts has a badExpr: "
              -- ++ show e
              -- ++ " in cid = "
              -- ++ show i
              -- ++ " for kvar " ++ show k
              -- ++ " in env \n"
              -- ++ show (combinedSEnv g)

-- substPred :: F.Subst -> F.Pred
-- substPred (F.Su m) = F.pAnd [ F.PAtom F.Eq (F.eVar x) e | (x, e) <- M.toList m]

combinedSEnv :: CombinedEnv -> F.SEnv F.Sort
combinedSEnv (_, se, bs) = F.sr_sort <$> F.fromListSEnv (F.envCs be bs)
  where
    be                   = F.soeBinds se

addCEnv :: CombinedEnv -> F.IBindEnv -> CombinedEnv
addCEnv (x, be, bs) bs' = (x, be, F.unionIBindEnv bs bs')

delCEnv :: F.IBindEnv -> CombinedEnv -> F.IBindEnv
delCEnv bs (_, _, bs')  = F.diffIBindEnv bs bs'

symSorts :: CombinedEnv -> F.IBindEnv -> [(F.Symbol, F.Sort)]
symSorts (_, se, _) bs = second F.sr_sort <$> F.envCs be  bs
  where
    be                 = F.soeBinds se

noKvars :: F.Expr -> Bool
noKvars = null . V.kvars

--------------------------------------------------------------------------------
qBindPred :: F.Subst -> QBind -> ExprInfo
--------------------------------------------------------------------------------
qBindPred su eqs = (F.subst su $ F.pAnd $ F.eqPred <$> eqs, mempty)

--------------------------------------------------------------------------------
-- | Build and print the graph of post eliminate solution, which has an edge
--   from k -> k' if k' appears directly inside the "solution" for k
--------------------------------------------------------------------------------
elimSolGraph :: Config -> F.Solution -> IO ()
elimSolGraph cfg s = writeGraph f (solutionGraph s)
  where
    f              = queryFile Dot cfg

--------------------------------------------------------------------------------
solutionGraph :: Solution -> KVGraph
--------------------------------------------------------------------------------
solutionGraph s = KVGraph [ (KVar k, KVar k, KVar <$> eqKvars eqs) | (k, eqs) <- kEqs ]
  where
     eqKvars    = sortNub . concatMap (V.kvars . F.eqPred)
     kEqs       = M.toList (F.sMap s)

--------------------------------------------------------------------------------
-- | Information about size of formula corresponding to an "eliminated" KVar.
--------------------------------------------------------------------------------
data KInfo = KI { kiTags  :: [Tag]
                , kiDepth :: !Int
                , kiCubes :: !Integer
                } deriving (Eq, Ord, Show)

instance Monoid KInfo where
  mempty         = KI [] 0 1
  mappend ki ki' = KI ts d s
    where
      ts         = appendTags (kiTags  ki) (kiTags  ki')
      d          = max        (kiDepth ki) (kiDepth ki')
      s          = (*)        (kiCubes ki) (kiCubes ki')

mplus :: KInfo -> KInfo -> KInfo
mplus ki ki' = (mappend ki ki') { kiCubes = kiCubes ki + kiCubes ki'}

mconcatPlus :: [KInfo] -> KInfo
mconcatPlus = foldr mplus mempty

appendTags :: [Tag] -> [Tag] -> [Tag]
appendTags ts ts' = sortNub (ts ++ ts')

extendKInfo :: KInfo -> F.Tag -> KInfo
extendKInfo ki t = ki { kiTags  = appendTags [t] (kiTags  ki)
                      , kiDepth = 1  +            kiDepth ki }

mrExprInfos :: (a -> ExprInfo) -> ([F.Expr] -> F.Expr) -> ([KInfo] -> KInfo) -> [a] -> ExprInfo
mrExprInfos mF erF irF xs = (erF es, irF is)
  where
    (es, is)              = unzip $ map mF xs
