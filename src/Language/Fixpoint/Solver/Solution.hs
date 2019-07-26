{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE PatternGuards     #-}

module Language.Fixpoint.Solver.Solution
  ( -- * Create Initial Solution
    init

    -- * Update Solution
  , Sol.update

  -- * Lookup Solution
  , lhsPred
  ) where

import           Control.Parallel.Strategies
import           Control.Arrow (second, (***))
import qualified Data.HashSet                   as S
import qualified Data.HashMap.Strict            as M
import           Data.Hashable
import qualified Data.List                      as L
import           Data.Maybe                     (fromMaybe, maybeToList, isNothing)
import           Data.Semigroup                 (Semigroup (..))
import           Language.Fixpoint.Types.PrettyPrint ()
import           Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.SortCheck          as So
import qualified Language.Fixpoint.Misc               as Misc
import           Language.Fixpoint.Types.Config
import qualified Language.Fixpoint.Types              as F
import           Language.Fixpoint.Types                 ((&.&))
import qualified Language.Fixpoint.Types.Solutions    as Sol
import           Language.Fixpoint.Types.Constraints  hiding (ws, bs)
import           Prelude                              hiding (init, lookup)
import           Language.Fixpoint.Solver.Sanitize

-- DEBUG
import Text.Printf (printf)
-- import           Debug.Trace


--------------------------------------------------------------------------------
-- | Initial Solution (from Qualifiers and WF constraints) ---------------------
--------------------------------------------------------------------------------
init :: (NFData s, Show s, Ord s, F.PPrint s, F.Fixpoint s, Hashable s, Eq s, F.Fixpoint a) => Config -> F.SInfo s a -> S.HashSet (F.KVar s) -> Sol.Solution s
--------------------------------------------------------------------------------
init cfg si ks = Sol.fromList senv mempty keqs [] mempty ebs xEnv
  where
    keqs       = map (refine si qs genv) ws `using` parList rdeepseq
    qs         = F.quals si
    ws         = [ w | (k, w) <- M.toList (F.ws si), not (isGWfc w) , k `S.member` ks]
    genv       = instConstants si
    senv       = symbolEnv cfg si
    ebs        = ebindInfo si
    xEnv       = F.fromListSEnv [ (x, (i, F.sr_sort sr)) | (i,x,sr) <- F.bindEnvToList (F.bs si)]

--------------------------------------------------------------------------------
refine :: (F.Fixpoint s, Ord s, F.PPrint s, Show s, Hashable s, Eq s) => F.SInfo s a -> [F.Qualifier s] -> F.SEnv s (F.Sort s) -> F.WfC s a -> (F.KVar s, Sol.QBind s)
refine fi qs genv w = refineK (allowHOquals fi) env qs $ F.wrft w
  where
    env             = wenv <> genv
    wenv            = F.sr_sort <$> F.fromListSEnv (F.envCs (F.bs fi) (F.wenv w))

instConstants :: (Hashable s, Eq s) => F.SInfo s a -> F.SEnv s (F.Sort s)
instConstants = F.fromListSEnv . filter notLit . F.toListSEnv . F.gLits
  where
    notLit    = not . F.isLitSymbol . F.symbol . fst


refineK :: (Show s, Hashable s, F.PPrint s, Ord s, F.Fixpoint s) => Bool -> F.SEnv s (F.Sort s) -> [F.Qualifier s] -> (F.Symbol s, F.Sort s, F.KVar s) -> (F.KVar s, Sol.QBind s)
refineK ho env qs (v, t, k) = F.notracepp _msg (k, eqs')
   where
    eqs                     = instK ho env v t qs
    eqs'                    = Sol.qbFilter (okInst env v t) eqs
    _msg                    = printf "\n\nrefineK: k = %s, eqs = %s" (F.showpp k) (F.showpp eqs)

--------------------------------------------------------------------------------
instK :: (Hashable s, F.Fixpoint s, F.PPrint s, Show s, Ord s, Eq s) => Bool
      -> F.SEnv s (F.Sort s)
      -> F.Symbol s
      -> F.Sort s
      -> [F.Qualifier s]
      -> Sol.QBind s
--------------------------------------------------------------------------------
instK ho env v t = Sol.qb . unique . concatMap (instKQ ho env v t)
  where
    unique       = L.nubBy ((. Sol.eqPred) . (==) . Sol.eqPred)

instKQ :: (Ord s, Show s, F.PPrint s, F.Fixpoint s, Hashable s, Eq s) => Bool
       -> F.SEnv s (F.Sort s)
       -> F.Symbol s
       -> F.Sort s
       -> F.Qualifier s
       -> [Sol.EQual s]
instKQ ho env v t q = do 
  (su0, qsu0, v0) <- candidates senv [(t, [v])] qp
  xs              <- match senv tyss [v0] (applyQP su0 qsu0 <$> qps) 
  return           $ Sol.eQual q (F.notracepp msg (reverse xs))
  where
    msg        = "instKQ " ++ F.showpp (F.qName q) ++ F.showpp (F.qParams q)
    qp : qps   = F.qParams q
    tyss       = instCands ho env
    senv       = (`F.lookupSEnvWithDistance` env)

instCands :: (Hashable s, Eq s) => Bool -> F.SEnv s (F.Sort s) -> [(F.Sort s, [F.Symbol s])]
instCands ho env = filter isOk tyss
  where
    tyss      = Misc.groupList [(t, x) | (x, t) <- xts]
    isOk      = if ho then const True else isNothing . F.functionSort . fst
    xts       = F.toListSEnv env

match :: (F.Fixpoint s, F.PPrint s, Ord s) => So.Env s -> [(F.Sort s, [F.Symbol s])] -> [F.Symbol s] -> [F.QualParam s] -> [[F.Symbol s]]
match env tyss xs (qp : qps)
  = do (su, qsu, x) <- candidates env tyss qp
       match env tyss (x : xs) (applyQP su qsu <$> qps)
match _   _   xs []
  = return xs

applyQP :: So.TVSubst s -> QPSubst s -> F.QualParam s -> F.QualParam s
applyQP su qsu qp = qp { qpSort = So.apply     su  (qpSort qp) 
                       , qpPat  = applyQPSubst qsu (qpPat qp) 
                       }

--------------------------------------------------------------------------------
candidates :: (Ord s, F.PPrint s, F.Fixpoint s, Eq s) => So.Env s -> [(F.Sort s, [F.Symbol s])] -> F.QualParam s 
           -> [(So.TVSubst s, QPSubst s, F.Symbol s)]
--------------------------------------------------------------------------------
candidates env tyss x = -- traceShow _msg
    [(su, qsu, y) | (t, ys)  <- tyss
                  , su       <- maybeToList (So.unifyFast mono env xt t)
                  , y        <- ys
                  , qsu      <- maybeToList (matchSym x y)                                     
    ]
  where
    xt   = F.qpSort x
    mono = So.isMono xt
    _msg = "candidates tyss :=" ++ F.showpp tyss ++ "tx := " ++ F.showpp xt

matchSym :: (Eq s) => F.QualParam s -> F.Symbol s -> Maybe (QPSubst s)
matchSym qp y' = case F.qpPat qp of
  F.PatPrefix s i -> JustSub i . F.FS <$> F.stripPrefix (F.symbol s) y 
  F.PatSuffix i s -> JustSub i . F.FS <$> F.stripSuffix (F.symbol s) y 
  F.PatNone       -> Just NoSub 
  F.PatExact s    -> if s == F.FS y then Just NoSub else Nothing 
  where 
    y             =  F.tidySymbol (F.symbol y')


data QPSubst s = NoSub | JustSub Int (F.Symbol s)

applyQPSubst :: QPSubst s -> F.QualPattern s -> F.QualPattern s 
applyQPSubst (JustSub i x) (F.PatPrefix s j) 
  | i == j = F.PatExact (F.FS (F.mappendSym (F.symbol s) (F.symbol x)))
applyQPSubst (JustSub i x) (F.PatSuffix j s) 
  | i == j = F.PatExact (F.FS (F.mappendSym (F.symbol x) (F.symbol s)))
applyQPSubst _ p 
  = p 

--------------------------------------------------------------------------------
okInst :: (Hashable s, Ord s, F.PPrint s, F.Fixpoint s, Show s) => F.SEnv s (F.Sort s) -> F.Symbol s -> F.Sort s -> Sol.EQual s -> Bool
--------------------------------------------------------------------------------
okInst env v t eq = isNothing tc
  where
    sr            = F.RR t (F.Reft (v, p))
    p             = Sol.eqPred eq
    tc            = So.checkSorted (F.srcSpan eq) env sr 
    -- _msg          = printf "okInst: t = %s, eq = %s, env = %s" (F.showpp t) (F.showpp eq) (F.showpp env)


--------------------------------------------------------------------------------
-- | Predicate corresponding to LHS of constraint in current solution
--------------------------------------------------------------------------------
lhsPred :: (Show s, Hashable s, F.PPrint s, F.Fixpoint s, Ord s, F.Loc a) => F.BindEnv s -> Sol.Solution s -> F.SimpC s a -> F.Expr s
lhsPred be s c = F.notracepp _msg $ fst $ apply g s bs
  where
    g          = CEnv ci be bs (F.srcSpan c)
    bs         = F.senv c
    ci         = sid c
    _msg       = "LhsPred for id = " ++ show (sid c) ++ " with SOLUTION = " ++ F.showpp s

data CombinedEnv s = CEnv 
  { ceCid  :: !Cid
  , ceBEnv :: !(F.BindEnv s)
  , ceIEnv :: !F.IBindEnv 
  , ceSpan :: !F.SrcSpan
  }

instance F.Loc (CombinedEnv s) where 
  srcSpan = ceSpan

type Cid         = Maybe Integer
type ExprInfo s    = (F.Expr s, KInfo)

apply :: (Hashable s, Ord s, F.Fixpoint s, Show s, F.PPrint s) => CombinedEnv s -> Sol.Sol s a (Sol.QBind s) -> F.IBindEnv -> ExprInfo s
apply g s bs      = (F.pAnd (pks:ps), kI)
  where
    (pks, kI)     = applyKVars g s ks  
    (ps,  ks, _)  = envConcKVars g s bs


envConcKVars :: (F.PPrint s, Show s, F.Fixpoint s, Ord s, Hashable s) => CombinedEnv s -> Sol.Sol s a (Sol.QBind s) -> F.IBindEnv -> ([F.Expr s], [F.KVSub s], [F.KVSub s])
envConcKVars g s bs = (concat pss, concat kss, L.nubBy (\x y -> F.ksuKVar x == F.ksuKVar y) $ concat gss)
  where
    (pss, kss, gss) = unzip3 [ F.notracepp ("sortedReftConcKVars" ++ F.showpp sr) $ F.sortedReftConcKVars x sr | (x, sr) <- xrs ]
    xrs             = lookupBindEnvExt g s <$> is
    is              = F.elemsIBindEnv bs

lookupBindEnvExt :: (Hashable s, Ord s, F.Fixpoint s, Show s, F.PPrint s) => CombinedEnv s -> Sol.Sol s a (Sol.QBind s) -> F.BindId -> (F.Symbol s, F.SortedReft s)
lookupBindEnvExt g s i 
  | Just p <- ebSol g s i = (x, sr { F.sr_reft = F.Reft (x, p) }) 
  | otherwise             = (x, sr)
   where 
      (x, sr)              = F.lookupBindEnv i (ceBEnv g) 

ebSol :: (F.PPrint s, Show s, F.Fixpoint s, Ord s, Hashable s) => CombinedEnv s -> Sol.Sol s a (Sol.QBind s) -> F.BindId -> Maybe (F.Expr s)
ebSol g s i = case  M.lookup i sebds of
  Just (Sol.EbSol p)    -> Just p
  Just (Sol.EbDef cs _) -> Just $ F.PAnd (cSol <$> cs)
  _                     -> Nothing
  where
    sebds = Sol.sEbd s

    ebReft s (i,c) = exElim (Sol.sxEnv s) (senv c) i (ebindReft g s c)
    cSol c = if sid c == ceCid g 
                then F.PFalse
                else ebReft s' (i, c)

    s' = s { Sol.sEbd = M.insert i Sol.EbIncr sebds }

ebindReft :: (F.PPrint s, Show s, Hashable s, F.Fixpoint s, Ord s) => CombinedEnv s -> Sol.Sol s a (Sol.QBind s) -> F.SimpC s () -> F.Pred s
ebindReft g s c = F.pAnd [ fst $ apply g' s bs, F.crhs c ]
  where
    g'          = g { ceCid = sid c, ceIEnv = bs } 
    bs          = F.senv c

exElim :: (F.PPrint s, Show s, F.Fixpoint s, Ord s, Hashable s) => F.SEnv s (F.BindId, F.Sort s) -> F.IBindEnv -> F.BindId -> F.Pred s -> F.Pred s
exElim env ienv xi p = F.notracepp msg (F.pExist yts p)
  where
    msg         = "exElim" -- printf "exElim: ix = %d, p = %s" xi (F.showpp p)
    yts         = [ (y, yt) | y        <- F.syms p
                            , (yi, yt) <- maybeToList (F.lookupSEnv y env)
                            , xi < yi
                            , yi `F.memberIBindEnv` ienv                  ]

applyKVars :: (F.Fixpoint s, Ord s, F.PPrint s, Show s, Hashable s, Eq s) => CombinedEnv s -> Sol.Sol s a (Sol.QBind s) -> [F.KVSub s] -> ExprInfo s
applyKVars g s = mrExprInfos (applyKVar g s) F.pAnd mconcat

applyKVar :: (Show s, Hashable s, F.PPrint s, Ord s, F.Fixpoint s) => CombinedEnv s -> Sol.Sol s a (Sol.QBind s) -> F.KVSub s -> ExprInfo s
applyKVar g s ksu = case Sol.lookup s (F.ksuKVar ksu) of
  Left cs   -> hypPred g s ksu cs
  Right eqs -> (F.pAnd $ fst <$> Sol.qbPreds msg s (F.ksuSubst ksu) eqs, mempty) -- TODO: don't initialize kvars that have a hyp solution
  where
    msg     = "applyKVar: " ++ show (ceCid g)

hypPred :: (F.Fixpoint s, Ord s, Hashable s, Show s, F.PPrint s) => CombinedEnv s -> Sol.Sol s a (Sol.QBind s) -> F.KVSub s -> Sol.Hyp s  -> ExprInfo s
hypPred g s ksu hyp = F.pOr *** mconcatPlus $ unzip $ cubePred g s ksu <$> hyp

{- | `cubePred g s k su c` returns the predicate for

        (k . su)

      defined by using cube

        c := [b1,...,bn] |- (k . su')

      in the binder environment `g`.

        bs' := the subset of "extra" binders in [b1...bn] that are *not* in `g`
        p'  := the predicate corresponding to the "extra" binders

 -}

elabExist :: (Eq s) => F.SrcSpan -> Sol.Sol s a (Sol.QBind s) -> [(F.Symbol s, F.Sort s)] -> F.Expr s -> F.Expr s
elabExist sp s xts p = F.pExist xts' p
  where
    xts'        = [ (x, elab t) | (x, t) <- xts]
    elab        = So.elaborate (F.atLoc sp "elabExist") env
    env         = Sol.sEnv s

cubePred :: (F.PPrint s, Ord s, Show s, F.Fixpoint s, F.Fixpoint s, Eq s, Hashable s) => CombinedEnv s -> Sol.Sol s a (Sol.QBind s) -> F.KVSub s -> Sol.Cube s -> ExprInfo s
cubePred g s ksu c    = (F.notracepp "cubePred" $ elabExist sp s xts (psu &.& p), kI)
  where
    sp                = F.srcSpan g
    ((xts,psu,p), kI) = cubePredExc g s ksu c bs'
    bs'               = delCEnv s k bs
    bs                = Sol.cuBinds c
    k                 = F.ksuKVar ksu

type Binders s = [(F.Symbol s, F.Sort s)]

-- | @cubePredExc@ computes the predicate for the subset of binders bs'.
--   The output is a tuple, `(xts, psu, p, kI)` such that the actual predicate
--   we want is `Exists xts. (psu /\ p)`.

cubePredExc :: (F.Fixpoint s, Show s, Ord s, F.PPrint s, Hashable s, Eq s) => CombinedEnv s -> Sol.Sol s a (Sol.QBind s) -> F.KVSub s -> Sol.Cube s -> F.IBindEnv
            -> ((Binders s, F.Pred s, F.Pred s), KInfo)

cubePredExc g s ksu c bs' = (cubeP, extendKInfo kI (Sol.cuTag c))
  where
    cubeP           = (xts, psu, elabExist sp s yts' (p' &.& psu') )
    sp              = F.srcSpan g
    yts'            = symSorts g bs'
    g'              = addCEnv  g bs
    (p', kI)        = apply g' s bs'
    (_  , psu')     = substElim (Sol.sEnv s) sEnv g' k su'
    (xts, psu)      = substElim (Sol.sEnv s) sEnv g  k su
    su'             = Sol.cuSubst c
    bs              = Sol.cuBinds c
    k               = F.ksuKVar   ksu
    su              = F.ksuSubst  ksu
    sEnv            = F.insertSEnv (F.ksuVV ksu) (F.ksuSort ksu) (F.seSort $ Sol.sEnv s)

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
substElim :: (Hashable s, F.PPrint s, Ord s, Show s, F.Fixpoint s) => F.SymEnv s -> F.SEnv s (F.Sort s) -> CombinedEnv s -> F.KVar s -> F.Subst s -> ([(F.Symbol s, F.Sort s)], F.Pred s)
substElim syEnv sEnv g _ (F.Su m) = (xts, p)
  where
    p      = F.pAnd [ mkSubst sp syEnv x (substSort sEnv frees x t) e t | (x, e, t) <- xets  ]
    xts    = [ (x, t)    | (x, _, t) <- xets, not (S.member x frees) ]
    xets   = [ (x, e, t) | (x, e)    <- xes, t <- sortOf e, not (isClass t)]
    xes    = M.toList m
    env    = combinedSEnv g
    frees  = S.fromList (concatMap (F.syms . snd) xes)
    sortOf = maybeToList . So.checkSortExpr sp env
    sp     = F.srcSpan g

substSort :: (F.PPrint s, Hashable s, Eq s) => F.SEnv s (F.Sort s) -> S.HashSet (F.Symbol s) -> F.Symbol s -> F.Sort s -> F.Sort s
substSort sEnv _frees x _t = fromMaybe (err x) $ F.lookupSEnv x sEnv
  where
    err x            = error $ "Solution.mkSubst: unknown binder " ++ F.showpp x


-- LH #1091
mkSubst :: (Show s, Hashable s, F.PPrint s, Ord s, F.Fixpoint s) => F.SrcSpan -> F.SymEnv s -> F.Symbol s -> F.Sort s -> F.Expr s -> F.Sort s -> F.Expr s
mkSubst sp env x tx ey ty
  | tx == ty    = F.EEq ex ey
  | otherwise   = {- F.tracepp _msg -} (F.EEq ex' ey')
  where
    _msg         = "mkSubst-DIFF:" ++ F.showpp (tx, ty) ++ F.showpp (ex', ey')
    ex          = F.expr x
    ex'         = elabToInt sp env ex tx
    ey'         = elabToInt sp env ey ty

elabToInt :: (F.Fixpoint s, Ord s, F.PPrint s, Hashable s, Show s, Eq s) => F.SrcSpan -> F.SymEnv s -> F.Expr s -> F.Sort s -> F.Expr s
elabToInt sp env e s = So.elaborate (F.atLoc sp "elabToInt") env (So.toInt env e s)

isClass :: F.Sort s -> Bool
isClass F.FNum  = True
isClass F.FFrac = True
isClass _       = False

--badExpr :: CombinedEnv -> F.KVar s -> F.Expr s -> a
--badExpr g@(i,_,_) k e
  -- = errorstar $ "substSorts has a badExpr: "
              -- ++ show e
              -- ++ " in cid = "
              -- ++ show i
              -- ++ " for kvar " ++ show k
              -- ++ " in env \n"
              -- ++ show (combinedSEnv g)

-- substPred :: F.Subst s -> F.Pred s
-- substPred (F.Su m) = F.pAnd [ F.PAtom F.Eq (F.eVar x) e | (x, e) <- M.toList m]

combinedSEnv :: (Hashable s, Eq s) => CombinedEnv s -> F.SEnv s (F.Sort s)
combinedSEnv g = F.sr_sort <$> F.fromListSEnv (F.envCs be bs)
  where 
    be         = ceBEnv g 
    bs         = ceIEnv g 

addCEnv :: CombinedEnv s -> F.IBindEnv -> CombinedEnv s
addCEnv g bs' = g { ceIEnv = F.unionIBindEnv (ceIEnv g) bs' }
-- addCEnv (x, be, bs) bs' = (x, be, F.unionIBindEnv bs bs')


delCEnv :: (Hashable s, Eq s) => Sol.Sol s a (Sol.QBind s) -> F.KVar s -> F.IBindEnv -> F.IBindEnv
delCEnv s k bs = F.diffIBindEnv bs _kbs
  where
    _kbs       = Misc.safeLookup "delCEnv" k (Sol.sScp s)

symSorts :: CombinedEnv s -> F.IBindEnv -> [(F.Symbol s, F.Sort s)]
symSorts g bs = second F.sr_sort <$> F.envCs (ceBEnv g) bs

_noKvars :: F.Expr s -> Bool
_noKvars = null . V.kvars

--------------------------------------------------------------------------------
-- | Information about size of formula corresponding to an "eliminated" KVar.
--------------------------------------------------------------------------------
data KInfo = KI { kiTags  :: [Tag]
                , kiDepth :: !Int
                , kiCubes :: !Integer
                } deriving (Eq, Ord, Show)

instance Semigroup KInfo where
  ki <> ki' = KI ts d s
    where
      ts    = appendTags (kiTags  ki) (kiTags  ki')
      d     = max        (kiDepth ki) (kiDepth ki')
      s     = (*)        (kiCubes ki) (kiCubes ki')

instance Monoid KInfo where
  mempty  = KI [] 0 1
  mappend = (<>)

mplus :: KInfo -> KInfo -> KInfo
mplus ki ki' = (mappend ki ki') { kiCubes = kiCubes ki + kiCubes ki'}

mconcatPlus :: [KInfo] -> KInfo
mconcatPlus = foldr mplus mempty

appendTags :: [Tag] -> [Tag] -> [Tag]
appendTags ts ts' = Misc.sortNub (ts ++ ts')

extendKInfo :: KInfo -> F.Tag -> KInfo
extendKInfo ki t = ki { kiTags  = appendTags [t] (kiTags  ki)
                      , kiDepth = 1  +            kiDepth ki }

-- mrExprInfos :: (a -> ExprInfo) -> ([F.Expr] -> F.Expr) -> ([KInfo] -> KInfo) -> [a] -> ExprInfo
mrExprInfos :: (a -> (b, c)) -> ([b] -> b1) -> ([c] -> c1) -> [a] -> (b1, c1)
mrExprInfos mF erF irF xs = (erF es, irF is)
  where
    (es, is)              = unzip $ map mF xs

--------------------------------------------------------------------------------
-- | `ebindInfo` constructs the information about the "ebind-definitions". 
--------------------------------------------------------------------------------
ebindInfo :: (F.Fixpoint s, F.PPrint s, Ord s, Hashable s) => F.SInfo s a -> [(F.BindId, Sol.EbindSol s)]
ebindInfo si = group [((bid, x), cons cid) | (bid, cid, x) <- ebindDefs si]
  where cons cid = const () <$> Misc.safeLookup "ebindInfo" cid cs
        cs = F.cm si
        cmpByFst x y = fst ( fst x ) == fst ( fst y )
        group xs = (\ys -> ( (fst $ fst $ head ys)
                           , Sol.EbDef (snd <$> ys) (snd $ fst $ head ys)))
                    <$> L.groupBy cmpByFst xs

ebindDefs :: (Hashable s, Ord s, F.PPrint s, F.Fixpoint s) => F.SInfo s a -> [(F.BindId, F.SubcId, F.Symbol s)]
ebindDefs si = [ (bid, cid, x) | (cid, x) <- cDefs
                               , bid      <- maybeToList (M.lookup x ebSyms)]
  where 
    ebSyms   = ebindSyms si 
    cDefs    = cstrDefs  si 

ebindSyms :: (Hashable s, Eq s) => F.SInfo s a -> M.HashMap (F.Symbol s) F.BindId
ebindSyms si = M.fromList [ (xi, bi) | bi        <- ebinds si
                                     , let (xi,_) = F.lookupBindEnv bi be ] 
  where
    be       = F.bs si 
 
cstrDefs :: (F.Fixpoint s, F.PPrint s, Ord s) => F.SInfo s a -> [(F.SubcId, F.Symbol s)]
cstrDefs si = [(cid, x) | (cid, c) <- M.toList (cm si)
                        , x <- maybeToList (cstrDef be c) ]
  where 
    be      = F.bs si

cstrDef :: (Ord s, F.PPrint s, F.Fixpoint s) => F.BindEnv s -> F.SimpC s a -> Maybe (F.Symbol s) 
cstrDef be c 
  | Just (F.EVar x) <- e = Just x 
  | otherwise            = Nothing 
  where 
    (v,_)              = F.lookupBindEnv (cbind c) be 
    e                  = F.notracepp _msg $ F.isSingletonExpr v rhs 
    _msg                = "cstrDef: " ++ show (stag c) ++ " crhs = " ++ F.showpp rhs 
    rhs                = V.stripCasts (crhs c)

