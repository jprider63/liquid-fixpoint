--------------------------------------------------------------------------------
-- | This module implements "Proof by Logical Evaluation" where we 
--   unfold function definitions if they *must* be unfolded, to strengthen
--   the environments with function-definition-equalities. 
--   The algorithm is discussed at length in:
-- 
--     1. "Refinement Reflection", POPL 2018, https://arxiv.org/pdf/1711.03842
--     2. "Reasoning about Functions", VMCAI 2018, https://ranjitjhala.github.io/static/reasoning-about-functions.pdf 
--------------------------------------------------------------------------------
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ExistentialQuantification #-}

module Language.Fixpoint.Solver.Instantiate (instantiate) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Config  as FC
import qualified Language.Fixpoint.Types.Visitor as Vis
import qualified Language.Fixpoint.Misc          as Misc -- (mapFst)
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Defunctionalize
import qualified Language.Fixpoint.Utils.Trie    as T 
import           Language.Fixpoint.Utils.Progress -- as T 
import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Graph.Deps             (isTarget) 
import           Language.Fixpoint.Solver.Sanitize        (symbolEnv)
import           Control.Monad.State
import qualified Data.Text            as T
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S
import           Data.Hashable
import qualified Data.List            as L
import qualified Data.Maybe           as Mb -- (isNothing, catMaybes, fromMaybe)
import           Data.Char            (isUpper)
-- import           Debug.Trace          (trace)
-- import           Text.Printf (printf)

mytracepp :: (PPrint a) => String -> a -> a
mytracepp = notracepp 

--------------------------------------------------------------------------------
-- | Strengthen Constraint Environments via PLE 
--------------------------------------------------------------------------------
instantiate :: (Show s, Ord s, Fixpoint s, PPrint s, Hashable s, SMT.SMTLIB2 s s, Loc a) => Config -> SInfo s a -> IO (SInfo s a)
instantiate cfg fi
  | rewriteAxioms cfg && noIncrPle cfg
  = instantiate' cfg fi

  | rewriteAxioms cfg -- && incrPle cfg 
  = incrInstantiate' cfg fi

  | otherwise         
  = return fi

------------------------------------------------------------------------------- 
-- | New "Incremental" PLE
------------------------------------------------------------------------------- 
incrInstantiate' :: (SMT.SMTLIB2 s s, Hashable s, PPrint s, Fixpoint s, Ord s, Show s, Loc a) => Config -> SInfo s a -> IO (SInfo s a)
------------------------------------------------------------------------------- 
incrInstantiate' cfg fi = do 
    let cs = [ (i, c) | (i, c) <- M.toList (cm fi), isPleCstr aEnv i c ] 
    let t  = mkCTrie cs                                               -- 1. BUILD the Trie
    res   <- withProgress (1 + length cs) $ 
               withCtx cfg file sEnv (pleTrie t . instEnv cfg fi cs)  -- 2. TRAVERSE Trie to compute InstRes
    return $ resSInfo cfg sEnv fi res                                 -- 3. STRENGTHEN SInfo s using InstRes
  where
    file   = srcFile cfg ++ ".evals"
    sEnv   = symbolEnv cfg fi
    aEnv   = ae fi 



------------------------------------------------------------------------------- 
-- | Step 1a: @instEnv@ sets up the incremental-PLE environment 
instEnv :: (SMT.SMTLIB2 s s, Hashable s, Ord s, Fixpoint s, Show s, PPrint s, Loc a) => Config -> SInfo s a -> [(SubcId, SimpC s a)] -> SMT.Context s -> InstEnv s a 
instEnv cfg fi cs ctx = InstEnv cfg ctx bEnv aEnv (M.fromList cs) γ s0
  where 
    bEnv              = bs fi
    aEnv              = ae fi
    γ                 = knowledge cfg ctx aEnv 
    s0                = EvalEnv 0 [] aEnv (SMT.ctxSymEnv ctx) cfg 

---------------------------------------------------------------------------------------------- 
-- | Step 1b: @mkCTrie@ builds the @Trie@ of constraints indexed by their environments 
mkCTrie :: [(SubcId, SimpC s a)] -> CTrie 
mkCTrie ics  = mytracepp  "TRIE" $ T.fromList [ (cBinds c, i) | (i, c) <- ics ]
  where
    cBinds   = L.sort . elemsIBindEnv . senv 

---------------------------------------------------------------------------------------------- 
-- | Step 2: @pleTrie@ walks over the @CTrie@ to actually do the incremental-PLE
pleTrie :: (Show s, SMT.SMTLIB2 s s, Fixpoint s, PPrint s, Ord s, Hashable s) => CTrie -> InstEnv s a -> IO (InstRes s)
pleTrie t env = loopT env ctx0 diff0 Nothing res0 t 
  where 
    diff0        = []
    res0         = M.empty 
    ctx0         = initCtx es0
    es0          = eqBody <$> L.filter (null . eqArgs) (aenvEqs . ieAenv $ env)

loopT :: (PPrint s, Fixpoint s, Ord s, SMT.SMTLIB2 s s, Hashable s, Show s) => InstEnv s a -> ICtx s -> Diff -> Maybe BindId -> InstRes s -> CTrie -> IO (InstRes s)
loopT env ctx delta i res t = case t of 
  T.Node []  -> return res
  T.Node [b] -> loopB env ctx delta i res b
  T.Node bs  -> withAssms env ctx delta Nothing $ \ctx' -> do 
                  (ctx'', res') <- ple1 env ctx' i Nothing res 
                  foldM (loopB env ctx'' [] i) res' bs

loopB :: (Show s, Hashable s, SMT.SMTLIB2 s s, Ord s, Fixpoint s, PPrint s) => InstEnv s a -> ICtx s -> Diff -> Maybe BindId -> InstRes s -> CBranch -> IO (InstRes s)
loopB env ctx delta iMb res b = case b of 
  T.Bind i t -> loopT env ctx (i:delta) (Just i) res t
  T.Val cid  -> withAssms env ctx delta (Just cid) $ \ctx' -> do 
                  progressTick
                  (snd <$> ple1 env ctx' iMb (Just cid) res) 


withAssms :: (PPrint s, Fixpoint s, Ord s, SMT.SMTLIB2 s s, Hashable s, Show s) => InstEnv s a -> ICtx s -> Diff -> Maybe SubcId -> (ICtx s -> IO b) -> IO b 
withAssms env@(InstEnv {..}) ctx delta cidMb act = do 
  let ctx'  = updCtx env ctx delta cidMb 
  let assms = mytracepp  ("ple1-assms: " ++ show (cidMb, delta)) (icAssms ctx')
  SMT.smtBracket ieSMT  "PLE.evaluate" $ do
    forM_ assms (SMT.smtAssert ieSMT) 
    act ctx'

-- | @ple1@ performs the PLE at a single "node" in the Trie 
ple1 :: (Hashable s, Show s, SMT.SMTLIB2 s s, Ord s, Fixpoint s, PPrint s) => InstEnv s a -> ICtx s -> Maybe BindId -> Maybe SubcId -> InstRes s -> IO (ICtx s, InstRes s)
ple1 env@(InstEnv {..}) ctx i cidMb res = do 
  let cands = mytracepp  ("ple1-cands: "  ++ show cidMb) $ S.toList (icCands ctx) 
  -- unfolds  <- evalCands ieKnowl ieEvEnv cands   
  unfolds  <- evalCandsLoop ieCfg ieSMT ieKnowl ieEvEnv cands   
  return    $ updCtxRes env ctx res i cidMb (mytracepp  ("ple1-cands-unfolds: " ++ show cidMb) unfolds)

_evalCands :: (PPrint s, Fixpoint s, Ord s, Hashable s, Show s, Eq s) => Knowledge s -> EvalEnv s -> [Expr s] -> IO [Unfold s] 
_evalCands _ _  []    = return []
_evalCands γ s0 cands = do eqs <- mapM (evalOne γ s0) cands
                           return $ mkUnfolds (zip (Just <$> cands) eqs)

unfoldPred :: (Hashable s, Ord s, Fixpoint s, Show s, PPrint s) => Config -> SMT.Context s -> [Unfold s] -> Pred s 
unfoldPred cfg ctx = toSMT cfg ctx [] . pAnd . concatMap snd  

evalCandsLoop :: (PPrint s, Fixpoint s, Ord s, SMT.SMTLIB2 s s, Show s, Hashable s, Eq s) => Config -> SMT.Context s -> Knowledge s -> EvalEnv s -> [Expr s] -> IO [Unfold s] 
evalCandsLoop cfg ctx γ s0 cands = go [] cands 
  where 
    go acc []    = return acc 
    go acc cands = do eqss   <- SMT.smtBracket ctx "PLE.evaluate" $ do
                                  SMT.smtAssert ctx (unfoldPred cfg ctx acc) 
                                  mapM (evalOne γ s0) cands
                      let us  = zip (Just <$> cands) eqss 
                      case mkUnfolds us of 
                        []  -> return acc 
                        us' -> do let acc'   = acc ++ us' 
                                  let oks    = S.fromList [ e | (Just e, _) <- us' ]
                                  let cands' = [ e | e <- cands, not (S.member e oks) ] 
                                  go acc' cands' 


---------------------------------------------------------------------------------------------- 
-- | Step 3: @resSInfo@ uses incremental PLE result @InstRes@ to produce the strengthened SInfo s 

resSInfo :: (Hashable s, Show s, PPrint s, Ord s, Fixpoint s) => Config -> SymEnv s -> SInfo s a -> InstRes s -> SInfo s a
resSInfo cfg env fi res = strengthenBinds fi res' 
  where
    res'     = M.fromList $ mytracepp  "ELAB-INST:  " $ zip is ps''
    ps''     = zipWith (\i -> elaborate (atLoc dummySpan ("PLE1 " ++ show i)) env) is ps' 
    ps'      = defuncAny cfg env ps
    (is, ps) = unzip (M.toList res)

---------------------------------------------------------------------------------------------- 
-- | @InstEnv@ has the global information needed to do PLE
data InstEnv s a = InstEnv 
  { ieCfg   :: !Config
  , ieSMT   :: !(SMT.Context s)
  , ieBEnv  :: !(BindEnv s)
  , ieAenv  :: !(AxiomEnv s)
  , ieCstrs :: !(M.HashMap SubcId (SimpC s a))
  , ieKnowl :: !(Knowledge s)
  , ieEvEnv :: !(EvalEnv s)
  } 

-- | @ICtx@ is the local information -- at each trie node -- obtained by incremental PLE
data ICtx s    = ICtx 
  { icAssms  :: ![Pred s]          -- ^ Hypotheses, already converted to SMT format 
  , icCands  :: S.HashSet (Expr s)   -- ^ "Candidates" for unfolding
  , icEquals :: ![Expr s]          -- ^ "Known" equalities
  , icSolved :: S.HashSet (Expr s)   -- ^ Terms that we have already expanded
  } 

-- | @InstRes@ is the final result of PLE; a map from @BindId@ to the equations "known" at that BindId
type InstRes s = M.HashMap BindId (Expr s)

-- | @Unfold is the result of running PLE at a single equality; 
--     (e, [(e1, e1')...]) is the source @e@ and the (possible empty) 
--   list of PLE-generated equalities (e1, e1') ... 
-- type Unfold  = (Maybe Expr, [(Expr, Expr)])
type Unfold s  = (Maybe (Expr s), [Expr s])
type CTrie   = T.Trie   SubcId
type CBranch = T.Branch SubcId
type Diff    = [BindId]    -- ^ in "reverse" order

initCtx :: (Hashable s, Ord s, PPrint s, Fixpoint s) => [Expr s] -> ICtx s
initCtx es = ICtx 
  { icAssms  = [] 
  , icCands  = mempty 
  , icEquals = mytracepp  "INITIAL-STUFF-INCR" es 
  , icSolved = mempty
  }

equalitiesPred :: (Eq s) => [(Expr s, Expr s)] -> [Expr s]
equalitiesPred eqs = [ EEq e1 e2 | (e1, e2) <- eqs, e1 /= e2 ] 

updCtxRes :: (Hashable s, Ord s, PPrint s, Fixpoint s) => InstEnv s a -> ICtx s -> InstRes s -> Maybe BindId -> Maybe SubcId -> [Unfold s] -> (ICtx s, InstRes s) 
updCtxRes env ctx res iMb cidMb us 
                       = -- trace _msg 
                         ( ctx { {- icCands  = cands', -} icSolved = solved', icEquals = mempty}
                         , res'
                         ) 
  where 
    _msg               = Mb.maybe "nuttin\n" (debugResult env res') cidMb
    res'               = updRes res iMb (pAnd solvedEqs) 
    _cands'             = ((icCands ctx) `S.union` newCands) `S.difference` solved' 
    solved'            = S.union (icSolved ctx) solvedCands 
    newCands           = S.fromList (concatMap topApps newEqs) 
    solvedCands        = S.fromList [ e | (Just e, _) <- okUnfolds ] 
    solvedEqs          = icEquals ctx ++ newEqs 
    newEqs             = concatMap snd okUnfolds
    okUnfolds          = mytracepp  _str [ (eMb, ps)  | (eMb, ps) <- us, {- let ps = equalitiesPred eqs, -} not (null ps) ] 
    _str               = "okUnfolds " ++ showpp (iMb, cidMb)
    -- cands'             = S.difference (icCands ctx) (S.fromList solvedCands)
    -- solvedEqs          = icEquals ctx ++ concatMap snd us
    -- solvedCands        = [ e          | (Just e, _) <- us]

mkUnfolds :: (Eq s) => [(a, [(Expr s, Expr s)])] -> [(a, [Expr s])]
mkUnfolds us = [ (eMb, ps)  | (eMb, eqs) <- us
                            , let ps = equalitiesPred eqs
                            , not (null ps) 
               ] 

debugResult :: (PPrint s, Fixpoint s, Ord s) => InstEnv s a -> InstRes s -> SubcId -> String 
debugResult (InstEnv {..}) res i = msg 
  where 
    msg                          = "INCR-INSTANTIATE i = " ++ show i ++ ": " ++ showpp cidEqs 
    cidEqs                       = pAnd [ e | i <- cBinds, e <- Mb.maybeToList $ M.lookup i res ] 
    cBinds                       = L.sort . elemsIBindEnv . senv . getCstr ieCstrs $ i


updRes :: InstRes s -> Maybe BindId -> Expr s -> InstRes s
updRes res (Just i) e = M.insert i e res 
updRes res  Nothing _ = res 

-- | @updCtx env ctx delta cidMb@ adds the assumptions and candidates from @delta@ and @cidMb@ 
--   to the context. 
updCtx :: (PPrint s, Hashable s, Ord s, Fixpoint s, Show s) => InstEnv s a -> ICtx s -> Diff -> Maybe SubcId -> ICtx s
updCtx InstEnv {..} ctx delta cidMb 
              = ctx { icAssms  = ctxEqs  
                    , icCands  = cands   <> icCands  ctx
                    , icEquals = initEqs <> icEquals ctx }
  where         
    initEqs   = equalitiesPred (initEqualities ieSMT ieAenv bs)
    cands     = (S.fromList (concatMap topApps es0)) `S.difference` (icSolved ctx)
    ctxEqs    = toSMT ieCfg ieSMT [] <$> concat 
                  [ initEqs 
                  , [ expr xr   | xr@(_, r) <- bs, null (Vis.kvars r) ] 
                  ]
    (bs, es0) = (unElab <$> binds, unElab <$> es)
    es        = eRhs : (expr <$> binds) 
    eRhs      = maybe PTrue crhs subMb
    binds     = [ lookupBindEnv i ieBEnv | i <- delta ] 
    subMb     = getCstr ieCstrs <$> cidMb

getCstr :: M.HashMap SubcId (SimpC s a) -> SubcId -> SimpC s a 
getCstr env cid = Misc.safeLookup "Instantiate.getCstr" cid env

instance PPrint CTrie where 
  pprintTidy _ = Misc.tshow 

--------------------------------------------------------------------------------
-- | "Old" GLOBAL PLE 
--------------------------------------------------------------------------------
instantiate' :: (SMT.SMTLIB2 s s, Hashable s, PPrint s, Fixpoint s, Ord s, Show s, Loc a) => Config -> SInfo s a -> IO (SInfo s a)
instantiate' cfg fi = sInfo cfg env fi <$> withCtx cfg file env act
  where
    act ctx         = forM cstrs $ \(i, c) ->
                        ((i,srcSpan c),) . mytracepp  ("INSTANTIATE i = " ++ show i) <$> instSimpC cfg ctx (bs fi) aenv i c
    cstrs           = [ (i, c) | (i, c) <- M.toList (cm fi) , isPleCstr aenv i c] 
    file            = srcFile cfg ++ ".evals"
    env             = symbolEnv cfg fi
    aenv            = {- mytracepp  "AXIOM-ENV" -} (ae fi)


sInfo :: (Show s, Hashable s, PPrint s, Ord s, Fixpoint s) => Config -> SymEnv s -> SInfo s a -> [((SubcId, SrcSpan), Expr s)] -> SInfo s a
sInfo cfg env fi ips = strengthenHyp fi (mytracepp  "ELAB-INST:  " $ zip (fst <$> is) ps'')
  where
    (is, ps)         = unzip ips
    ps'              = defuncAny cfg env ps
    ps''             = zipWith (\(i, sp) -> elaborate (atLoc sp ("PLE1 " ++ show i)) env) is ps' 

instSimpC :: (PPrint s, Fixpoint s, Ord s, SMT.SMTLIB2 s s, Show s, Hashable s, Eq s) => Config -> SMT.Context s -> BindEnv s -> AxiomEnv s -> SubcId -> SimpC s a -> IO (Expr s)
instSimpC cfg ctx bds aenv sid sub 
  | isPleCstr aenv sid sub = do
    let is0       = mytracepp  "INITIAL-STUFF" $ eqBody <$> L.filter (null . eqArgs) (aenvEqs aenv) 
    let (bs, es0) = cstrExprs bds sub
    equalities   <- evaluate cfg ctx aenv bs es0 sid 
    let evalEqs   = [ EEq e1 e2 | (e1, e2) <- equalities, e1 /= e2 ] 
    return        $ pAnd (is0 ++ evalEqs)  
  | otherwise     = return PTrue

isPleCstr :: (Eq s) => AxiomEnv s -> SubcId -> SimpC s a -> Bool
isPleCstr aenv sid c = isTarget c && M.lookupDefault False sid (aenvExpand aenv) 

cstrExprs :: (Hashable s, Ord s, Fixpoint s, Show s) => BindEnv s -> SimpC s a -> ([(Symbol s, SortedReft s)], [Expr s])
cstrExprs bds sub = (unElab <$> binds, unElab <$> es)
  where
    es            = (crhs sub) : (expr <$> binds)
    binds         = envCs bds (senv sub)

unElab :: (Eq s, Vis.Visitable s t) => t -> t
unElab = Vis.stripCasts . unApply

unApply :: (Eq s, Vis.Visitable s t) => t -> t
unApply = Vis.trans (Vis.defaultVisitor { Vis.txExpr = const go }) () ()
  where
    go (ECst (EApp (EApp f e1) e2) _)
      | Just _ <- unApplyAt f = EApp e1 e2
    go e                      = e

--------------------------------------------------------------------------------
-- | Symbolic Evaluation with SMT
--------------------------------------------------------------------------------
evaluate :: (Hashable s, Show s, SMT.SMTLIB2 s s, Ord s, Fixpoint s, PPrint s) => Config -> SMT.Context s -> AxiomEnv s -- ^ Definitions
         -> [(Symbol s, SortedReft s)]            -- ^ Environment of "true" facts 
         -> [Expr s]                            -- ^ Candidates for unfolding 
         -> SubcId                            -- ^ Constraint Id
         -> IO [(Expr s, Expr s)]                 -- ^ Newly unfolded equalities
--------------------------------------------------------------------------------
evaluate cfg ctx aenv facts es sid = do 
  let eqs      = initEqualities ctx aenv facts  
  let γ        = knowledge cfg ctx aenv 
  let cands    = mytracepp  ("evaluate-cands " ++ showpp sid) $ Misc.hashNub (concatMap topApps es)
  let s0       = EvalEnv 0 [] aenv (SMT.ctxSymEnv ctx) cfg
  let ctxEqs   = [ toSMT cfg ctx [] (EEq e1 e2) | (e1, e2)  <- eqs ]
              ++ [ toSMT cfg ctx [] (expr xr)   | xr@(_, r) <- facts, null (Vis.kvars r) ] 
  eqss        <- _evalLoop cfg ctx γ s0 ctxEqs cands 
  return       $ eqs ++ eqss


 
_evalLoop :: (PPrint s, Fixpoint s, Ord s, SMT.SMTLIB2 s s, Show s, Hashable s, Eq s) => Config -> SMT.Context s -> Knowledge s -> EvalEnv s -> [Pred s] -> [Expr s] -> IO [(Expr s, Expr s)]
_evalLoop cfg ctx γ s0 ctxEqs cands = loop 0 [] cands 
  where 
    loop _ acc []    = return acc
    loop i acc cands = do let eqp = toSMT cfg ctx [] $ pAnd $ equalitiesPred acc
                          eqss <- SMT.smtBracket ctx "PLE.evaluate" $ do
                                    forM_ (eqp : ctxEqs) (SMT.smtAssert ctx) 
                                    mapM (evalOne γ s0) cands
                          case concat eqss of 
                            []   -> return acc 
                            eqs' -> do let acc'   = acc ++ eqs' 
                                       let oks    = S.fromList (fst <$> eqs')
                                       let cands' = [ e | e <- cands, not (S.member e oks) ] 
                                       loop (i+1) acc' cands'



--------------------------------------------------------------------------------
data EvalEnv s = EvalEnv
  { evId        :: !Int
  , evSequence  :: [(Expr s, Expr s)]
  , _evAEnv     :: !(AxiomEnv s)
  , evEnv       :: !(SymEnv s)
  , _evCfg      :: !Config
  }

type EvalST s a = StateT (EvalEnv s) IO a
--------------------------------------------------------------------------------

evalOne :: (Show s, Hashable s, Ord s, Fixpoint s, PPrint s) => Knowledge s -> EvalEnv s -> Expr s -> IO [(Expr s, Expr s)]
evalOne γ s0 e = do
  (e', st) <- runStateT (eval γ initCS (mytracepp "evalOne: " e)) s0 
  if e' == e then return [] else return ((e, e') : evSequence st)

{- | [NOTE: Eval-Ite]  We should not be doing any PLE/eval under if-then-else where 
     the guard condition does not provably hold. For example, see issue #387.
     However, its ok and desirable to `eval` in this case, as long as one is not 
     unfolding recursive functions. To permit this, we track the "call-stack" and 
     whether or not, `eval` is occurring under an unresolved guard: if so, we do not 
     expand under any function that is already on the call-stack.
  -}

data Recur  = Ok | Stop deriving (Eq, Show)
type CStack s = ([Symbol s], Recur)

instance PPrint Recur where 
  pprintTidy _ = Misc.tshow 

initCS :: CStack s 
initCS = ([], Ok)

pushCS :: CStack s -> Symbol s -> CStack s 
pushCS (fs, r) f = (f:fs, r)

recurCS :: (Eq s) => CStack s -> Symbol s -> Bool 
recurCS (_,  Ok) _ = True 
-- recurCS (_,  _ ) _ = False -- not (f `elem` fs) 
recurCS (fs, _) f  = not (f `elem` fs) 

noRecurCS :: CStack s -> CStack s 
noRecurCS (fs, _) = (fs, Stop)

-- Don't evaluate under Lam, App, Ite, or Constants
topApps :: Expr s -> [Expr s]
topApps = go 
  where 
    go (PAnd es)       = concatMap go es
    go (POr es)        = concatMap go es
    go (PAtom _ e1 e2) = go e1  ++ go e2
    go (PIff e1 e2)    = go e1  ++ go e2
    go (PImp e1 e2)    = go e1  ++ go e2
    go (EBin  _ e1 e2) = go e1  ++ go e2
    go (PNot e)        = go e
    go (ENeg e)        = go e
    go e@(EApp _ _)    = [e]
    go _               = []

-- makeLam is the adjoint of splitEApp
makeLam :: Knowledge s -> Expr s -> Expr s
makeLam γ e = L.foldl' (flip ELam) e (knLams γ)

eval :: (PPrint s, Fixpoint s, Ord s, Eq s, Hashable s, Show s) => Knowledge s -> CStack s -> Expr s -> EvalST s (Expr s)
eval γ stk = go 
  where 
    go (ELam (x,s) e)   = ELam (x, s) <$> eval γ' stk e where γ' = γ { knLams = (x, s) : knLams γ }
    go e@(EIte b e1 e2) = go b        >>= \b' -> evalIte γ stk e b' e1 e2
    go (ECoerc s t e)   = ECoerc s t  <$> go e
    go e@(EApp _ _)     = evalArgs γ stk e >>= evalApp γ stk e 
    go e@(EVar _)       = evalApp  γ stk e (e, [])
    go (PAtom r e1 e2)  = PAtom r      <$> go e1 <*> go e2
    go (ENeg e)         = ENeg         <$> go e
    go (EBin o e1 e2)   = EBin o       <$> go e1 <*> go e2
    go (ETApp e t)      = flip ETApp t <$> go e
    go (ETAbs e s)      = flip ETAbs s <$> go e
    go (PNot e)         = PNot         <$> go e
    go (PImp e1 e2)     = PImp         <$> go e1 <*> go e2
    go (PIff e1 e2)     = PIff         <$> go e1 <*> go e2
    go (PAnd es)        = PAnd         <$> (go  <$$> es)
    go (POr es)         = POr          <$> (go  <$$> es)
    go e                = return e

(<$$>) :: (Monad m) => (a -> m b) -> [a] -> m [b]
f <$$> xs = f Misc.<$$> xs

-- | `evalArgs` also evaluates all the partial applications for hacky reasons,
--   suppose `foo g = id` then we want `foo g 10 = 10` and for that we need 
--   to `eval` the term `foo g` into `id` to tickle the `eval` on `id 10`.
--   This seems a bit of a hack. At any rate, this can lead to divergence. 
--   TODO: distill a .fq test from the MOSSAKA-hw3 example.

evalArgs :: (Show s, Hashable s, Ord s, Fixpoint s, PPrint s) => Knowledge s -> CStack s -> Expr s -> EvalST s (Expr s, [Expr s])
evalArgs γ stk e = go [] e 
  where
    go acc (EApp f e)
      = do f' <- evalOk γ stk f
           e' <- eval γ stk e
           go (e':acc) f'
    go acc e
      = (,acc) <$> eval γ stk e

-- | Minimal test case illustrating this `evalOk` hack is LH#tests/ple/pos/MossakaBug.hs
--   too tired & baffled to generate simple .fq version. TODO:nuke and rewrite PLE!
evalOk :: (Show s, Hashable s, Ord s, Fixpoint s, PPrint s) => Knowledge s -> CStack s -> Expr s -> EvalST s (Expr s)
evalOk γ stk@(_, Ok) e = eval γ stk e 
evalOk _ _           e = pure e 

{- 
evalArgs :: Knowledge -> CStack -> Expr s -> EvalST (Expr s, [Expr s])
evalArgs 
  | True  = evalArgsOLD 
  | False = evalArgsNEW 

evalArgsNEW :: Knowledge -> CStack -> Expr s -> EvalST (Expr s, [Expr s])
evalArgsNEW γ stk e = do 
    let (e1, es) = splitEApp e 
    e1' <- eval γ stk e1 
    es' <- mapM (eval γ stk) es 
    return (e1', es')

-}
    
evalApp :: (Show s, Fixpoint s, Ord s, Hashable s, PPrint s, Eq s) => Knowledge s -> CStack s -> Expr s -> (Expr s, [Expr s]) -> EvalST s (Expr s)
-- evalApp γ stk e (e1, es) = tracepp ("evalApp:END" ++ showpp (e1,es)) <$> (evalAppAc γ stk e (e1, es))
evalApp γ stk e (e1, es) = do 
  res     <- evalAppAc γ stk e (e1, es)
  let diff = (res /= (eApps e1 es))
  return   $ mytracepp ("evalApp:END:" ++ showpp diff) res 

evalAppAc :: (PPrint s, Hashable s, Ord s, Fixpoint s, Show s) => Knowledge s -> CStack s -> Expr s -> (Expr s, [Expr s]) -> EvalST s (Expr s)

{- MOSSAKA-} 
evalAppAc γ stk e (EVar f, [ex])
  | (EVar dc, es) <- splitEApp ex
  , Just simp <- L.find (\simp -> (smName simp == f) && (smDC simp == dc)) (knSims γ)
  , length (smArgs simp) == length es
  = do let msg    = "evalAppAc:ePop: " ++ showpp (f, dc, es)
       let ePopIf = mytracepp msg $ substPopIf (zip (smArgs simp) es) (smBody simp)
       e'    <- eval γ stk ePopIf 
       (e, "Rewrite -" ++ showpp f) ~> e'

evalAppAc γ stk _ (EVar f, es)
  -- we should move the lookupKnowledge stuff here into kmAms γ
  | Just eq <- L.find (( == f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq
  , length (eqArgs eq) == length es
  , f `notElem` syms bd               -- non-recursive equations << HACK! misses MUTUALLY RECURSIVE definitions! 
  , recurCS stk f 
  = do env   <- seSort <$> gets evEnv
       let ee = substEq env PopIf eq es bd
       assertSelectors γ ee 
       eval γ (pushCS stk f) ee 

evalAppAc γ stk _e (EVar f, es)
  | Just eq <- L.find ((== f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq
  , length (eqArgs eq) == length es   -- recursive equations
  , recurCS stk f 
  = do env      <- seSort <$> gets evEnv
       mytracepp ("EVAL-REC-APP" ++ showpp (stk, _e)) 
         <$> evalRecApplication γ (pushCS stk f) (eApps (EVar f) es) (substEq env Normal eq es bd)

evalAppAc _ _ _ (f, es)
  = return (eApps f es)

--------------------------------------------------------------------------------
-- | 'substEq' unfolds or instantiates an equation at a particular list of
--   argument values. We must also substitute the sort-variables that appear
--   as coercions. See tests/proof/ple1.fq
--------------------------------------------------------------------------------
substEq :: (Show s, Fixpoint s, Ord s, Hashable s, PPrint s) => SEnv s (Sort s) -> SubstOp -> Equation s -> [Expr s] -> Expr s -> Expr s
substEq env o eq es bd = substEqVal o eq es (substEqCoerce env eq es bd)

data SubstOp = PopIf | Normal

substEqVal :: (Hashable s, Ord s, Fixpoint s, Show s, Eq s) => SubstOp -> Equation s -> [Expr s] -> Expr s -> Expr s
substEqVal o eq es bd = case o of
    PopIf  -> substPopIf     xes  bd
    Normal -> subst (mkSubst xes) bd
  where
    xes    =  zip xs es
    xs     =  eqArgNames eq

substEqCoerce :: (Show s, Fixpoint s, PPrint s, Ord s, Hashable s) => SEnv s (Sort s) -> Equation s -> [Expr s] -> Expr s -> Expr s
substEqCoerce env eq es bd = Vis.applyCoSub coSub bd
  where 
    ts    = snd    <$> eqArgs eq
    sp    = panicSpan "mkCoSub"
    eTs   = sortExpr sp env <$> es
    coSub = mytracepp  ("substEqCoerce" ++ showpp (eqName eq, es, eTs, ts)) $ mkCoSub env eTs ts

mkCoSub :: (Ord s, Fixpoint s, Hashable s, PPrint s, Eq s) => SEnv s (Sort s) -> [Sort s] -> [Sort s] -> Vis.CoSub s
mkCoSub env eTs xTs = M.fromList [ (x, unite ys) | (x, ys) <- Misc.groupList xys ] 
  where
    unite ts    = mytracepp ("UNITE: " ++ showpp ts) $ Mb.fromMaybe (uError ts) (unifyTo1 senv ts)
    senv        = mkSearchEnv env
    uError ts   = panic ("mkCoSub: cannot build CoSub for " ++ showpp xys ++ " cannot unify " ++ showpp ts) 
    xys         = mytracepp "mkCoSubXXX" $ Misc.sortNub $ concat $ zipWith matchSorts _xTs _eTs
    (_xTs,_eTs) = mytracepp "mkCoSub:MATCH" $ (xTs, eTs)

matchSorts :: (Fixpoint s, Eq s, PPrint s) => Sort s -> Sort s -> [(Symbol s, Sort s)]
matchSorts s1 s2 = mytracepp  ("matchSorts :" ++ showpp (s1, s2)) $ go s1 s2
  where
    go (FObj x)      {-FObj-} y    = [(x, y)]
    go (FAbs _ t1)   (FAbs _ t2)   = go t1 t2
    go (FFunc s1 t1) (FFunc s2 t2) = go s1 s2 ++ go t1 t2
    go (FApp s1 t1)  (FApp s2 t2)  = go s1 s2 ++ go t1 t2
    go _             _             = []

--------------------------------------------------------------------------------
getEqBody :: (Eq s) => Equation s -> Maybe (Expr s)
getEqBody (Equ x xts b _ _)
  | Just (fxs, e) <- getEqBodyPred b
  , (EVar f, es)  <- splitEApp fxs
  , f == x
  , es == (EVar . fst <$> xts)
  = Just e
getEqBody _
  = Nothing

getEqBodyPred :: Expr s -> Maybe (Expr s, Expr s)
getEqBodyPred (PAtom Eq fxs e)
  = Just (fxs, e)
getEqBodyPred (PAnd ((PAtom Eq fxs e):_))
  = Just (fxs, e)
getEqBodyPred _
  = Nothing

eqArgNames :: Equation s -> [Symbol s]
eqArgNames = map fst . eqArgs

substPopIf :: (Show s, Fixpoint s, Ord s, Hashable s) => [(Symbol s, Expr s)] -> Expr s -> Expr s
substPopIf xes e = L.foldl' go e xes
  where
    go e (x, EIte b e1 e2) = EIte b (subst1 e (x, e1)) (subst1 e (x, e2))
    go e (x, ex)           = subst1 e (x, ex)

-- see [NOTE:Eval-Ite] the below is wrong; we need to guard other branches too. sigh.

evalRecApplication :: (Fixpoint s, PPrint s, Ord s, Eq s, Hashable s, Show s) => Knowledge s -> CStack s -> Expr s -> Expr s -> EvalST s (Expr s)
evalRecApplication γ stk e (EIte b e1 e2) = do
  contra <- {- mytracepp  ("CONTRA? " ++ showpp e) <$> -} liftIO (isValid γ PFalse)
  if contra
    then return e
    else do b' <- eval γ stk (mytracepp "REC-APP-COND" b) -- <<<<<<<<<<<<<<<<<<<<< MOSSAKA-LOOP?
            b1 <- liftIO (isValid γ b')
            if b1
              then addEquality γ e e1 >>
                   ({-# SCC "assertSelectors-1" #-} assertSelectors γ e1) >>
                   eval γ stk (mytracepp ("evalREC-1: " ++ showpp stk) e1) >>=
                   ((e, "App1: ") ~>)
              else do
                   b2 <- liftIO (isValid γ (PNot b'))
                   if b2
                      then addEquality γ e e2 >>
                           ({-# SCC "assertSelectors-2" #-} assertSelectors γ e2) >>
                           eval γ stk (mytracepp ("evalREC-2: " ++ showpp stk) e2) >>=
                           ((e, ("App2: " ++ showpp stk ) ) ~>)
                      else return e
evalRecApplication _ _ _ e
  = return e

addEquality :: Knowledge s -> Expr s -> Expr s -> EvalST s ()
addEquality γ e1 e2 =
  modify (\st -> st{evSequence = (makeLam γ e1, makeLam γ e2):evSequence st})

evalIte :: (Show s, Hashable s, Ord s, Fixpoint s, PPrint s) => Knowledge s -> CStack s -> Expr s -> Expr s -> Expr s -> Expr s -> EvalST s (Expr s)
evalIte γ stk e b e1 e2 = mytracepp "evalIte:END: " <$> 
                            evalIteAc γ stk e b e1 (mytracepp msg e2) 
  where 
    msg = "evalIte:BEGINS: " ++ showpp (stk, e) 


evalIteAc :: (Hashable s, Show s, PPrint s, Ord s, Fixpoint s) => Knowledge s -> CStack s -> Expr s -> Expr s -> Expr s -> Expr s -> EvalST s (Expr s)
evalIteAc γ stk e b e1 e2 
  = join $ evalIte' γ stk e b e1 e2 <$> liftIO (isValid γ b) <*> liftIO (isValid γ (PNot b))

evalIte' :: (Show s, Hashable s, Fixpoint s, Ord s, PPrint s) => Knowledge s -> CStack s -> Expr s -> Expr s -> Expr s -> Expr s -> Bool -> Bool -> EvalST s (Expr s)
evalIte' γ stk e _ e1 _ b _
  | b
  = do e' <- eval γ stk e1
       (e, "If-True of:" ++ showpp b)  ~> e'
evalIte' γ stk e _ _ e2 _ b'
  | b'
  = do e' <- eval γ stk e2
       (e, "If-False") ~> e'
evalIte' γ stk _ b e1 e2 _ _
  -- see [NOTE:Eval-Ite] #387 
  = EIte b <$> eval γ stk' e1 <*> eval γ stk' e2 
    where stk' = mytracepp "evalIte'" $ noRecurCS stk 

instance (Show s, Fixpoint s, Ord s, Hashable s) => Expression s (Symbol s, SortedReft s) where
  expr (x, RR _ (Reft (v, r))) = subst1 (expr r) (v, EVar x)

--------------------------------------------------------------------------------
-- | Knowledge (SMT Interaction)
--------------------------------------------------------------------------------
data Knowledge s = KN 
  { knSims    :: ![Rewrite s]           -- ^ Measure info, asserted for each new Ctor ('assertSelectors')
  , knAms     :: ![Equation s]          -- ^ (Recursive) function definitions, used for PLE
  , knContext :: SMT.Context s
  , knPreds   :: SMT.Context s -> [(Symbol s, Sort s)] -> Expr s -> IO Bool
  , knLams    :: [(Symbol s, Sort s)]
  }

isValid :: (Ord s, PPrint s, Fixpoint s) => Knowledge s -> Expr s -> IO Bool
isValid γ e = mytracepp ("isValid: " ++ showpp e) <$> 
                knPreds γ (knContext γ) (knLams γ) e

isProof :: (Fixpoint s, Eq s) => (a, SortedReft s) -> Bool 
isProof (_, RR s _) = showpp s == "Tuple"

knowledge :: (PPrint s, Show s, Fixpoint s, Ord s, Hashable s, SMT.SMTLIB2 s s) => Config -> SMT.Context s -> AxiomEnv s -> Knowledge s
knowledge cfg ctx aenv = KN 
  { knSims    = aenvSimpl aenv
  , knAms     = aenvEqs   aenv
  , knContext = ctx 
  , knPreds   = askSMT    cfg 
  , knLams    = [] 
  } 

-- | This creates the rewrite rule e1 -> e2, applied when:
-- 1. when e2 is a DataCon and can lead to further reductions
-- 2. when size e2 < size e1
initEqualities :: (Show s, Hashable s, Fixpoint s, PPrint s, Ord s) => SMT.Context s -> AxiomEnv s -> [(Symbol s, SortedReft s)] -> [(Expr s, Expr s)]
initEqualities ctx aenv es = concatMap (makeSimplifications (aenvSimpl aenv)) dcEqs
  where
    dcEqs                  = Misc.hashNub (Mb.catMaybes [getDCEquality senv e1 e2 | EEq e1 e2 <- atoms])
    atoms                  = splitPAnd =<< (expr <$> filter isProof es)
    senv                   = SMT.ctxSymEnv ctx

-- AT: Non-obvious needed invariant: askSMT True is always the 
-- totality-effecting one.
-- RJ: What does "totality effecting" mean? 

askSMT :: (SMT.SMTLIB2 s s, Hashable s, Ord s, Fixpoint s, Show s, PPrint s) => Config -> SMT.Context s -> [(Symbol s, Sort s)] -> Expr s -> IO Bool
askSMT cfg ctx bs e
  | isTautoPred  e     = return True
  | null (Vis.kvars e) = SMT.checkValidWithContext ctx [] PTrue e'
  | otherwise          = return False
  where 
    e'                 = toSMT cfg ctx bs e 

toSMT :: (PPrint s, Show s, Fixpoint s, Ord s, Hashable s, Eq s) => Config -> SMT.Context s -> [(Symbol s, Sort s)] -> Expr s -> Pred s
toSMT cfg ctx bs = defuncAny cfg senv . elaborate "makeKnowledge" (elabEnv bs)
  where
    elabEnv      = insertsSymEnv senv -- L.foldl' (\env (x, s) -> insertSymEnv x s env) senv
    senv         = SMT.ctxSymEnv ctx

makeSimplifications :: (Show s, Fixpoint s, Ord s, Hashable s) => [Rewrite s] -> (Symbol s, [Expr s], Expr s) -> [(Expr s, Expr s)]
makeSimplifications sis (dc, es, e)
     = go =<< sis
 where
   go (SMeasure f dc' xs bd)
     | dc == dc', length xs == length es
     = [(EApp (EVar f) e, subst (mkSubst $ zip xs es) bd)]
   go _
     = []

getDCEquality :: (Ord s, PPrint s, Fixpoint s, Hashable s, Eq s) => SymEnv s -> Expr s -> Expr s -> Maybe (Symbol s, [Expr s], Expr s)
getDCEquality senv e1 e2
  | Just dc1 <- f1
  , Just dc2 <- f2
  = if dc1 == dc2
      then Nothing
      else error ("isDCEquality on" ++ showpp e1 ++ "\n" ++ showpp e2)
  | Just dc1 <- f1
  = Just (dc1, es1, e2)
  | Just dc2 <- f2
  = Just (dc2, es2, e1)
  | otherwise
  = Nothing
  where
    (f1, es1) = Misc.mapFst (getDC senv) (splitEApp e1)
    (f2, es2) = Misc.mapFst (getDC senv) (splitEApp e2)

-- TODO: Stringy hacks
getDC :: (Eq s, Hashable s) => SymEnv s -> Expr s -> Maybe (Symbol s)
getDC senv (EVar x)
  | isUpperSymbol x && Mb.isNothing (symEnvTheory x senv)
  = Just x
getDC _ _
  = Nothing

isUpperSymbol :: Symbol s -> Bool
isUpperSymbol = isUpper . headSym . symbol . dropModuleNames 

dropModuleNames :: Symbol s -> Symbol s
dropModuleNames = FS . mungeNames (symbol . last) "." . symbol
  where
    mungeNames _ _ ""  = ""
    mungeNames f d s'@(symbolText -> s)
      | s' == tupConName = tupConName
      | otherwise        = f $ T.splitOn d $ stripParens s
    stripParens t = Mb.fromMaybe t ((T.stripPrefix "(" >=> T.stripSuffix ")") t)

--------------------------------------------------------------------------------
-- | Creating Measure Info
--------------------------------------------------------------------------------
-- AT@TODO do this for all reflected functions, not just DataCons

{- [NOTE:Datacon-Selectors] The 'assertSelectors' function
   insert measure information for every constructor that appears
   in the expression e.

   In theory, this is not required as the SMT ADT encoding takes
   care of it. However, in practice, some constructors, e.g. from
   GADTs cannot be directly encoded in SMT due to the lack of SMTLIB
   support for GADT. Hence, we still need to hang onto this code.

   See tests/proof/ple2.fq for a concrete example.
 -}

assertSelectors :: forall s. (Show s, Fixpoint s, Ord s, Hashable s, Eq s) => Knowledge s -> Expr s -> EvalST s ()
assertSelectors γ e = do
    sims <- aenvSimpl <$> gets _evAEnv
    -- cfg  <- gets evCfg
    -- _    <- foldlM (\_ s -> Vis.mapMExpr (go s) e) (mytracepp  "assertSelector" e) sims
    forM_ sims $ \s -> Vis.mapMExpr (go s) e
    return ()
  where
    go :: Rewrite s -> Expr s -> EvalST s (Expr s)
    go (SMeasure f dc xs bd) e@(EApp _ _)
      | (EVar dc', es) <- splitEApp e
      , dc == dc'
      , length xs == length es
      = do let e1 = EApp (EVar f) e
           let e2 = subst (mkSubst $ zip xs es) bd
           addEquality γ e1 e2
           return e
    go _ e
      = return e

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

withCtx :: (Ord s, Hashable s, Fixpoint s, PPrint s, Show s, SMT.SMTLIB2 s s) => Config -> FilePath -> SymEnv s -> (SMT.Context s -> IO a) -> IO a
withCtx cfg file env k = do
  ctx <- SMT.makeContextWithSEnv cfg file env
  _   <- SMT.smtPush ctx
  res <- k ctx
  _   <- SMT.cleanupContext ctx
  return res

(~>) :: (Ord s, PPrint s, Fixpoint s) => (Expr s, String) -> Expr s -> EvalST s (Expr s)
(e, _str) ~> e' = do
  let msg = "PLE: " ++ _str ++ showpp (e, e') 
  modify (\st -> st {evId = (mytracepp msg $ evId st) + 1})
  return e'

