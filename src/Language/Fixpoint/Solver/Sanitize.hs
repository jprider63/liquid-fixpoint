-- | Validate and Transform Constraints to Ensure various Invariants -------------------------
--   1. Each binder must be associated with a UNIQUE sort
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Fixpoint.Solver.Sanitize
  ( -- * Transform FInfo to enforce invariants
    sanitize

    -- * Sorts for each FixSymbol (move elsewhere)
  , symbolEnv

    -- * Remove substitutions K[x := e] where `x` is not in dom(K)
  , dropDeadSubsts
  ) where

import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Visitor (symConsts, isConcC, isKvarC, mapKVars, mapKVarSubsts)
import           Language.Fixpoint.SortCheck     (elaborate, applySorts, isFirstOrder)
-- import           Language.Fixpoint.Defunctionalize 
import qualified Language.Fixpoint.Misc                            as Misc
import qualified Language.Fixpoint.Types                           as F
import           Language.Fixpoint.Types.Config (Config, allowHO)
import qualified Language.Fixpoint.Types.Errors                    as E
import qualified Language.Fixpoint.Smt.Theories                    as Thy
import           Language.Fixpoint.Graph (kvEdges, CVertex (..))
import qualified Data.HashMap.Strict                               as M
import qualified Data.HashSet                                      as S
import           Data.Hashable
import qualified Data.List                                         as L
import qualified Data.Text                                         as T
import           Data.Maybe          (isNothing, mapMaybe)
import           Control.Monad       ((>=>))
import           Text.PrettyPrint.HughesPJ

type SanitizeM a = Either E.Error a

--------------------------------------------------------------------------------
sanitize :: (Hashable s, Ord s, Fixpoint s, Show s, PPrint s) => F.SInfo s a -> SanitizeM (F.SInfo s a)
--------------------------------------------------------------------------------
sanitize =    -- banIllScopedKvars
        --      Misc.fM dropAdtMeasures
        --      >=>
             Misc.fM dropFuncSortedShadowedBinders
         >=> Misc.fM sanitizeWfC
         >=> Misc.fM replaceDeadKvars
         >=> Misc.fM (dropDeadSubsts . restrictKVarDomain)
         >=>         banMixedRhs
         >=>         banQualifFreeVars
         >=>         banConstraintFreeVars
         >=> Misc.fM addLiterals


--------------------------------------------------------------------------------
-- | 'dropAdtMeasures' removes all the measure definitions that correspond to
--   constructor, selector or test names for declared datatypes, as these are
--   now "natively" handled by the SMT solver.
--------------------------------------------------------------------------------
_dropAdtMeasures :: (Hashable s, Eq s) => F.SInfo s a -> F.SInfo s a
_dropAdtMeasures si = si { F.ae = dropAdtAenv (F.ddecls si) (F.ae si) }

dropAdtAenv :: (Eq s, Hashable s) => [F.DataDecl s] -> F.AxiomEnv s -> F.AxiomEnv s
dropAdtAenv ds ae = ae { F.aenvSimpl = filter (not . isAdt) (F.aenvSimpl ae) }
  where
    isAdt         = (`S.member` adtSyms) . F.smName
    adtSyms       = adtSymbols ds

adtSymbols :: (Hashable s, Eq s) => [F.DataDecl s] -> S.HashSet (F.Symbol s)
adtSymbols = S.fromList . map fst . concatMap Thy.dataDeclSymbols

--------------------------------------------------------------------------------
-- | `addLiterals` traverses the constraints to find (string) literals that
--   are then added to the `dLits` field.
--------------------------------------------------------------------------------
addLiterals :: (Eq s, Hashable s) => F.SInfo s a -> F.SInfo s a
--------------------------------------------------------------------------------
addLiterals si = si { F.dLits = F.unionSEnv (F.dLits si) lits'
                    , F.gLits = F.unionSEnv (F.gLits si) lits'
                    }
  where
    lits'      = M.fromList [ (F.FS $ F.symbol x, F.strSort) | x <- symConsts si ]

--------------------------------------------------------------------------------
-- | See issue liquid-fixpoint issue #230. This checks that whenever we have,
--      G1        |- K.su1
--      G2, K.su2 |- rhs
--   then
--      G1 \cap G2 \subseteq wenv(k)
--------------------------------------------------------------------------------
_banIllScopedKvars :: (PPrint s, Show s, Fixpoint s, Ord s, Hashable s, Eq s) => F.SInfo s a ->  SanitizeM (F.SInfo s a)
--------------------------------------------------------------------------------
_banIllScopedKvars si = Misc.applyNonNull (Right si) (Left . badKs) errs
  where
    errs              = concatMap (checkIllScope si kDs) ks
    kDs               = kvarDefUses si
    ks                = filter notKut $ M.keys (F.ws si)
    notKut            = not . (`F.ksMember` F.kuts si)

badKs :: (PPrint s, PPrint s) => [(F.KVar s, F.SubcId, F.SubcId, F.IBindEnv)] -> F.Error
badKs = E.catErrors . map E.errIllScopedKVar

type KvConstrM s = M.HashMap (F.KVar s) [Integer]
type KvDefs s    = (KvConstrM s, KvConstrM s)

checkIllScope :: (Hashable s, Eq s) => F.SInfo s a -> KvDefs s -> F.KVar s -> [(F.KVar s, F.SubcId, F.SubcId, F.IBindEnv)]
checkIllScope si (inM, outM) k = mapMaybe (uncurry (isIllScope si k)) ios
  where
    ios                        = [(i, o) | i <- ins, o <- outs, i /= o ]
    ins                        = M.lookupDefault [] k inM
    outs                       = M.lookupDefault [] k outM

isIllScope :: (Eq s, Hashable s) => F.SInfo s a -> F.KVar s -> F.SubcId -> F.SubcId -> Maybe (F.KVar s, F.SubcId, F.SubcId, F.IBindEnv)
isIllScope si k inI outI
  | F.nullIBindEnv badXs = Nothing
  | otherwise            = Just (k, inI, outI, badXs)
  where
    badXs                = F.diffIBindEnv commonXs kXs
    kXs                  = {- F.tracepp ("kvarBinds " ++ show k) $ -} kvarBinds si k
    commonXs             = F.intersectionIBindEnv inXs outXs
    inXs                 = subcBinds si inI
    outXs                = subcBinds si outI

subcBinds :: F.SInfo s a -> F.SubcId -> F.IBindEnv
subcBinds si i = F._cenv $ F.cm si M.! i

kvarBinds :: (Hashable s, Eq s) => F.SInfo s a -> F.KVar s -> F.IBindEnv
kvarBinds si = F.wenv . (F.ws si M.!)

kvarDefUses :: (Ord s, Fixpoint s, Show s, Hashable s) => F.SInfo s a -> KvDefs s
kvarDefUses si = (Misc.group ins, Misc.group outs)
  where
    es         = kvEdges si
    outs       = [(k, o) | (KVar k, Cstr o) <- es ]
    ins        = [(k, i) | (Cstr i, KVar k) <- es ]

--------------------------------------------------------------------------------
-- | `dropDeadSubsts` removes dead `K[x := e]` where `x` NOT in the domain of K.
--------------------------------------------------------------------------------
dropDeadSubsts :: (Hashable s, Eq s) => F.SInfo s a -> F.SInfo s a
dropDeadSubsts si = mapKVarSubsts (F.filterSubst . f) si
  where
    kvsM          = M.mapWithKey (\k _ -> kvDom k) (F.ws si)
    kvDom         = S.fromList . F.kvarDomain si
    f k x _       = S.member x (M.lookupDefault mempty k kvsM)

--------------------------------------------------------------------------------
-- | `restrictKVarDomain` updates the kvar-domains in the wf constraints
--   to a subset of the original binders, where we DELETE the parameters
--   `x` which appear in substitutions of the form `K[x := y]` where `y`
--   is not in the env.
--------------------------------------------------------------------------------
restrictKVarDomain :: (Hashable s, Ord s, Fixpoint s) => F.SInfo s a -> F.SInfo s a
restrictKVarDomain si = si { F.ws = M.mapWithKey (restrictWf kvm) (F.ws si) }
  where
    kvm               = safeKvarEnv si

-- | `restrictWf kve k w` restricts the env of `w` to the parameters in `kve k`.
restrictWf :: (Hashable s, Eq s) => KvDom s -> F.KVar s -> F.WfC s a -> F.WfC s a
restrictWf kve k w = w { F.wenv = F.filterIBindEnv f (F.wenv w) }
  where
    f i            = S.member i kis
    kis            = S.fromList [ i | (_, i) <- F.toListSEnv kEnv ]
    kEnv           = M.lookupDefault mempty k kve

-- | `safeKvarEnv` computes the "real" domain of each kvar, which is
--   a SUBSET of the input domain, in which we KILL the parameters
--   `x` which appear in substitutions of the form `K[x := y]`
--   where `y` is not in the env.

type KvDom   s  = M.HashMap (F.KVar s) (F.SEnv s F.BindId)
type KvBads  s  = M.HashMap (F.KVar s) [F.Symbol s]

safeKvarEnv :: (Fixpoint s, Ord s, Hashable s, Eq s) => F.SInfo s a -> KvDom s
safeKvarEnv si = L.foldl' (dropKvarEnv si) env0 cs
  where
    cs         = M.elems  (F.cm si)
    env0       = initKvarEnv si

dropKvarEnv :: (Hashable s, Ord s, Fixpoint s) => F.SInfo s a -> KvDom s -> F.SimpC s a -> KvDom s
dropKvarEnv si kve c = M.mapWithKey (dropBadParams kBads) kve
  where
    kBads            = badParams si c

dropBadParams :: (Hashable s, Eq s) => KvBads s -> F.KVar s -> F.SEnv s F.BindId -> F.SEnv s F.BindId
dropBadParams kBads k kEnv = L.foldl' (flip F.deleteSEnv) kEnv xs
  where
    xs                     = M.lookupDefault mempty k kBads

badParams :: (Fixpoint s, Ord s, Hashable s, Eq s) => F.SInfo s a -> F.SimpC s a -> M.HashMap (F.KVar s) [F.Symbol s]
badParams si c = Misc.group bads
  where
    bads       = [ (k, x) | (v, k, F.Su su) <- subcKSubs xsrs c
                          , let vEnv = maybe sEnv (`S.insert` sEnv) v
                          , (x, e)          <- M.toList su
                          , badArg vEnv e
                 ]
    sEnv       = S.fromList (fst <$> xsrs)
    xsrs       = F.envCs (F.bs si) (F.senv c)

badArg :: (Hashable s, Eq s) => S.HashSet (F.Symbol s) -> F.Expr s -> Bool
badArg sEnv (F.EVar y) = not (y `S.member` sEnv)
badArg _    _          = True

type KSub s = (Maybe (F.Symbol s), F.KVar s, F.Subst s)

subcKSubs :: (Ord s, Fixpoint s) => [(F.Symbol s, F.SortedReft s)] -> F.SimpC s a -> [KSub s]
subcKSubs xsrs c = rhs ++ lhs
  where
    lhs          = [ (Just v, k, su) | (_, sr) <- xsrs
                                     , let rs   = F.reftConjuncts (F.sr_reft sr)
                                     , F.Reft (v, F.PKVar k su) <- rs
                   ]
    rhs          = [(Nothing, k, su) | F.PKVar k su <- [F.crhs c]]


initKvarEnv :: (Eq s, Hashable s) => F.SInfo s a -> KvDom s
initKvarEnv si = initEnv si <$> F.ws si

initEnv :: (Hashable s, Eq s) => F.SInfo s a -> F.WfC s a -> F.SEnv s F.BindId
initEnv si w = F.fromListSEnv [ (bind i, i) | i <- is ]
  where
    is       = F.elemsIBindEnv $ F.wenv w
    bind i   = fst (F.lookupBindEnv i be)
    be       = F.bs si

--------------------------------------------------------------------------------
-- | check that no constraint has free variables (ignores kvars)
--------------------------------------------------------------------------------
banConstraintFreeVars :: (PPrint s, Ord s, Show s, Fixpoint s, Eq s, Hashable s) => F.SInfo s a -> SanitizeM (F.SInfo s a)
banConstraintFreeVars fi0 = Misc.applyNonNull (Right fi0) (Left . badCs) bads
  where
    fi      = mapKVars (const $ Just F.PTrue) fi0
    bads    = [(c, fs) | c <- M.elems $ F.cm fi, Just fs <- [cNoFreeVars fi k c]]
    k       = known fi

known :: (Hashable s, Eq s) => F.SInfo s a -> F.Symbol s -> Bool
known fi  = \x -> F.memberSEnv x lits || F.memberSEnv x prims
  where
    lits  = F.gLits fi
    prims = Thy.theorySymbols . F.ddecls $ fi

cNoFreeVars :: (Fixpoint s, Show s, Ord s, Hashable s, Eq s) => F.SInfo s a -> (F.Symbol s -> Bool) -> F.SimpC s a -> Maybe [F.Symbol s]
cNoFreeVars fi known c = if S.null fv then Nothing else Just (S.toList fv)
  where
    be   = F.bs fi
    ids  = F.elemsIBindEnv $ F.senv c
    cDom = [fst $ F.lookupBindEnv i be | i <- ids]
    cRng = concat [S.toList . F.reftFreeVars . F.sr_reft . snd $ F.lookupBindEnv i be | i <- ids]
    fv   = (`Misc.nubDiff` cDom) . filter (not . known) $ cRng 

badCs :: (PPrint s) => Misc.ListNE (F.SimpC s a, [F.Symbol s]) -> E.Error
badCs = E.catErrors . map (E.errFreeVarInConstraint . Misc.mapFst F.subcId)


--------------------------------------------------------------------------------
-- | check that no qualifier has free variables
--------------------------------------------------------------------------------
banQualifFreeVars :: (PPrint s, Show s, Fixpoint s, Ord s, Hashable s, Eq s) => F.SInfo s a -> SanitizeM (F.SInfo s a)
--------------------------------------------------------------------------------
banQualifFreeVars fi = Misc.applyNonNull (Right fi) (Left . badQuals) bads
  where
    bads    = [ (q, xs) | q <- F.quals fi, let xs = free q, not (null xs) ]
    free q  = filter (not . isLit) (F.syms q) 
    isLit x = F.memberSEnv x (F.gLits fi) 
    -- lits    = fst <$> F.toListSEnv (F.gLits fi)
    -- free q  = S.toList $ F.syms (F.qBody q) `nubDiff` (lits ++ F.prims ++ F.syms (F.qpSym <$> F.qParams q))

badQuals     :: (PPrint s) => Misc.ListNE (F.Qualifier s, Misc.ListNE (F.Symbol s)) -> E.Error
badQuals bqs = E.catErrors [ E.errFreeVarInQual q xs | (q, xs) <- bqs]


--------------------------------------------------------------------------------
-- | check that each constraint has RHS of form [k1,...,kn] or [p]
--------------------------------------------------------------------------------
banMixedRhs :: (Ord s, Fixpoint s, PPrint s, Eq s) => F.SInfo s a -> SanitizeM (F.SInfo s a)
--------------------------------------------------------------------------------
banMixedRhs fi = Misc.applyNonNull (Right fi) (Left . badRhs) bads
  where
    ics        = M.toList $ F.cm fi
    bads       = [(i, c) | (i, c) <- ics, not $ isOk c]
    isOk c     = isKvarC c || isConcC c

badRhs :: (PPrint s, Fixpoint s, Ord s) => Misc.ListNE (Integer, F.SimpC s a) -> E.Error
badRhs = E.catErrors . map badRhs1

badRhs1 :: (Ord s, Fixpoint s, PPrint s) => (Integer, F.SimpC s a) -> E.Error
badRhs1 (i, c) = E.err E.dummySpan $ vcat [ "Malformed RHS for constraint id" <+> pprint i
                                          , nest 4 (pprint (F.crhs c)) ]

--------------------------------------------------------------------------------
-- | symbol |-> sort for EVERY variable in the SInfo s; 'symbolEnv' can ONLY be
--   called with **sanitized** environments (post the uniqification etc.) or
--   else you get duplicate sorts and other such errors.
--   We do this peculiar dance with `env0` to extract the apply-sorts from the 
--   function definitions inside the `AxiomEnv` which cannot be elaborated as 
--   it makes it hard to actually find the fundefs within (breaking PLE.)
--------------------------------------------------------------------------------
symbolEnv :: (Show s, Ord s, Fixpoint s, PPrint s, Hashable s) => Config -> F.SInfo s a -> F.SymEnv s
symbolEnv cfg si = F.symEnv sEnv tEnv ds (F.dLits si) (ts ++ ts')
  where
    ts'          = applySorts ae' 
    ae'          = elaborate (F.atLoc E.dummySpan "symbolEnv") env0 (F.ae si)
    env0         = F.symEnv sEnv tEnv ds (F.dLits si) ts
    tEnv         = Thy.theorySymbols ds
    ds           = F.ddecls si
    ts           = Misc.hashNub (applySorts si ++ [t | (_, t) <- F.toListSEnv sEnv])
    sEnv         = (F.tsSort <$> tEnv) `mappend` (F.fromListSEnv xts)
    xts          = symbolSorts cfg si


symbolSorts :: (Hashable s, PPrint s, Fixpoint s, Ord s) => Config -> F.GInfo s c a -> [(F.Symbol s, F.Sort s)]
symbolSorts cfg fi = either E.die id $ symbolSorts' cfg fi

symbolSorts' :: (Ord s, Fixpoint s, PPrint s, Hashable s, Eq s) => Config -> F.GInfo s c a -> SanitizeM [(F.Symbol s, F.Sort s)]
symbolSorts' cfg fi  = (normalize . compact . (defs ++)) =<< bindSorts fi
  where
    normalize       = fmap (map (unShadow txFun dm))
    dm              = M.fromList defs
    defs            = F.toListSEnv . F.gLits $ fi
    txFun           
      | True        = id
      | allowHO cfg = id
      | otherwise   = defuncSort

unShadow :: (Hashable s, Eq s) => (F.Sort s -> F.Sort s) -> M.HashMap (F.Symbol s) a -> (F.Symbol s, F.Sort s) -> (F.Symbol s, F.Sort s)
unShadow tx dm (x, t)
  | M.member x dm  = (x, t)
  | otherwise      = (x, tx t)

defuncSort :: (Eq s) => F.Sort s -> F.Sort s
defuncSort (F.FFunc {}) = F.funcSort
defuncSort t            = t

compact :: (PPrint s, Fixpoint s, Ord s, Eq s, Hashable s) => [(F.Symbol s, F.Sort s)] -> Either E.Error [(F.Symbol s, F.Sort s)]
compact xts
  | null bad  = Right [(x, t) | (x, [t]) <- ok ]
  | otherwise = Left $ dupBindErrors bad'
  where
    bad'      = [(x, (, []) <$> ts) | (x, ts) <- bad]
    (bad, ok) = L.partition multiSorted . binds $ xts
    binds     = M.toList . M.map Misc.sortNub . Misc.group

--------------------------------------------------------------------------------
bindSorts  :: (PPrint s, Fixpoint s, Eq s, Hashable s) => F.GInfo s c a -> Either E.Error [(F.Symbol s, F.Sort s)]
--------------------------------------------------------------------------------
bindSorts fi
  | null bad   = Right [ (x, t) | (x, [(t, _)]) <- ok ]
  | otherwise  = Left $ dupBindErrors [ (x, ts) | (x, ts) <- bad]
  where
    (bad, ok)  = L.partition multiSorted . binds $ fi
    binds      = symBinds . F.bs


multiSorted :: (x, [t]) -> Bool
multiSorted = (1 <) . length . snd

dupBindErrors :: (Fixpoint s, Eq s, PPrint s) => [(F.Symbol s, [(F.Sort s, [F.BindId] )])] -> E.Error
dupBindErrors = foldr1 E.catError . map dbe
  where
   dbe (x, y) = E.err E.dummySpan $ vcat [ "Multiple sorts for" <+> pprint x
                                         , nest 4 (pprint y) ]

--------------------------------------------------------------------------------
symBinds  :: (Hashable s, Eq s) => F.BindEnv s -> [SymBinds s]
--------------------------------------------------------------------------------
symBinds  = {- THIS KILLS ELEM: tracepp "symBinds" . -}
            M.toList
          . M.map Misc.groupList
          . Misc.group
          . binders

type SymBinds s = (F.Symbol s, [(F.Sort s, [F.BindId])])

binders :: F.BindEnv s -> [(F.Symbol s, (F.Sort s, F.BindId))]
binders be = [(x, (F.sr_sort t, i)) | (i, x, t) <- F.bindEnvToList be]


--------------------------------------------------------------------------------
-- | Drop func-sorted `bind` that are shadowed by `constant` (if same type, else error)
--------------------------------------------------------------------------------
dropFuncSortedShadowedBinders :: (Hashable s, Eq s) => F.SInfo s a -> F.SInfo s a
--------------------------------------------------------------------------------
dropFuncSortedShadowedBinders fi = dropBinders ok (const True) fi
  where
    ok x t  = (M.member x defs) ==> (F.allowHO fi || isFirstOrder t)
    defs    = M.fromList $ F.toListSEnv $ F.gLits fi

(==>) :: Bool -> Bool -> Bool
p ==> q = not p || q

--------------------------------------------------------------------------------
-- | Drop irrelevant binders from WfC Environments
--------------------------------------------------------------------------------
sanitizeWfC :: (Eq s, Hashable s) => F.SInfo s a -> F.SInfo s a
sanitizeWfC si = si { F.ws = ws' }
  where
    ws'        = deleteWfCBinds drops <$> F.ws si
    (_,drops)  = filterBindEnv keepF   $  F.bs si
    keepF      = conjKF [nonConstantF si, nonFunctionF si, _nonDerivedLH]
    -- drops   = F.tracepp "sanitizeWfC: dropping" $ L.sort drops'

conjKF :: [KeepBindF s] -> KeepBindF s
conjKF fs x t = and [f x t | f <- fs]

-- | `nonDerivedLH` keeps a bind x if it does not start with `$` which is used
--   typically for names that are automatically "derived" by GHC (and which can)
--   blow up the environments thereby clogging instantiation, etc.
--   NOTE: This is an LH specific hack and should be moved there.

_nonDerivedLH :: KeepBindF s
_nonDerivedLH x _ = not . T.isPrefixOf "$" . last . T.split ('.' ==) . F.symbolText . F.symbol $ x

nonConstantF :: (Hashable s, Eq s) => F.SInfo s a -> KeepBindF s
nonConstantF si = \x _ -> not (x `F.memberSEnv` cEnv)
  where
    cEnv        = F.gLits si

nonFunctionF :: F.SInfo s a -> KeepBindF s
nonFunctionF si
  | F.allowHO si    = \_ _ -> True
  | otherwise       = \_ t -> isNothing (F.functionSort t)

--------------------------------------------------------------------------------
-- | Generic API for Deleting Binders from FInfo
--------------------------------------------------------------------------------
dropBinders :: (Hashable s, Eq s) => KeepBindF s -> KeepSortF s -> F.SInfo s a -> F.SInfo s a
--------------------------------------------------------------------------------
dropBinders f g fi  = fi { F.bs    = bs'
                         , F.cm    = cm'
                         , F.ws    = ws'
                         , F.gLits = lits' }
  where
    -- discards        = diss
    (bs', discards) = filterBindEnv f $ F.bs fi
    cm'             = deleteSubCBinds discards   <$> F.cm fi
    ws'             = deleteWfCBinds  discards   <$> F.ws fi
    lits'           = F.filterSEnv g (F.gLits fi)

type KeepBindF s = F.Symbol s -> F.Sort s -> Bool
type KeepSortF s = F.Sort s -> Bool

deleteSubCBinds :: [F.BindId] -> F.SimpC s a -> F.SimpC s a
deleteSubCBinds bs sc = sc { F._cenv = foldr F.deleteIBindEnv (F.senv sc) bs }

deleteWfCBinds :: [F.BindId] -> F.WfC s a -> F.WfC s a
deleteWfCBinds bs wf = wf { F.wenv = foldr F.deleteIBindEnv (F.wenv wf) bs }

filterBindEnv :: KeepBindF s -> F.BindEnv s -> (F.BindEnv s, [F.BindId])
filterBindEnv f be  = (F.bindEnvFromList keep, discard')
  where
    (keep, discard) = L.partition f' $ F.bindEnvToList be
    discard'        = Misc.fst3     <$> discard
    f' (_, x, t)    = f x (F.sr_sort t)


---------------------------------------------------------------------------
-- | Replace KVars that do not have a WfC with PFalse
---------------------------------------------------------------------------
replaceDeadKvars :: (Show s, Hashable s, Fixpoint s, Ord s) => F.SInfo s a -> F.SInfo s a
---------------------------------------------------------------------------
replaceDeadKvars fi = mapKVars go fi
  where
    go k | k `M.member` F.ws fi = Nothing
         | otherwise            = Just F.PFalse
