-------------------------------------------------------------------------------
-- | This module defines a function to solve NNF constraints,
--   by reducing them to the standard FInfo. 
-------------------------------------------------------------------------------


{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}

module Language.Fixpoint.Horn.Solve (solveHorn, solve) where 

import qualified Data.HashMap.Strict            as M
import           Data.Hashable
import           Data.Binary
import qualified Data.List                      as L
import qualified Data.Tuple                     as Tuple 
import qualified Data.Maybe                     as Mb
import           Data.Either                    (partitionEithers)
import           Data.Void
import           System.Exit
import           GHC.Generics                   (Generic)
import           Control.DeepSeq
import qualified Language.Fixpoint.Solver       as Solver 
import qualified Language.Fixpoint.Misc         as Misc 
import qualified Language.Fixpoint.Parse        as Parse 
import qualified Language.Fixpoint.Types        as F
import           Language.Fixpoint.Smt.Types    (SMTLIB2)
import qualified Language.Fixpoint.Types.Config as F 
import qualified Language.Fixpoint.Horn.Types   as H 
import qualified Language.Fixpoint.Horn.Parse   as H 
import qualified Language.Fixpoint.Horn.Transformations as Tx
-- import qualified Language.Fixpoint.Smt.Interface as SI
import           System.Console.CmdArgs.Verbosity

----------------------------------------------------------------------------------
solveHorn :: F.Config -> IO ExitCode 
----------------------------------------------------------------------------------
solveHorn cfg = do
  (q, opts) <- Parse.parseFromFile H.hornP (F.srcFile cfg)

  -- If you want to set --eliminate=none, you better make it a pragma
  cfg <- if F.eliminate cfg == F.None
           then pure (cfg { F.eliminate =  F.Some })
           else pure cfg
  cfg <- F.withPragmas cfg opts

  r <- solve @Void cfg q
  Solver.resultExitCode (fst <$> r)

----------------------------------------------------------------------------------
eliminate :: (F.PPrint s, Hashable s, Ord s, F.Fixpoint s, Show s, F.PPrint a) => F.Config -> H.Query s a -> IO (H.Query s a) 
----------------------------------------------------------------------------------
eliminate cfg q
  | F.eliminate cfg == F.Existentials = do
    q <- Tx.solveEbs q
    -- b <- SI.checkValid cfg "/tmp/asdf.smt2" [] F.PTrue $ Tx.cstrToExpr side
    -- if b then print "checked side condition" else error "side failed"
    pure q
  | F.eliminate cfg == F.Horn = do
    let c = Tx.elim $ H.qCstr q
    whenLoud $ putStrLn "Horn Elim:"
    whenLoud $ putStrLn $ F.showpp c
    pure $ q { H.qCstr = c }
  | otherwise = pure q

----------------------------------------------------------------------------------
solve :: (Ord s, F.PPrint s, Eq s, F.Fixpoint s, SMTLIB2 s s, Binary s, Show s, Hashable s, NFData s, F.PPrint a, NFData a, F.Loc a, Show a, F.Fixpoint a) => F.Config -> H.Query s a 
       -> IO (F.Result s (Integer, a))
----------------------------------------------------------------------------------
solve cfg q = do
  let c = Tx.uniq $ Tx.flatten $ H.qCstr q
  whenLoud $ putStrLn "Horn Uniq:"
  whenLoud $ putStrLn $ F.showpp c
  q <- eliminate cfg ({- void $ -} q { H.qCstr = c })
  Solver.solve cfg (hornFInfo q)

hornFInfo :: (Hashable s, F.PPrint s, Ord s, F.Fixpoint s, Show s) => H.Query s a -> F.FInfo s a 
hornFInfo q    = mempty 
  { F.cm       = cs 
  , F.bs       = be2  
  , F.ebinds   = ebs
  , F.ws       = kvEnvWfCs kve 
  , F.quals    = H.qQuals q
  , F.gLits    = F.fromMapSEnv $ H.qCon q
  , F.dLits    = F.fromMapSEnv $ H.qDis q
  } 
  where 
    be0        = F.emptyBindEnv
    (be1, kve) = hornWfs   be0     (H.qVars q)
    (be2, ebs, cs) = hornSubCs be1 kve hCst 
    hCst       = H.qCstr q

----------------------------------------------------------------------------------
hornSubCs :: (Show s, F.Fixpoint s, Ord s, F.PPrint s, Eq s, Hashable s) => F.BindEnv s -> KVEnv s a -> H.Cstr s a 
          -> (F.BindEnv s, [F.BindId], M.HashMap F.SubcId (F.SubC s a)) 
----------------------------------------------------------------------------------
hornSubCs be kve c = (be', ebs, M.fromList (F.addIds cs)) 
  where
    (be', ebs, cs)      = goS kve F.emptyIBindEnv lhs0 be c 
    lhs0           = bindSortedReft kve H.dummyBind 

-- | @goS@ recursively traverses the NNF constraint to build up a list 
--   of the vanilla @SubC@ constraints.

goS :: (Hashable s, Eq s, F.PPrint s) => KVEnv s a -> F.IBindEnv -> F.SortedReft s -> F.BindEnv s -> H.Cstr s a 
    -> (F.BindEnv s, [F.BindId], [F.SubC s a])

goS kve env lhs be c = (be', mEbs, subcs)
  where
    (be', ecs) = goS' kve env lhs be c
    (mEbs, subcs) = partitionEithers ecs

goS' :: (F.PPrint s, Eq s, Hashable s) => KVEnv s a -> F.IBindEnv -> F.SortedReft s -> F.BindEnv s -> H.Cstr s a 
    -> (F.BindEnv s, [Either F.BindId (F.SubC s a)])
goS' kve env lhs be (H.Head p l) = (be, [Right subc])
  where 
    subc                        = F.mkSubC env lhs rhs Nothing [] l 
    rhs                         = updSortedReft kve lhs p 

goS' kve env lhs be (H.CAnd cs)  = (be', concat subcss)
  where 
    (be', subcss)               = L.mapAccumL (goS' kve env lhs) be cs 

goS' kve env _   be (H.All b c)  = (be'', subcs)
  where 
    (be'', subcs)               = goS' kve env' bSR be' c 
    (bId, be')                  = F.insertBindEnv (H.bSym b) bSR be 
    bSR                         = bindSortedReft kve b 
    env'                        = F.insertsIBindEnv [bId] env 

goS' kve env _   be (H.Any b c)  = (be'', Left bId : subcs)
  where 
    (be'', subcs)               = goS' kve env' bSR be' c 
    (bId, be')                  = F.insertBindEnv (H.bSym b) bSR be 
    bSR                         = bindSortedReft kve b 
    env'                        = F.insertsIBindEnv [bId] env 

bindSortedReft :: (Hashable s, Eq s, F.PPrint s) => KVEnv s a -> H.Bind s -> F.SortedReft s 
bindSortedReft kve (H.Bind x t p) = F.RR t (F.Reft (x, predExpr kve p))

updSortedReft :: (Hashable s, Eq s, F.PPrint s) => KVEnv s a -> F.SortedReft s -> H.Pred s -> F.SortedReft s 
updSortedReft kve (F.RR s (F.Reft (v, _))) p = F.RR s (F.Reft (v, predExpr kve p))  

predExpr :: (F.PPrint s, Eq s, Hashable s) => KVEnv s a -> H.Pred s -> F.Expr s 
predExpr kve        = go 
  where 
    go (H.Reft  e ) = e 
    go (H.Var k ys) = kvApp kve k ys
    go (H.PAnd  ps) = F.PAnd (go <$> ps)  

kvApp :: (Hashable s, Eq s, F.PPrint s) => KVEnv s a -> F.Symbol s -> [F.Symbol s] -> F.Expr s 
kvApp kve k ys = F.PKVar (F.KV k) su 
  where 
    su         = F.mkSubst (zip params (F.eVar <$> ys))
    params     = Mb.fromMaybe err1 $ kvParams <$> M.lookup k kve 
    err1       = F.panic ("Unknown Horn variable: " ++ F.showpp k) 

----------------------------------------------------------------------------------
hornWfs :: (Hashable s, Eq s) => F.BindEnv s -> [H.Var s a] -> (F.BindEnv s, KVEnv s a) 
----------------------------------------------------------------------------------
hornWfs be vars = (be', kve) 
  where 
    kve         = M.fromList [ (kname i, i) | i <- is ] 
    (be', is)   = L.mapAccumL kvInfo be vars 
    kname       = H.hvName . kvVar 

kvInfo :: F.BindEnv s -> H.Var s a -> (F.BindEnv s, KVInfo s a)
kvInfo be k       = (be', KVInfo k (fst <$> xts) wfc) 
  where 
    -- make the WfC 
    wfc           = F.WfC wenv wrft  (H.hvMeta k)
    wenv          = F.fromListIBindEnv ids
    wrft          = (x, t, F.KV (H.hvName k)) 
    -- add the binders
    (be', ids)    = L.mapAccumL insertBE be xts' 
    ((x,t), xts') = Misc.safeUncons "Horn var with no args" xts 
    -- make the parameters
    xts           = [ (hvarArg k i, t) | (t, i) <- zip (H.hvArgs k) [0..] ]

insertBE :: F.BindEnv s -> (F.Symbol s, F.Sort s) -> (F.BindEnv s, F.BindId)
insertBE be (x, t) = Tuple.swap $ F.insertBindEnv x (F.trueSortedReft t) be

----------------------------------------------------------------------------------
-- | Data types and helpers for manipulating information about KVars
----------------------------------------------------------------------------------
type KVEnv s a  = M.HashMap (F.Symbol s) (KVInfo s a)

data KVInfo s a = KVInfo 
  { kvVar    :: !(H.Var s a)
  , kvParams :: ![F.Symbol s]
  , kvWfC    :: !(F.WfC s a) 
  }
  deriving (Generic, Functor)

kvEnvWfCs :: (Hashable s, Eq s) => KVEnv s a -> M.HashMap (F.KVar s) (F.WfC s a)
kvEnvWfCs kve = M.fromList [ (F.KV k, kvWfC info) | (k, info) <- M.toList kve ]

hvarArg :: H.Var s a -> Int -> F.Symbol s 
hvarArg k i = F.FS $ F.intSymbol (F.suffixSymbol (F.symbol hvarPrefix) (F.symbol $ H.hvName k)) i 

hvarPrefix :: F.Symbol s 
hvarPrefix = F.FS $ F.symbol "nnf_arg" 
