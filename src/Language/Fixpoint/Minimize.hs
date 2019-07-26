-- | This module implements a "delta-debugging" based query minimizer.
--   Exported clients of that minimizer include one that attempts to
--   shrink UNSAT queries down to a minimal subset of constraints,
--   one that shrinks SAT queries down to a minimal subset of qualifiers,
--   and one that shrinks SAT queries down to a minimal subset of KVars
--   (replacing all others by True).

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Language.Fixpoint.Minimize ( minQuery, minQuals, minKvars ) where

import qualified Data.HashMap.Strict                as M
import           Data.Hashable
import           Data.Binary                        (Binary)
import           Control.Monad                      (filterM)
import           Language.Fixpoint.Types.Visitor    (mapKVars)
import           Language.Fixpoint.Types.Config     (Config (..), queryFile)
import           Language.Fixpoint.Misc             (safeHead)
import           Language.Fixpoint.Utils.Files      hiding (Result)
import           Language.Fixpoint.Graph
import           Language.Fixpoint.Types
import           Control.DeepSeq

---------------------------------------------------------------------------
-- polymorphic delta debugging implementation
---------------------------------------------------------------------------
deltaDebug :: Bool -> Oracle s a c -> Config -> Solver s a -> FInfo s a -> [c] -> [c] -> IO [c]
deltaDebug min testSet cfg solve finfo set r = do
  let (s1, s2) = splitAt (length set `div` 2) set
  if length set == 1
    then deltaDebug1 min testSet cfg solve finfo set r
    else do
      test1 <- testSet cfg solve finfo (s1 ++ r)
      if test1
        then deltaDebug min testSet cfg solve finfo s1 r
        else do
          test2 <- testSet cfg solve finfo (s2 ++ r)
          if test2
            then deltaDebug min testSet cfg solve finfo s2 r
            else do
              d1 <- deltaDebug min testSet cfg solve finfo s1 (s2 ++ r)
              d2 <- deltaDebug min testSet cfg solve finfo s2 (d1 ++ r)
              return (d1 ++ d2)

deltaDebug1 :: Bool -> (a -> b -> c -> d -> IO Bool)
            -> a -> b -> c -> [e] -> d
            -> IO [e]
deltaDebug1 True  _       _   _     _     set _ = return set
deltaDebug1 False testSet cfg solve finfo set r = do
  test <- testSet cfg solve finfo r
  if test then return [] else return set

type Oracle s a c = (Config -> Solver s a -> FInfo s a -> [c] -> IO Bool)

commonDebug :: (Binary s, Hashable s, Show s, Ord s, Fixpoint s, PPrint s, NFData a, Fixpoint a) => (FInfo s a -> [c])
                                      -> (FInfo s a -> [c] -> FInfo s a)
                                      -> (Result s (Integer, a) -> Bool)
                                      -> Bool
                                      -> Config
                                      -> Solver s a
                                      -> FInfo s a
                                      -> Ext
                                      -> (FInfo s a -> [c] -> String)
                                      -> IO (Result s (Integer, a))
commonDebug init updateFi checkRes min cfg solve fi ext formatter = do
  let cs0 = init fi
  let oracle = mkOracle updateFi checkRes
  cs <- deltaDebug min oracle cfg solve fi cs0 []
  let minFi = updateFi fi cs
  saveQuery (addExt ext cfg) minFi
  putStrLn $ formatter fi cs
  return mempty

---------------------------------------------------------------------------
minQuery :: (Binary s, PPrint s, Show s, Hashable s, Ord s, Fixpoint s, NFData a, Fixpoint a) => Config -> Solver s a -> FInfo s a
         -> IO (Result s (Integer, a))
---------------------------------------------------------------------------
minQuery cfg solve fi = do
  let cfg'  = cfg { minimize = False }
  let fis   = partition' Nothing fi
  failFis  <- filterM (fmap (not . isSafe) . solve cfg') fis
  let failFi = safeHead "--minimize can only be called on UNSAT fq" failFis
  let format _ cs = "Minimized Constraints: " ++ show (fst <$> cs)
  let update fi cs = fi { cm = M.fromList cs }
  commonDebug (M.toList . cm) update (not . isSafe) True cfg' solve failFi Min format

---------------------------------------------------------------------------
minQuals :: (Binary s, PPrint s, Fixpoint s, Ord s, Show s, Hashable s, NFData a, Fixpoint a) => Config -> Solver s a -> FInfo s a
         -> IO (Result s (Integer, a))
---------------------------------------------------------------------------
minQuals cfg solve fi = do
  let cfg'  = cfg { minimizeQs = False }
  let format fi qs = "Required Qualifiers: " ++ show (length qs)
                  ++ "; Total Qualifiers: "  ++ show (length $ quals fi)
  let update fi qs = fi { quals = qs }
  commonDebug quals update isSafe False cfg' solve fi MinQuals format

---------------------------------------------------------------------------
minKvars :: (Binary s, PPrint s, Hashable s, Ord s, Fixpoint s, Show s, NFData a, Fixpoint a) => Config -> Solver s a -> FInfo s a
         -> IO (Result s (Integer, a))
---------------------------------------------------------------------------
minKvars cfg solve fi = do
  let cfg'  = cfg { minimizeKs = False }
  let format fi ks = "Required KVars: " ++ show (length ks)
                  ++ "; Total KVars: "  ++ show (length $ ws fi)
  commonDebug (M.keys . ws) removeOtherKs isSafe False cfg' solve fi MinKVars format

removeOtherKs :: forall s a. (Show s, Fixpoint s, Ord s, Hashable s) => FInfo s a -> [KVar s] -> FInfo s a
removeOtherKs fi0 ks = fi1 { ws = ws', cm = cm' }
  where
    fi1 = mapKVars go fi0
    go k | k `elem` ks = Nothing
         | otherwise   = Just PTrue
    ws' = M.filterWithKey (\k _ -> k `elem` ks) $ ws fi1
    cm' = M.filter (isNonTrivial @s @_ . srhs) $ cm fi1

---------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------
addExt :: Ext -> Config -> Config
addExt ext cfg = cfg { srcFile = queryFile ext cfg }

mkOracle :: (NFData a, Fixpoint a) => (FInfo s a -> [c] -> FInfo s a)
                                   -> (Result s (Integer, a) -> Bool)
                                   -> Oracle s a c
mkOracle updateFi checkRes cfg solve fi qs = do
  let fi' = updateFi fi qs
  res <- solve cfg fi'
  return $ checkRes res
