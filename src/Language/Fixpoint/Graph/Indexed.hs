--------------------------------------------------------------------------------
-- | This module implements Indexed KV Graphs,
--   a representation of the KVGraph with a fast
--   succ, pred lookup
--------------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings #-}

module Language.Fixpoint.Graph.Indexed (
  -- * (Abstract) Indexed Graphs
    IKVGraph (..)

  -- * Constructor
  , edgesIkvg

  -- * Destructor
  , ikvgEdges

  -- * Modify
  , addLinks
  , delNodes

  -- * Lookup
  , getSuccs
  , getPreds
  ) where

import           Language.Fixpoint.Graph.Types
import qualified Data.HashSet              as S
import qualified Data.HashMap.Strict       as M
import qualified Data.List as L
import           Data.Hashable (Hashable)

--------------------------------------------------------------------------------
-- | `IKVGraph` is representation of the KVGraph with a fast succ, pred lookup
--------------------------------------------------------------------------------

data IKVGraph s = IKVGraph
  { igSucc :: !(M.HashMap (CVertex s) (S.HashSet (CVertex s)))  -- ^ out-edges of a `CVertex`
  , igPred :: !(M.HashMap (CVertex s) (S.HashSet (CVertex s)))  -- ^ in-edges  of a `CVertex`
  } deriving (Show)


addLinks :: (Hashable s, Eq s) => IKVGraph s -> [CEdge s] -> IKVGraph s
addLinks = L.foldl' addLink

addLink :: (Eq s, Hashable s) => IKVGraph s -> CEdge s -> IKVGraph s
addLink g (u, v) = addSucc (u, v) . addPred (u, v) $ g

delNodes :: (Hashable s, Eq s) => IKVGraph s -> [CVertex s] -> IKVGraph s
delNodes = L.foldl' delNode

delNode :: (Eq s, Hashable s) => IKVGraph s -> CVertex s -> IKVGraph s
delNode g v = delVtx v . txMany delSucc uvs . txMany delPred vws $ g
  where
    uvs     = [ (u, v) | u <- getPreds g v ]
    vws     = [ (v, w) | w <- getSuccs g v ]

edgesIkvg :: (Eq s, Hashable s) => [CEdge s] -> IKVGraph s
edgesIkvg = addLinks empty

ikvgEdges :: IKVGraph s -> [CEdge s]
ikvgEdges g = [ (u, v) | (u, vs) <- M.toList (igSucc g), v <- S.toList vs]

getSuccs :: (Hashable s, Eq s) => IKVGraph s -> CVertex s -> [CVertex s]
getSuccs g u = S.toList $ M.lookupDefault S.empty u (igSucc g)

getPreds :: (Hashable s, Eq s) => IKVGraph s -> CVertex s -> [CVertex s]
getPreds g v = S.toList $ M.lookupDefault S.empty v (igPred g)

--------------------------------------------------------------------------------
empty :: IKVGraph s
empty = IKVGraph M.empty M.empty

txMany :: (a -> b -> b) -> [a] -> b -> b
txMany op es g = L.foldl' (flip op) g es

addSucc :: (Hashable s, Eq s) => CEdge s -> IKVGraph s -> IKVGraph s
addSucc (u, v) g = g { igSucc = inserts u v (igSucc g) }

addPred :: (Hashable s, Eq s) => CEdge s -> IKVGraph s -> IKVGraph s
addPred (u, v) g = g { igPred = inserts v u (igPred g) }

delSucc :: (Hashable s, Eq s) => CEdge s -> IKVGraph s -> IKVGraph s
delSucc (u, v) g = g { igSucc = removes u v (igSucc g)}

delPred :: (Hashable s, Eq s) => (CVertex s, CVertex s) -> IKVGraph s -> IKVGraph s
delPred (u, v) g = g { igPred = removes v u (igPred g)}

delVtx :: (Hashable s, Eq s) => CVertex s -> IKVGraph s -> IKVGraph s
delVtx v g = g { igSucc = M.delete v (igSucc g) }
               { igPred = M.delete v (igPred g) }

inserts :: (Eq k, Eq v, Hashable k, Hashable v)
        => k -> v -> M.HashMap k (S.HashSet v) -> M.HashMap k (S.HashSet v)
inserts k v m = M.insert k (S.insert v $ M.lookupDefault S.empty k m) m

removes :: (Eq k, Eq v, Hashable k, Hashable v)
        => k -> v -> M.HashMap k (S.HashSet v) -> M.HashMap k (S.HashSet v)
removes k v m = M.insert k (S.delete v (M.lookupDefault S.empty k m)) m
