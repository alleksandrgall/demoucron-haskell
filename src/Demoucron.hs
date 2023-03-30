{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}

{- |
Module      : Demoucron
Copyright   : (c) 2023 Ivan Iablochkin

License     : BSD-style
Maintainer  : alleksandegall@gmail.com
Stability   : experimental
Portability : GHC

Code for Demoucron algorithm.
-}
module Demoucron (demoucron) where

import Algebra.Graph.AdjacencyIntMap
import Control.DeepSeq (deepseq)
import Control.Monad.Primitive (PrimMonad (..))
import Control.Monad.ST (runST)
import Data.Bool (bool)
import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (fromJust)
import qualified Data.Vector.Unboxed.Mutable as VM

{- | If the graph `g` represented by `AdjacencyIntMap` is acyclic, `demoucron g` evaluates to `Right xs`.
No matter the permutations of elements of `xs`, the resulting list will be a topological sort of the given graph.
In other words, vertices belonging to one element of xs can be evaluated in parallel without ruining the dependency graph order.
@
let g = (0 * 4) + (4 * 1) + (4 * 3)
demoucron g = [[0], [4], [1,3]]
@

If the graph `g` contains a cycle, `demoucron g` evaluates to `Left containsACycle`.
`containsACycle` is a list of vertices where a cycle can be found (Not an exact cycle itself, the list can contain additional vertices.)

Complexity: /O(n + m)/ time and memory
Typically performs better than `Algebra.Graph.AdjacencyIntMap.Algorithm.topSort`, especially on large numbers of edges.
-}
demoucron :: AdjacencyIntMap -> Either (NonEmpty Int) [[Int]]
demoucron aim = runST (demoucronImpl aim)

demoucronImpl :: PrimMonad m => AdjacencyIntMap -> m (Either (NonEmpty Int) [[Int]])
demoucronImpl graph = do
  vertexsIncomingDeg <- VM.replicate (vertexCount graph) 0
  let vls = vertexList graph
      vertexIndexMap = IntMap.fromList $ zip vls [0, 1 ..]
      indexVertexMap = IntMap.fromList $ zip [0, 1 ..] vls
      indexOfVertex v = fromJust . IntMap.lookup v $ vertexIndexMap
  vertexIndexMap `deepseq`
    mapM_ (mapM_ (VM.unsafeModify vertexsIncomingDeg (+ 1) . indexOfVertex) . IntSet.toAscList) (adjacencyIntMap graph)
  indexVertexMap `deepseq` loop vertexIndexMap indexVertexMap vertexsIncomingDeg graph mempty

loop :: PrimMonad m => IntMap Int -> IntMap Int -> VM.MVector (PrimState m) Int -> AdjacencyIntMap -> IntSet -> m (Either (NonEmpty Int) [[Int]])
loop vertexIndexMap indexVertexMap vec graph = loop'
 where
  indexOfVertex v = fromJust . IntMap.lookup v $ vertexIndexMap
  vertexOfIndex i = fromJust . IntMap.lookup i $ indexVertexMap
  loop' visited = do
    currentLevel <-
      VM.ifoldM'
        ( \acc i a ->
            let vof = vertexOfIndex i
             in pure . bool acc (vof : acc) $ (a <= 0 && vof `IntSet.notMember` visited)
        )
        []
        vec
    case currentLevel of
      [] -> do
        containsCycle <- VM.ifoldr' (\i a acc -> if a <= 0 then acc else vertexOfIndex i : acc) [] vec
        case containsCycle of
          (x : xs) -> return . Left $ x :| xs
          _ -> return . Right $ []
      _ -> do
        let newVisited = foldr IntSet.insert visited currentLevel
        mapM_ (\v -> mapM_ (VM.unsafeModify vec (subtract 1) . indexOfVertex) . IntSet.toAscList $ postIntSet v graph) currentLevel
        res <- loop' newVisited
        pure $ (currentLevel :) <$> res