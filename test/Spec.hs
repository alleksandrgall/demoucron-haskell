{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

import Algebra.Graph.AdjacencyIntMap
import Algebra.Graph.AdjacencyIntMap.Algorithm (isTopSortOf, topSort)
import Control.Applicative (liftA2)
import Control.Monad (foldM)
import Data.Bool (bool)
import Data.Either (isLeft)
import Data.Foldable (Foldable (foldr'))
import Data.List (intersect, permutations)
import qualified Data.List.NonEmpty as NE
import Demoucron (demoucron)
import Test.Hspec (describe, hspec, it)
import Test.QuickCheck (
  Arbitrary (arbitrary),
  Args (maxSize),
  Property,
  choose,
  counterexample,
  forAll,
  sized,
  stdArgs,
  sublistOf,
  suchThat,
  verboseCheckWith,
  withMaxSuccess,
  (===),
 )

-- | Tests take some time due to `n!` of permutations which must be checked for the first property.
main :: IO ()
main = hspec $ describe "Demoucron properties" $ do
  it "Evaluates graph order function on acyclic graph" $
    verboseCheckWith stdArgs{maxSize = 20} (withMaxSuccess 100 demoucronAcyclic)
  it "Detects a cycle in a cyclic graph and returns vertices containing a cycle" $
    verboseCheckWith stdArgs{maxSize = 20} (withMaxSuccess 100 demoucronCyclic)

newtype Acyclic = Acyclic AdjacencyIntMap
  deriving newtype (Show)

instance Arbitrary Acyclic where
  arbitrary = fmap Acyclic $ sized $ \n -> do
    let sqrtN = (sqrt :: Float -> Float) . fromIntegral $ n
        loop = liftA2 (:) (choose (0, ceiling sqrtN)) loop
        takeUntilSumGrN s (x : xs) = if x + s < n then x : takeUntilSumGrN (x + s) xs else []
        takeUntilSumGrN _ [] = []
    levelSizes <- takeUntilSumGrN 0 <$> loop
    let levels = snd $ foldr' (\levelSize (lst, curLvls) -> (lst + levelSize, (take levelSize . iterate (+ 1) $ lst) : curLvls)) (-1, []) levelSizes
        makeStars (x : xs) = liftA2 (++) (chooseStars x xs) (makeStars xs)
        makeStars [] = pure []
        chooseStars _ [] = pure []
        chooseStars level higherLevels = let cHigherLevels = concat higherLevels in mapM (\v -> sublistOf cHigherLevels >>= \edgs -> pure (v, edgs)) level
    starLS <- makeStars levels
    return $ stars starLS

demoucronAcyclic :: Property
demoucronAcyclic = forAll arbitrary $ \(Acyclic graph) -> do
  let demoucronSorted = demoucron graph
  case demoucronSorted of
    Left containsCycle -> counterexample ("False cycle detected: " <> show containsCycle) False
    Right topSorted -> do
      let allLevelOrders =
            map reverse $
              foldM
                ( \acc levelPermutations -> do
                    oneOfLevelPermutations <- levelPermutations
                    return $ oneOfLevelPermutations : acc
                )
                []
                (map permutations topSorted)
      counterexample "All permutations should be equivalent to topological sort" $
        Nothing === foldr' (\onOfSorts _ -> bool (Just (topSorted, onOfSorts)) Nothing $ isTopSortOf (concat onOfSorts) graph) Nothing allLevelOrders

newtype Cyclic = Cyclic AdjacencyIntMap
  deriving newtype (Show)

instance Arbitrary Cyclic where
  arbitrary = fmap Cyclic $ flip suchThat (isLeft . topSort) $ sized $ \n -> do
    let curVertices = [0 .. n - 1]
    starLS <- mapM (\v -> sublistOf curVertices >>= \edgs -> pure (v, edgs)) curVertices
    return $ stars starLS

demoucronCyclic :: Property
demoucronCyclic = forAll arbitrary $ \(Cyclic graph) -> do
  let demoucronSorted = demoucron graph
  case demoucronSorted of
    Left containsCycle -> do
      let Left ccle = topSort graph
      counterexample "Should return a list containig a cycle" $
        (NE.toList ccle `intersect` NE.toList containsCycle) === NE.toList ccle
    Right topSortedIncorrect -> counterexample ("Did not detect a cycle: " <> show topSortedIncorrect) $ False
