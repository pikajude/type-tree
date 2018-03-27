{-# Language MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Arrow
import Control.Monad
import Data.Array
import Data.Graph
import Data.List
import Distribution.PackageDescription
import Language.Haskell.TypeTree

main = do
    forM_ (map (fmap close) $ nub $ stronglyConnCompR edges) $ \x -> case x of
        AcyclicSCC x -> print x
        CyclicSCC xs -> mapM_ print xs
  where
    close (scc, k, _) = (scc, typeClosure k)
    edges = $(ttEdges ''PackageDescription)
    (grph, ixfn, revix) = graphFromEdges edges
    typeClosure n = nub $ go n [n]
      where
        go (revix -> Just x) ns =
            concatMap
                (\i ->
                     let ((nod, len), k, _) = ixfn i
                      in if | k `elem` ns -> []
                            | len == 0 -> [nod]
                            | otherwise -> go k (k : ns))
                (grph ! x)
