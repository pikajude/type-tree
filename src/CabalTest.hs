{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module CabalTest where

import Control.Concurrent
import Control.Monad
import Data.Array
import Data.Either
import Data.Foldable
import Data.Graph
import Data.List
import Data.Maybe
import Data.Tree
import Debug.Trace
import Distribution.PackageDescription
import Distribution.Types.UnqualComponentName
import Language.Haskell.TypeTree

main :: IO ()
main = do
    let nodes =
            partitionEithers $
            flip map sc $ \n@(Node v _) ->
                case decode n of
                    AcyclicSCC v -> Left $ typeClosure v
                    CyclicSCC q -> Right $ map (_fst . deref) q
    print (filter (`notElem` concat (snd nodes)) $ concat $ fst nodes)
    print (snd nodes)
  where
    sc = scc grph
    cycles =
        concat $
        mapMaybe
            (\case
                 CyclicSCC x -> Just x
                 _ -> Nothing)
            (map decode sc)
    typeClosure n
        | n `elem` cycles = [_fst (deref n)]
        | otherwise =
            case (_fst $ deref n, grph ! n) of
                (x, []) -> [x]
                (x, xs) -> x : (map (_fst . deref) sat ++ concatMap typeClosure unsat)
                    where (sat, unsat) = partition saturated xs
                          saturated m =
                              let ((_, k), _, _) = deref m
                               in k == 0
    (grph, deref, lookup) = conComp $(ttLit ''CondTree)
    getTypeClosure idx =
        case deref idx of
            node@(n, _, ks) ->
                let deps = map (fromJust . lookup) ks
                 in node : concatMap getTypeClosure deps
    decode (Node v [])
        | mentions_itself v = CyclicSCC [v]
        | otherwise = AcyclicSCC v
    decode other = CyclicSCC (dec other [])
      where
        dec (Node v ts) vs = v : foldr dec vs ts
    mentions_itself v = v `elem` (grph ! v)

_fst (x, _, _) = x

_snd (_, x, _) = x
