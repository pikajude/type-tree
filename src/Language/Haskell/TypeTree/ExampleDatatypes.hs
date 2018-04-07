module Language.Haskell.TypeTree.ExampleDatatypes where

import Prelude

data CondTree v c a = CondNode
    { condTreeData :: a
    , condTreeConstraints :: c
    , condTreeComponents :: [CondBranch v c a]
    }

data CondBranch v c a = CondBranch
    { condBranchCondition :: Condition v
    , condBranchIfTrue :: CondTree v c a
    , condBranchIfFalse :: Maybe (CondTree v c a)
    }

data Condition c
    = Var c
    | Lit Bool
    | CAnd (Condition c)
           (Condition c)
