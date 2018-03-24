{-# Language DeriveDataTypeable #-}

module Language.Haskell.TypeTree.Leaf where

import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Ppr
import Language.Haskell.TH.PprLib
import Language.Haskell.TypeTree.CheatingLift
import Data.Data

instance Lift Type

data Leaf
    = TypeLeaf (Name, [Type])
    -- ^ @TypeLeaf (name, xs)@ is a field with type @ConT name@, applied to types @xs@.
    | FreeVar (Name, [Type])
    -- ^ @TypeLeaf (name, xs)@ is a field with type @VarT name@, applied to types @xs@.
    | Recursion -- ^ Recursive field.
    deriving (Eq, Data, Ord)

instance Show Leaf where
    showsPrec p (TypeLeaf (n, ts)) =
        showsPrec p (pprName n) . showString " " . showList (map ppr ts)
    showsPrec p (FreeVar (n, ts)) =
        showString "$" . showsPrec p (pprName n) . showString " " . showList (map ppr ts)
    showsPrec p (Recursion) = showString "recursion"

instance Lift Leaf where
    lift (TypeLeaf (n, x)) = [|TypeLeaf ($(liftName n), x)|]
    lift (FreeVar (n, x)) = [|FreeVar ($(liftName n), x)|]
    lift (Recursion) = [|Recursion|]
