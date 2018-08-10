{-# OPTIONS_GHC -fno-warn-deriving-typeable #-} -- N/A in earlier GHC versions
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Language.Haskell.TypeTree.Leaf
    ( Leaf(..)
    , unLeaf
    ) where

import Data.Data
import Data.List.Compat
import Language.Haskell.TH.Syntax
import Language.Haskell.TypeTree.CheatingLift
import Prelude.Compat

data Leaf
    = TypeL Name
            Arity
    -- ^ @TypeL name arr@ represents the type constructor @name@, which has
    -- arity @arr@.
    | Recursive Leaf -- ^ Recursive field.
    deriving (Eq, Data, Ord, Typeable)

instance Show Leaf where
    showsPrec p (TypeL n rs) =
        showParen (p > 10) $
        showString (nameBase n) .
        showString " :: " . showString (intercalate " -> " (replicate (rs + 1) "*"))
    showsPrec p (Recursive r) = showString "..." . showsPrec p r

unLeaf :: Leaf -> Leaf
unLeaf (Recursive t) = unLeaf t
unLeaf x = x

instance Lift Leaf where
    lift (TypeL n x) = [|TypeL $(liftName n) x|]
    lift (Recursive r) = [|Recursive $(lift r)|]
