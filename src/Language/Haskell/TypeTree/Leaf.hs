{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Language.Haskell.TypeTree.Leaf where

import Data.Data
import Data.List.Compat
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax
import Language.Haskell.TypeTree.CheatingLift
import Prelude.Compat

liftType :: Type -> ExpQ
liftType (VarT x) = [|VarT $(liftName x)|]
liftType (ConT x) = [|ConT $(liftName x)|]
liftType (AppT x y) = [|AppT $(liftType x) $(liftType y)|]
liftType (TupleT n) = [|TupleT n|]
liftType ListT = [|ListT|]
liftType (SigT t k) = [|SigT $(liftType t) $(liftType k)|]
liftType (UnboxedTupleT n) = [|UnboxedTupleT n|]
liftType x = error $ show x

data Leaf
    = TypeL Name
            Arity
    -- ^ @TypeL name arr@ represents the type constructor @name@, which has
    -- arity @arr@.
    | Recursive Leaf -- ^ Recursive field.
    deriving (Eq, Data, Ord, Typeable)

leafName (TypeL n _) = n
leafName (Recursive l) = leafName l

instance Show Leaf where
    showsPrec p (TypeL n rs) =
        showParen (p > 10) $
        showString (nameBase n) .
        showString " :: " . showString (intercalate " -> " (replicate (rs + 1) "*"))
    showsPrec p (Recursive r) = showString "..." . showsPrec p r

unRec (Recursive t) = unRec t
unRec x = x

instance Lift Leaf where
    lift (TypeL n x) = [|TypeL $(liftName n) x|]
    lift (Recursive r) = [|Recursive $(lift r)|]
