{-# Language DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Haskell.TypeTree.Datatype where

import Data.Data
import Data.Maybe
import Language.Haskell.TH

-- | More ergonomic representation of bound and unbound names of things.
data Binding
    = Bound { unBinding :: Name }
    -- ^ We know this name refers to a specific thing (i.e. it's
    -- a constructor)
    | Unbound { unBinding :: Name }
    -- ^ We don't know what this is (i.e. a type variable)
    deriving (Show, Ord, Eq, Data)

class IsDatatype a where
    -- | Produce binding info and a list of type arguments
    asDatatype :: a -> Q (Binding, [Type])

instance IsDatatype Name where
    asDatatype n = pure (guess n, [])

instance IsDatatype TypeQ where
    asDatatype = fmap unwrap

unwrap :: Type -> (Binding, [Type])
unwrap = go
  where
    go (ConT x) = (Bound x, [])
    go (VarT y) = (Unbound y, [])
    go (ForallT _ _ x) = go x
    go (AppT x y) =
        let (hd, args) = go x
         in (hd, args ++ [y])
    go ListT = (Bound ''[], [])
    go ArrowT = (Bound ''(->), [])
    go (TupleT n) = (Bound (tupleTypeName n), [])
    go (UnboxedTupleT n) = (Bound (unboxedTupleTypeName n), [])
    go (SigT t _k) = go t
    go z = error $ show z

-- | Convenience function.
guess n
    | isNothing (nameSpace n) = Unbound n
    | otherwise = Bound n
