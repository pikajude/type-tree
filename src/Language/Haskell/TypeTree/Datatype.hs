{-# Language DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Haskell.TypeTree.Datatype where

import Language.Haskell.TH
import Prelude.Compat

class IsDatatype a where
    -- | Produce a list of type arguments
    asDatatype :: a -> Q [Name]

instance IsDatatype Name where
    asDatatype n = pure [n]

instance IsDatatype TypeQ where
    asDatatype = fmap getTypes

getTypes (ConT x) = [x]
getTypes (VarT _) = []
getTypes ListT = [''[]]
getTypes ArrowT = [''(->)]
getTypes (TupleT n) = [tupleTypeName n]
getTypes (UnboxedTupleT n) = [unboxedTupleTypeName n]
getTypes (AppT x y) = getTypes x ++ getTypes y
getTypes x = error $ show x
