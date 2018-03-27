{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Language.Haskell.TypeTree.Leaf where

import Data.Data
import Data.Tree
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Ppr
import Language.Haskell.TH.PprLib
import Language.Haskell.TH.Syntax
import Language.Haskell.TypeTree.CheatingLift

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
    = ConL (Name, [Type])
    -- ^ @ConL (name, xs)@ is a field with type @ConT name@, applied to types @xs@.
    | VarL (Name, [Type])
    -- ^ @VarL (name, xs)@ is a field with type @VarT name@, applied to types @xs@.
    | Recursive Leaf -- ^ Recursive field.
    deriving (Eq, Data, Ord, Show)

instance Lift Leaf where
    lift (ConL (n, x)) = [|ConL ($(liftName n), $(listE $ map liftType x))|]
    lift (VarL (n, x)) = [|VarL ($(liftName n), $(listE $ map liftType x))|]
    lift (Recursive r) = [|Recursive $(lift r)|]

treeDoc :: Tree Leaf -> Doc
treeDoc = vcat . go
  where
    go (Node x ts0) = leafDoc x : drawSubtrees ts0
    leafDoc (ConL (n, [a,b]))
        | n == ''(->) = pprParendType a <+> text "->" <+> pprParendType b
    leafDoc (ConL (n, x)) = pprName n <+> hsep (map pprParendType x)
    leafDoc (VarL (n, x)) = text "$" <> pprName n <+> hsep (map pprParendType x)
    leafDoc (Recursive x) = text "<" <> text "recursive" <+> leafDoc x <> text ">"
    drawSubtrees [] = mempty
    drawSubtrees [t] = char '|' : shift (text "`- ") (text "   ") (go t)
    drawSubtrees (t:ts) =
        char '|' : shift (text "+- ") (text "|  ") (go t) ++ drawSubtrees ts
    shift first other = zipWith (<>) (first : repeat other)
