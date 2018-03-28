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
import Language.Haskell.TypeTree.Datatype
import Prelude.Compat hiding ((<>))

liftType :: Type -> ExpQ
liftType (VarT x) = [|VarT $(liftName x)|]
liftType (ConT x) = [|ConT $(liftName x)|]
liftType (AppT x y) = [|AppT $(liftType x) $(liftType y)|]
liftType (TupleT n) = [|TupleT n|]
liftType ListT = [|ListT|]
liftType (SigT t k) = [|SigT $(liftType t) $(liftType k)|]
liftType (UnboxedTupleT n) = [|UnboxedTupleT n|]
liftType x = error $ show x

liftBinding (Bound n) = [|Bound $(liftName n)|]
liftBinding (Unbound n) = [|Unbound $(liftName n)|]

data Leaf
    = TypeL (Binding, [Type])
    -- ^ @TypeL (name, xs)@ is a field with type @name@ applied to types @xs@.
    | Recursive Leaf -- ^ Recursive field.
    deriving (Eq, Data, Ord, Show)

instance Lift Leaf where
    lift (TypeL (n, x)) = [|TypeL ($(liftBinding n), $(listE $ map liftType x))|]
    lift (Recursive r) = [|Recursive $(lift r)|]

treeDoc :: Tree Leaf -> Doc
treeDoc = vcat . go
  where
    go (Node x ts0) = leafDoc x : drawSubtrees ts0
    leafDoc (TypeL (n, [a,b]))
        | unBinding n == ''(->) = pprParendType a <+> text "->" <+> pprParendType b
    leafDoc (TypeL (n, x)) = pprBind n <+> hsep (map pprParendType x)
    leafDoc (Recursive x) = text "<" <> text "recursive" <+> leafDoc x <> text ">"
    drawSubtrees [] = mempty
    drawSubtrees [t] = char '|' : shift (text "`- ") (text "   ") (go t)
    drawSubtrees (t:ts) =
        char '|' : shift (text "+- ") (text "|  ") (go t) ++ drawSubtrees ts
    shift first other = zipWith (<>) (first : repeat other)
    pprBind (Bound n) = pprName n
    pprBind (Unbound n) = text "$" <> pprName n
