{-# Language TypeFamilies #-}
{-# Language ScopedTypeVariables #-}
{-# Language LambdaCase #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language DeriveDataTypeable #-}
{-# Language DeriveLift #-}
{-# Language TemplateHaskell #-}

module Language.Haskell.TypeTree
    ( -- ** GHCi setup
      -- $setup
      -- * Usage
      -- $usage
      -- * Producing trees
      ttReify
    , ttReifyOpts
    , ttLit
    , ttLitOpts
    , ttDescribe
    , ttDescribeOpts
      -- * Useful helper functions
    -- , constructors
    , conComp
    , unLeaf
      -- * Customizing trees
    , Leaf(..)
    , ReifyOpts(..)
    , defaultOpts
    ) where

import Control.Concurrent
import Control.Monad
import Control.Monad.Reader
import Data.Data (Data)
import Data.Graph
import Data.Function
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S
import Data.Tree
import Debug.Trace
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)
import qualified Language.Haskell.TH.Syntax as TH
import Language.Haskell.TypeTree.CheatingLift

instance Lift Type

data Leaf
    = TypeLeaf (Name, [Type])
    -- ^ @TypeLeaf (name, xs)@ is a field with type @ConT name@, applied to types @xs@.
    | FreeVar (Name, [Type])
    -- ^ @TypeLeaf (name, xs)@ is a field with type @VarT name@, applied to types @xs@.
    | Recursion Leaf -- ^ Recursive field.
    deriving (Show, Eq, Data, Ord)

unLeaf (TypeLeaf x) = x
unLeaf (FreeVar x) = x
unLeaf (Recursion x) = unLeaf x

unCon (TypeLeaf x) = Just x
unCon (FreeVar _) = Nothing
unCon (Recursion x) = unCon x

instance Lift Leaf where
    lift (TypeLeaf (n, x)) = [|TypeLeaf ($(liftName n), x)|]
    lift (FreeVar (n, x)) = [|FreeVar ($(liftName n), x)|]
    lift (Recursion x) = [|Recursion $(TH.lift x)|]

data ReifyOpts a = ReifyOpts
    { expandPrim :: Bool -- ^ Descend into primitive type constructors?
    , terminals :: S.Set Name -- ^ If a name in this set is encountered, stop descending.
    , leafFn :: Leaf -> Maybe a
    -- ^ Convenience function to filter nodes. Default: 'Just'
    }

-- | Default reify options.
--
-- @
-- defaultOpts = "ReifyOpts"
--   { expandPrim = False
--   , terminals = S.fromList [''"String"]
--   , leafFn = Just -- don't filter any leaves by default
--   }
-- @
defaultOpts :: ReifyOpts Leaf
defaultOpts =
    ReifyOpts {expandPrim = False, terminals = S.fromList [''String], leafFn = Just}

-- | Given a type tree, produce a set of all constructor names (that is,
-- concrete types) and their type arguments.
treeCons :: Tree Leaf -> S.Set (Name, [Type])
treeCons ts = S.fromList $ mapMaybe unleaf $ flatten ts
  where
    unleaf (TypeLeaf (n, x)) = Just (n, x)
    unleaf _ = Nothing

-- | Like 'treeCons', but only returns expected arities rather than the
-- full argument list.
treeArities :: Tree Leaf -> S.Set (Name, Int)
treeArities ts = S.fromList $ mapMaybe unleaf $ flatten ts where
    unleaf (TypeLeaf (n, x)) = Just (n, length x)
    unleaf _ = Nothing

type Key = (Name, Int)

-- | A graph of the strongly connected components of the graph representing
-- the type tree of the given type. See 'stronglyConnComp' (on which this
-- is a pun)
conComp :: Tree Leaf -> (Graph, Vertex -> (Key, Key, [Key]), Key -> Maybe Vertex)
conComp = graphFromEdges . go where
    go (Node x xs) = (unleaf x, unleaf x, map (unleaf . rootLabel) xs) : nubBy ((==) `on` _fst) (concatMap go xs)
    _fst (x,_,_) = x
    second f (a,b) = (a, f b)
    unleaf = second length . unLeaf

-- | Produces a string literal representing a type tree. Useful for
-- debugging purposes.
ttDescribe = ttDescribeOpts defaultOpts

-- | 'ttDescribe' with the given options.
ttDescribeOpts o n = do
    tree <- ttReifyOpts o n
    stringE $ drawTree $ fmap showLeaf tree
  where
    showLeaf (TypeLeaf n) = show n
    showLeaf (FreeVar (n, x)) = "<<unbound var " ++ show (nameBase n) ++ ">> " ++ show x
    showLeaf (Recursion x) = "<<recursive " ++ show x ++ ">>"

-- | Embed the produced tree as an expression.
ttLit = liftTree <=< ttReify

-- | 'ttLit' with provided opts.
ttLitOpts opts = liftTree <=< ttReifyOpts opts

liftTree (Node n xs) = [|Node $(TH.lift n) $(listE $ map liftTree xs)|]

-- | Build a "type tree" of the given datatype.
--
-- Concrete types will appear in the tree as 'TypeLeaf'. Unbound variables
-- will appear as 'FreeVar'. If the datastructure is recursive, occurrences
-- of the node after the first will be replaced with 'Recursion'.
ttReify = ttReifyOpts defaultOpts

-- | 'ttReify' with the provided options.
ttReifyOpts opts n = do
    tree <- go (mempty :: Map Name Type) mempty (n, [])
    case tree of
        Nothing -> fail tyerr
        Just x ->
            case filterTree x of
                Nothing -> fail filtererr
                Just x -> return x
  where
    filterTree (Node x xs) =
        case leafFn opts x of
            Just y -> Just $ Node y $ nub $ mapMaybe filterTree xs
            Nothing -> Nothing
    tyerr =
        "Unable to expand the given type. Did you pass in a PrimTyCon with expandPrim disabled?"
    filtererr =
        "Provided filtering function rejected the root node. No tree can be produced"
    go hs visited p = do
        go' hs visited p
    go' hs visited p@(nm, typeArgs)
        | S.member nm (terminals opts) =
            pure $ Just $ Node (TypeLeaf (nm, typeArgs)) []
        | S.member p visited || looped nm =
            let con = if nameSpace nm `elem` [Just VarName, Nothing] then FreeVar else TypeLeaf
             in pure $ Just $ Node (Recursion (con (nm, typeArgs))) []
          -- hack: is our recursion depth at least 1? passing in invalid
          -- names like 'show or 'Just falls into this case otherwise
        | not (S.null visited) && nameSpace nm `elem` [Just VarName, Nothing] =
            case M.lookup nm hs of
                Just resolved -> go hs visited $ unwrap resolved
                Nothing -> do
                    fields <- mapM (go hs (insert' p) . unwrap) typeArgs
                    return $
                        Just $ Node (FreeVar (nm, typeArgs)) $ catMaybes fields
        | isUnboxedTuple nm && not (expandPrim opts) = pure Nothing
        | otherwise = do
            x <- reify nm
            case x of
                TyConI dec -> do
                    let (con, holes) = unhead dec
                        fields = concat $ unfield dec
                        resolutions = zip holes typeArgs
                    children <-
                        mapM (go (M.fromList resolutions <> hs) (insert' p)) fields
                    return $
                        Just $ Node (TypeLeaf (con, typeArgs)) $ catMaybes children
                PrimTyConI nm _ _
                    | expandPrim opts || nm == ''(->) -> do
                        fields <- mapM (go hs (insert' p) . unwrap) typeArgs
                        pure $
                            Just $
                            Node (TypeLeaf (nm, typeArgs)) $ catMaybes fields
                    | otherwise -> pure Nothing
                DataConI {} -> failWith "a data constructor"
                ClassI {} -> failWith "a class name"
                ClassOpI {} -> failWith "a class method"
                VarI {} -> failWith "a plain variable"
                PatSynI {} -> failWith "a pattern synonym"
                TyVarI {} -> failWith "how did you get here?"
                FamilyI _ insts ->
                    case resolve typeArgs insts of
                        Just dec -> do
                            let (con, holes) = unhead' dec
                                fields = concat $ unfield dec
                                resolutions = tweakResolutions $ zip holes typeArgs
                            children <-
                                mapM
                                    (go (M.fromList resolutions <> hs) (insert' p))
                                    fields
                            return $
                                Just $
                                Node (TypeLeaf (con, typeArgs)) $
                                catMaybes children
                        Nothing ->
                            fail
                                "The 'impossible' happened: data instance resolution failed"
        -- implies that we're trying to unify a free variable with
        -- itself. this indicates a recursive data structure; bail out once
        -- it's detected
      where
        failWith s = fail $ "ttReify expects a type constructor, but got " ++ s
        looped n = go n
          where
            go name =
                case M.lookup name hs of
                    Just (VarT x)
                        | x == n -> True
                        | otherwise -> go x
                    _ -> False
        insert' x = S.insert x visited
        isUnboxedTuple nm = nameModule nm == Just "GHC.Tuple" && '#' `elem` (nameBase nm)

tweakResolutions ((x, y):xs)
    | x == y = tweakResolutions xs
tweakResolutions ((VarT n, y):xs) = (n, y) : tweakResolutions xs
tweakResolutions [] = []

resolve tys (d@(DataInstD _ _ args _ _ _):ds)
    | and (zipWith unify tys args) = Just d
    | otherwise = resolve tys ds
resolve tys (d@(NewtypeInstD _ _ args _ _ _):ds)
    | and (zipWith unify tys args) = Just d
    | otherwise = resolve tys ds
resolve _ x = error $ show x

unify (ConT a) (ConT b) = a == b
unify VarT {} _ = True
unify _ VarT {} = True
unify x y = error $ show (x, y)

unhead (DataD _ x holes _ _ _) = (x, map unhole holes)
unhead (TySynD x vars _) = (x, map unhole vars)
unhead (NewtypeD _ x holes _ _ _) = (x, map unhole holes)
unhead x = error $ show x

unhead' (DataInstD _ x holes _ _ _) = (x, holes)
unhead' (NewtypeInstD _ x holes _ _ _) = (x, holes)

unhole (KindedTV nm _) = nm
unhole (PlainTV nm) = nm

unfield (DataD _ _ _ _ cons _) = map uncon cons
unfield (NewtypeD _ _ _ _ con _) = [uncon con]
unfield (TySynD _ _ ty) = [[unwrap ty]]
unfield (DataInstD _ _ _ _ cons _) = map uncon cons
unfield (NewtypeInstD _ _ _ _ con _) = [uncon con]
unfield x = error $ show x

uncon (ForallC _ _ c) = uncon c
uncon (RecC _ fs) = map (\(_, _, ty) -> unwrap ty) fs
uncon (NormalC _ fs) = map (\(_, ty) -> unwrap ty) fs
uncon (GadtC _ fs ret) = map (\(_, ty) -> unwrap ty) fs ++ map unwrap tys
    -- invariant: first arg of GADT return type will always be the parent
    -- datatype, otherwise you wouldn't be able to define it
  where
    (_, tys) = unwrap ret
uncon (RecGadtC _ fs ret) = map (\(_, _, ty) -> unwrap ty) fs ++ map unwrap tys
  where
    (_, tys) = unwrap ret
uncon (InfixC (_, t1) n (_, t2))
    | n == '(:) = [unwrap t1]
    | otherwise = [unwrap t1, unwrap t2]

unwrap = go
  where
    go (ConT x) = (x, [])
    go (VarT y) = (y, [])
    go (AppT x y) = second (++ [y]) (go x)
    go ListT = (''[], [])
    go (TupleT n) = (tupleTypeName n, [])
    go (UnboxedTupleT n) = (unboxedTupleTypeName n, [])
    go ArrowT = (''(->), [])
    go (SigT t _k) = go t
    go x = error $ show x
    second f (a, b) = (a, f b)
{- $setup

>>> :set -XTemplateHaskell -XTypeFamilies -XGADTs

-}
{- $usage

== Basic usage

'ttReify' allows you to build a 'Tree' containing type information for
each field of any given datatype, which can then be examined if you want
to, for example, generate class instances for a deeply nested datatype.
(The idea for this package came about when I was trying to figure out the easiest
way to generate several dozen instances for Cabal's @GenericPackageDescription@.)

=== Plain constructors

>>> data Foo a = Foo { field1 :: Either a Int }
>>> putStr $(ttDescribe ''Foo)
Ghci4.Foo
|
`- Data.Either.Either
   |
   +- <<unbound var "a">>
   |
   `- GHC.Types.Int

=== GADTs

>>> data MyGADT a where Con1 :: String -> MyGADT String; Con2 :: Int -> MyGADT [Int]
>>> putStr $(ttDescribe ''MyGADT)
Ghci8.MyGADT
|
+- GHC.Base.String
|
+- GHC.Base.String
|
+- GHC.Types.Int
|
`- GHC.Types.[]
   |
   `- GHC.Types.Int

=== Data family instances

>>> class Foo a where data Bar a :: *
>>> instance Foo Int where data Bar Int = IntBar { bar :: Maybe Int }
>>> type IntBar = Bar Int
>>> putStr $(ttDescribe ''IntBar)
Ghci16.IntBar
|
`- Ghci12.Bar
   |
   `- GHC.Base.Maybe
      |
      `- GHC.Types.Int

=== Recursive datatypes

>>> data Foo a = Foo { a :: Either Int (Bar a) }; data Bar b = Bar { b :: Either (Foo b) Int }
>>> putStr $(ttDescribe ''Foo)
Ghci20.Foo
|
`- Data.Either.Either
   |
   +- GHC.Types.Int
   |
   `- Ghci20.Bar
      |
      `- Data.Either.Either
         |
         +- Ghci20.Foo
         |  |
         |  `- <<recursion>>
         |
         `- GHC.Types.Int

Currently, if you want to instantiate type variables in the given datatype, the
best way to do so is to define a type synonym:

>>> type MaybeChar = Maybe Char
>>> putStr $(ttDescribe ''MaybeChar)
Ghci24.MaybeChar
|
`- GHC.Base.Maybe
   |
   `- GHC.Types.Char

...but future versions of this library may provide a more ergonomic way to
pass type arguments.

== Passing options

If needed, @type-tree@ allows you to specify that primitive type constructors
should be included in its output.

>>> data Baz = Baz { field :: [Int] }
>>> putStr $(ttDescribeOpts defaultOpts { expandPrim = True } ''Baz)
Ghci28.Baz
|
`- GHC.Types.[]
   |
   `- GHC.Types.Int
      |
      `- GHC.Prim.Int#

Note that the function arrow @(->)@, despite being a primitive type constructor,
will always be included even with @'expandPrim' = False@, as otherwise you
would never be able to get useful information out of a field with a function type.

You can also specify a set of names where @type-tree@ should stop descending, if,
for example, you have no desire to see @String -> [] -> Char@ ad nauseam in
your tree.

>>> data Bar = Bar (Either String [String])
>>> putStr $(ttDescribeOpts defaultOpts { terminals = S.fromList [''String] } ''Bar)
Ghci32.Bar
|
`- Data.Either.Either
   |
   +- GHC.Base.String
   |
   `- GHC.Types.[]
      |
      `- GHC.Base.String

-}
