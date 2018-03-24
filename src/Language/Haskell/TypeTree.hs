{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.Haskell.TypeTree
      -- ** GHCi setup
      -- $setup
      -- * Usage
      -- $usage
      -- * Producing trees
    ( ttReify
    -- , ttReifyOpts
    , ttLit
    -- , ttLitOpts
    -- , ttDescribe
    -- , ttDescribeOpts
      -- * Customizing trees
    , Leaf(..)
    , ReifyOpts(..)
    , defaultOpts
    ) where

import Control.Concurrent
import Control.Monad
import Control.Monad.Reader
import Data.Data (Data)
import Data.Function
import Data.Graph
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
import Language.Haskell.TypeTree.Leaf

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

-- | Produces a string literal representing a type tree. Useful for
-- debugging purposes.
-- ttDescribe = ttDescribeOpts defaultOpts
-- | 'ttDescribe' with the given options.
-- ttDescribeOpts o n = do
--     tree <- ttReifyOpts o n
--     stringE $ drawTree $ fmap showLeaf tree
--   where
--     showLeaf (TypeLeaf n) = show n
--     showLeaf (FreeVar (n, x)) = "<<unbound var " ++ show (nameBase n) ++ ">> " ++ show x
--     showLeaf (Recursion x) = "<<recursive " ++ show x ++ ">>"
-- | Embed the produced tree as an expression.
ttLit = liftTree <=< ttReify

instance Lift Name

-- | 'ttLit' with provided opts.
-- ttLitOpts opts = liftTree <=< ttReifyOpts opts
liftTree (Node n xs) = [|Node $(TH.lift n) $(listE $ map liftTree xs)|]

-- | Build a "type tree" of the given datatype.
--
-- Concrete types will appear in the tree as 'TypeLeaf'. Unbound variables
-- will appear as 'FreeVar'. If the datastructure is recursive, occurrences
-- of the node after the first will be replaced with 'Recursion'.
ttReify = ttReifyOpts defaultOpts

data ReifyEnv = ReifyEnv
              { typeEnv :: Map Name Type
              , nodes :: S.Set (Binding, [Type])
              } deriving Show

-- | 'ttReify' with the provided options.
ttReifyOpts :: ReifyOpts Leaf -> Name -> Q (Tree Leaf)
ttReifyOpts opts n = runReaderT (go (Bound n) []) (ReifyEnv mempty mempty)
  where
    go n as = do
        r <- ask
        lift $
            qRunIO $ do
                print (n, as)
                print r
                threadDelay 1000000
        go' n as
    go' v@(Unbound n) givenArgs = withVisit v givenArgs $
        Node (FreeVar (n,[])) <$>
            mapM
                (\arg -> recurseField =<< uncurry resolve (unwrap arg))
                givenArgs
    go' v@(Bound n) givenArgs = withVisit v givenArgs $ do
        dec <- lift $ reify n
        case dec of
            TyConI x -> do
                let (name, wantedArgs) = decodeHead x
                    cons = decodeBody x
                -- invariant: constructor fields (obviously) must be of
                -- kind *. if the type isn't fully applied, generate some
                -- placeholders and recurse. this happens when you pass in
                -- type function at top level (like ttReify ''Maybe)
                if length givenArgs /= length wantedArgs
                    then do
                        go (Bound n) =<< lift (sequence $ fmap VarT (newName "arg") <$ wantedArgs)
                    else withReaderT (\m -> foldr resolution m $ zip wantedArgs givenArgs) $ do
                             fields <-
                                 forM cons $ \(x, args) -> do
                                     recurseField =<< resolve x args
                             return $ Node (TypeLeaf (n, [])) fields
    recurseField Nothing = pure $ Node Recursion []
    recurseField (Just (a,b)) = go a b
    decodeHead (DataD _ n holes _ _ _) = (n, map unTV holes)
    decodeHead (TySynD n holes _) = (n, map unTV holes)
    decodeBody (DataD _ _ _ _ cons _) = concatMap getFieldTypes cons
    decodeBody (TySynD _ _ ty) = [unwrap ty]
    getFieldTypes (NormalC _ xs) = map (\(_, y) -> unwrap y) xs
    getFieldTypes (RecC _ xs) = map (\(_, _, y) -> unwrap y) xs
    getFieldTypes (InfixC (_, a) _ (_, b)) = [unwrap a, unwrap b]
    unTV (KindedTV n _) = n
    unTV (PlainTV n) = n
    resolution (x,y) r@ReifyEnv{typeEnv = t} = r { typeEnv = M.insert x y t }
    withVisit a b m = do
        n <- asks nodes
        if S.member (a,b) n
            then pure $ Node Recursion []
            else withReaderT (\ r -> r { nodes = S.insert (a,b) (nodes r) }) m
    resolve (Bound x) args = pure $ Just (Bound x, args)
    resolve (Unbound x) args = go' x args [] where
        go' x args xs = do
            m <- asks typeEnv
            case M.lookup x m of
                Just (VarT y)
                    | elem y xs -> pure Nothing
                    | otherwise -> go' y args (y:xs)
                Just (unwrap -> (h, args')) -> pure $ Just (h, args' ++ args)
                Nothing -> pure $ Just (Unbound x, [])
    unwrap = go
      where
        go (ConT x) = (Bound x, [])
        go (VarT y) = (Unbound y, [])
        go (AppT x y) =
            let (hd, args) = go x
             in (hd, args ++ [y])
        go ListT = (Bound ''[], [])
        go z = error $ show z

data Binding
    = Bound Name
    | Unbound Name
    deriving (Show, Ord, Eq)
{-

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
    | n == ': = [unwrap t1]
    | otherwise = [unwrap t1, unwrap t2]

unwrap = go
  where
    go (ConT x) = (x, [])
    go (VarT y) = (y, [])
    go (AppT x y) = second (++ [y]) (go x)
    go ListT = (''[], [])
    go (TupleT n) = (tupleTypeName n, [])
    go (UnboxedTupleT n) = (unboxedTupleTypeName n, [])
    go ArrowT = (''->, [])
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

-}
