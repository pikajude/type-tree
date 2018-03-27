{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
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
    , ttReifyOpts
    , ttLit
    , ttLitOpts
      -- ** Debugging trees
    , ttDescribe
    , ttDescribeOpts
      -- ** Building graphs
    , Key
    , Arity
    , ttEdges
    , ttConnComp
      -- * Customizing trees
    , Leaf(..)
    , ReifyOpts(..)
    , defaultOpts
    ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Data.Graph
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.Tree
import Language.Haskell.TH hiding (Arity)
import Language.Haskell.TH.PprLib
import Language.Haskell.TH.Syntax hiding (Arity, lift)
import qualified Language.Haskell.TH.Syntax as TH
import Language.Haskell.TypeTree.CheatingLift
import Language.Haskell.TypeTree.Datatype
import Language.Haskell.TypeTree.Leaf
import qualified Text.PrettyPrint as HPJ

data ReifyOpts = ReifyOpts
    { expandPrim :: Bool -- ^ Descend into primitive type constructors?
    , terminals :: S.Set Name -- ^ If a name in this set is encountered, stop descending.
    }

-- | Default reify options.
--
-- @
-- defaultOpts = "ReifyOpts"
--   { expandPrim = False
--   , terminals = mempty
--   }
-- @
defaultOpts :: ReifyOpts
defaultOpts = ReifyOpts {expandPrim = False, terminals = mempty}

-- | Produces a string literal representing a type tree. Useful for
-- debugging purposes.
ttDescribe :: IsDatatype t => t -> ExpQ
ttDescribe = ttDescribeOpts defaultOpts

-- | 'ttDescribe' with the given options.
ttDescribeOpts :: IsDatatype t => ReifyOpts -> t -> ExpQ
ttDescribeOpts o n = do
    tree <- ttReifyOpts o n
    stringE $
        HPJ.renderStyle
            HPJ.Style
                {HPJ.mode = HPJ.LeftMode, HPJ.lineLength = 0, HPJ.ribbonsPerLine = 5} $
        to_HPJ_Doc $ treeDoc tree

-- | Embed the produced tree as an expression.
ttLit :: IsDatatype t => t -> ExpQ
ttLit = liftTree <=< ttReify

-- | Some type and its arguments, as representable in a graph.
type Key = (Name, [Type])

-- | Type constructor arity.
type Arity = Int

-- | @$(ttEdges ''Foo) :: [(('Name', 'Arity'), 'Key', ['Key'])]@
--
-- @$(ttEdges ''Foo)@ produces a list suitable for passing to 'graphFromEdges'.
ttEdges :: IsDatatype t => t -> ExpQ
ttEdges name = do
    tr <- ttReify name
    sigE (listE $ map lift_ $ node tr) [t|[((Name, Arity), Key, [Key])]|]
  where
    lift_ ((x, n), y, zs) = [|(($(liftName x), n), $(tup y), $(listE $ map tup zs))|]
    tup (n, t) = [|($(liftName n), $(listE $ map liftType t))|]

-- | @$(ttConnComp ''Foo) :: ['SCC' ('Name', 'Arity')]@
--
-- @$(ttConnComp ''Foo)@ produces a topologically sorted list
-- of the strongly connected components of the graph representing @Foo@.
ttConnComp :: IsDatatype t => t -> ExpQ
ttConnComp name = [|stronglyConnComp $(ttEdges name)|]

node :: Tree Leaf -> [((Name, Arity), Key, [Key])]
node = nubBy (\(x, _, _) (y, _, _) -> x == y) . go
  where
    go (Node ty xs) =
        (second length $ unCon ty, unCon ty, map (unCon . rootLabel) xs) : concatMap go xs
    second f (a, b) = (a, f b)

unCon :: Leaf -> (Name, [Type])
unCon (ConL x) = x
unCon (VarL x) = x
unCon (Recursive r) = unCon r

-- | 'ttLit' with provided opts.
ttLitOpts :: IsDatatype t => ReifyOpts -> t -> ExpQ
ttLitOpts opts = liftTree <=< ttReifyOpts opts

liftTree :: Lift t => Tree t -> ExpQ
liftTree (Node n xs) = [|Node $(TH.lift n) $(listE $ map liftTree xs)|]

data ReifyEnv = ReifyEnv
    { typeEnv :: Map Name Type
    , nodes :: S.Set (Binding, [Type])
    } deriving (Show)

-- | Build a "type tree" of the given datatype.
--
-- Concrete types will appear in the tree as 'ConL'. Unbound variables
-- will appear as 'VarL'. If the datastructure is recursive, occurrences
-- of the node after the first will be wrapped in 'Recursive'.
ttReify :: IsDatatype t => t -> Q (Tree Leaf)
ttReify = ttReifyOpts defaultOpts

-- | 'ttReify' with the provided options.
ttReifyOpts :: IsDatatype t => ReifyOpts -> t -> Q (Tree Leaf)
ttReifyOpts opts t = do
    (a, b) <- asDatatype t
    fromJust <$> runReaderT (go a b) (ReifyEnv mempty mempty)
  where
    go n args = do
        go' n args
    go' v@(Unbound n) gargs
        | n `S.member` terminals opts = pure $ Just (Node (VarL (n, gargs)) [])
        | otherwise =
            withVisit v gargs $ \givenArgs ->
                Just . Node (VarL (n, givenArgs)) <$>
                mapMaybeM (uncurry resolve . unwrap) givenArgs
    go' v@(Bound n) gargs
        | n `S.member` terminals opts = pure $ Just (Node (ConL (n, gargs)) [])
        | otherwise =
            withVisit v gargs $ \givenArgs -> do
                dec <- lift $ reify n
                case dec of
                    PrimTyConI n' _ _
                        | expandPrim opts || n' == ''(->) ->
                            Just . Node (ConL (n', givenArgs)) <$>
                            mapMaybeM (uncurry resolve . unwrap) givenArgs
                        | otherwise -> pure Nothing
                    TyConI x -> processDec x n givenArgs
                    FamilyI _ insts ->
                        case matches givenArgs insts of
                            Just (dec, gargs) -> do
                                let (n, holes) = decodeHead' gargs dec
                                cons <- decodeBody dec
                                if length gargs /= length holes
                                    then do
                                        arglist <- mapM (lift . fillVar) holes
                                        go (Bound n) arglist
                                    else withReaderT
                                             (\m ->
                                                  foldr
                                                      resolveType
                                                      m
                                                      (zip holes givenArgs)) $
                                         Just . Node (ConL (n, gargs)) <$>
                                         mapMaybeM (uncurry resolve) cons
                            Nothing ->
                                fail $
                                "sorry, I cannot find a data instance in scope which matches: " ++
                                show (treeDoc (Node (ConL (n, givenArgs)) []))
                    x -> error $ show (x, givenArgs)
    processDec x n givenArgs = do
        let (_, wantedArgs) = decodeHead givenArgs x
        cons <- decodeBody x
        -- invariant: constructor fields (obviously) must be of
        -- kind *. if the type isn't fully applied, generate some
        -- placeholders and recurse. this happens when you pass in
        -- type function at top level (like ttReify ''Maybe)
        if length givenArgs /= length wantedArgs
            then do
                vars <- lift $ sequence (fmap VarT . newName . nameBase <$> wantedArgs)
                go (Bound n) vars
            else withReaderT (\m -> foldr resolution m $ zip wantedArgs givenArgs) $
                 Just . Node (ConL (n, givenArgs)) <$> mapMaybeM (uncurry resolve) cons
    mapMaybeM m xs = catMaybes <$> mapM m xs
    seqTup (a, b) = (,) <$> a <*> b
    fillVar (VarT n) = VarT <$> newName (nameBase n)
    fillVar x = pure x
    fill r@ReifyEnv {typeEnv = te} (VarT n) =
        case M.lookup n te of
            Just ty -> fill r ty
            Nothing -> VarT n
    fill _ x@ConT {} = x
    fill r (AppT x y) = AppT (fill r x) (fill r y)
    fill _ x@TupleT {} = x
    fill _ x@UnboxedTupleT {} = x
    fill _ ListT = ListT
    fill _ ArrowT = ArrowT
    fill r (SigT t k) = SigT (fill r t) k
    fill _ x = error $ show x
    decodeHead _ (DataD _ n holes _ cons _)
        | any isGadtCon cons = (n, [])
        | otherwise = (n, map unTV holes)
    decodeHead _ (NewtypeD _ n holes _ _ _) = (n, map unTV holes)
    decodeHead _ (TySynD n holes _) = (n, map unTV holes)
    decodeHead _ x = error $ "decodeHead " ++ show x
    decodeHead' _ (DataInstD _ n tys _ _ _) = (n, tys)
    decodeBody (DataD _ decName _ _ cons _) = concat <$> mapM (getFieldTypes decName) cons
    decodeBody (DataInstD _ decName _ _ cons _) =
        concat <$> mapM (getFieldTypes decName) cons
    decodeBody (NewtypeD _ decName _ _ con _) = getFieldTypes decName con
    decodeBody (TySynD _ _ ty) = pure [unwrap ty]
    decodeBody x = error $ "decodeBody " ++ show x
    matches typeArgs (d@(DataInstD _ _ tys _ _ _):ds) =
        fmap ((,) d) (unify typeArgs tys) <|> matches typeArgs ds
    matches _ [] = Nothing
    getFieldTypes _ (NormalC _ xs) = pure $ map (\(_, y) -> unwrap y) xs
    getFieldTypes _ (RecC _ xs) = pure $ map (\(_, _, y) -> unwrap y) xs
    getFieldTypes _ (InfixC (_, a) nm (_, b))
        | nameBase nm == ":" = pure [unwrap a]
        | otherwise = pure [unwrap a, unwrap b]
    getFieldTypes decName (GadtC _ fs ret) =
        case unwrap ret of
            (retN, retTys)
                | retN == Bound decName ->
                    pure $ map (\(_, y) -> unwrap y) fs ++ map unwrap retTys
                | otherwise ->
                    fail $
                    "sorry, GADT constructor return type must exactly " ++
                    "match datatype (this is a limitation in type-tree)"
    getFieldTypes decName (ForallC _ _ cn) = getFieldTypes decName cn
    getFieldTypes _ x = error $ show x
    isGadtCon GadtC {} = True
    isGadtCon RecGadtC {} = True
    isGadtCon (ForallC _ _ c) = isGadtCon c
    isGadtCon _ = False
    unTV (KindedTV n _) = n
    unTV (PlainTV n) = n
    resolution (x, y) r@ReifyEnv {typeEnv = t} = r {typeEnv = M.insert x y t}
    resolveType (VarT x, y)
        | VarT x == y = error "???"
        | otherwise = resolution (x, y)
    resolveType _ = id
    withVisit a b m = do
        r@ReifyEnv {nodes = nodes'} <- ask
        let b' = map (fill r) b
            a' =
                case fill
                         r
                         (case a of
                              Bound x -> ConT x
                              Unbound x -> VarT x) of
                    ConT n -> Bound n
                    VarT n -> Unbound n
                    _ -> undefined
        if S.member (a', b') nodes'
            then pure $ Just $ Node (Recursive $ leaf (a', b')) []
            else withReaderT (\q -> q {nodes = S.insert (a', b') (nodes q)}) $ m b'
    resolve (Bound x) args = go (Bound x) args
    resolve (Unbound x) args = go' x args []
      where
        go' x' args' xs = do
            m <- asks typeEnv
            case M.lookup x' m of
                Just (VarT y)
                    | elem y xs ->
                        pure $ Just $ Node (Recursive $ leaf (Unbound x', args')) []
                    | otherwise -> go' y args' (y : xs)
                Just (unwrap -> (h, args'')) -> go h (args'' ++ args')
                Nothing -> go (Unbound x') args'

leaf :: (Binding, [Type]) -> Leaf
leaf (Bound n, x) = ConL (n, x)
leaf (Unbound n, y) = VarL (n, y)

unify (x:xs) (VarT _:ys) = (:) x <$> unify xs ys
unify (ConT x:xs) (ConT y:ys)
    | x == y = (:) (ConT x) <$> unify xs ys
    | otherwise = Nothing
unify [] (VarT y:ys) = (:) (VarT y) <$> unify [] ys
unify [] [] = Just []
unify [] _ = Nothing
unify a b = error $ show (a, b)
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
Ghci4.Foo a_0
|
`- Data.Either.Either a_0 GHC.Types.Int
   |
   +- $a_0
   |
   `- GHC.Types.Int

=== Passing type arguments

@ttReify@ and friends accept any value with an 'IsDatatype' instance.

>>> putStr $(ttDescribe [t|Maybe Int|])
GHC.Base.Maybe GHC.Types.Int
|
`- GHC.Types.Int

=== GADTs

>>> data MyGADT a where Con1 :: String -> MyGADT String; Con2 :: Int -> MyGADT [Int]
>>> putStr $(ttDescribe ''MyGADT)
Ghci10.MyGADT
|
+- GHC.Base.String
|  |
|  `- GHC.Types.[] GHC.Types.Char
|     |
|     `- GHC.Types.Char
|
+- GHC.Base.String
|  |
|  `- GHC.Types.[] GHC.Types.Char
|     |
|     `- GHC.Types.Char
|
+- GHC.Types.Int
|
`- GHC.Types.[] GHC.Types.Int
   |
   `- GHC.Types.Int

When reifying GADTs, constructors' return types are treated as another
field.

=== Data family instances

>>> class Foo a where data Bar a :: * -> *
>>> instance Foo Int where data Bar Int a = IntBar { bar :: Maybe (Int, a) }
>>> putStr $(ttDescribe [t|Bar Int|])
Ghci14.Bar GHC.Types.Int a_0
|
`- GHC.Base.Maybe (GHC.Types.Int, a_0)
   |
   `- GHC.Tuple.(,) GHC.Types.Int a_0
      |
      +- GHC.Types.Int
      |
      `- $a_0

=== Recursive datatypes

>>> data Foo a = Foo { a :: Either Int (Bar a) }; data Bar b = Bar { b :: Either (Foo b) Int }
>>> putStr $(ttDescribe ''Foo)
Ghci20.Foo a_0
|
`- Data.Either.Either GHC.Types.Int (Ghci20.Bar a_0)
   |
   +- GHC.Types.Int
   |
   `- Ghci20.Bar a_0
      |
      `- Data.Either.Either (Ghci20.Foo a_0) GHC.Types.Int
         |
         +- <recursive Ghci20.Foo a_0>
         |
         `- GHC.Types.Int

== Passing options

If needed, @type-tree@ allows you to specify that primitive type constructors
should be included in its output.

>>> data Baz = Baz { field :: [Int] }
>>> putStr $(ttDescribeOpts defaultOpts { expandPrim = True } ''Baz)
Ghci24.Baz
|
`- GHC.Types.[] GHC.Types.Int
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
Ghci28.Bar
|
`- Data.Either.Either GHC.Base.String ([GHC.Base.String])
   |
   +- GHC.Base.String
   |
   `- GHC.Types.[] GHC.Base.String
      |
      `- GHC.Base.String

-}
