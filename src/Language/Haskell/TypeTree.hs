{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell #-}

#if !MIN_VERSION_containers(0,5,9)
{-# LANGUAGE StandaloneDeriving #-}
#endif

#if MIN_VERSION_template_haskell(2,11,0)
#define _KIND _
#else
#define _KIND
#endif

module Language.Haskell.TypeTree
    ( -- ** GHCi setup
      -- $setup

      -- * Usage
      -- $usage
      ReifyOpts(..)
    , defaultOpts
    , ttConnComp
    , ttConnCompOpts
    , Leaf(..)
    , IsDatatype(..)
    ) where

import Control.Monad
import Data.Char
import Data.Graph
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Tree
import Language.Haskell.TH hiding (prim)
import Language.Haskell.TH.Syntax
import Language.Haskell.TypeTree.Datatype
import Language.Haskell.TypeTree.Leaf
import Prelude.Compat

#if !MIN_VERSION_containers(0,5,9)
deriving instance Show a => Show (SCC a)
#endif

{- $setup
>>> :set -XTemplateHaskell -XGADTs -XTypeFamilies
-}
{- $usage

@type-tree@ provides a way to build tree structures from datatypes.

== Basic usage

>>> data Foo a = Foo { field1 :: a, field2 :: Either String Int }
>>> putStr $(ttDescribe ''Foo)
Foo :: * -> *
|
+- Either :: * -> * -> *
|
+- [] :: * -> *
|  |
|  `- ...[] :: * -> *
|
+- Char :: *
|
`- Int :: *

'ttReify' passes through type synonyms by default:

>>> putStr $(ttDescribe ''FilePath) -- FilePath --> String --> [Char]
[] :: * -> *
|
`- ...[] :: * -> *
<BLANKLINE>
Char :: *

but this behavior can be disabled:

>>> putStr $(ttDescribeOpts defaultOpts { synonyms = True } ''FilePath)
FilePath :: *
|
`- String :: *
   |
   +- [] :: * -> *
   |  |
   |  `- ...[] :: * -> *
   |
   `- Char :: *
-}

ttDescribe :: IsDatatype a => a -> ExpQ
ttDescribe = ttDescribeOpts defaultOpts

ttDescribeOpts o x = do
    ts <- ttReifyOpts o x
    stringE $ reverse $ dropWhile isSpace $ reverse $ drawForest $ map (fmap show) ts

ttLit = ttLitOpts defaultOpts

ttLitOpts o n = do
    tr <- ttReifyOpts o n
    [|$(listE (map liftTree tr)) :: Forest Leaf|]
  where
    liftTree (Node n ns) = [|Node $(lift n) $(listE $ map liftTree ns)|]

ttConnComp = ttConnCompOpts defaultOpts

-- | 'ttConnCompOpts' is useful for the usecase which I had in mind when
-- I originally wrote this package, namely:
--
-- /Given some datatype, I need a topologically sorted list of all types contained in that datatype for which an instance of some class must be defined if I wish to define an instance for that datatype (and likewise for each subtype, etc.)/
--
-- Here's an example using 'Distribution.Types.CondTree', which is a useful datatype
-- for an example, as it's both mutually recursive and refers to other
-- recursive types.
--
-- >>> :m +Distribution.Types.CondTree
-- >>> mapM_ print $(ttConnComp ''CondTree)
-- AcyclicSCC ([] :: * -> *,[])
-- AcyclicSCC (Bool :: *,[])
-- AcyclicSCC (Maybe :: * -> *,[])
-- AcyclicSCC (Condition :: * -> *,[Bool :: *])
-- CyclicSCC [(CondBranch :: * -> * -> * -> *,[Condition :: * -> *,CondTree :: * -> * -> * -> *,Maybe :: * -> *]),(CondTree :: * -> * -> * -> *,[[] :: * -> *,CondBranch :: * -> * -> * -> *])]
ttConnCompOpts o name = do
    trs <- ttReifyOpts o name
    [|map (fmap (\(a, _, c) -> (a, nub c))) $
      stronglyConnCompR
          $(lift $ nubBy (\(x, _, _) (y, _, _) -> x == y) $ concatMap go trs)|]
  where
    go (Node ty xs) =
        (unRec ty, unRec ty, filter (/= unRec ty) $ map (unRec . rootLabel) xs) :
        concatMap go xs

data ReifyOpts = ReifyOpts
    { stop :: S.Set Name
      -- ^ If a name in this set is encountered, stop recursing.
    , prim :: Bool
      -- ^ Expand primitive type constructors (i.e. 'Int' &#8594; 'GHC.Prim.Int#')?
    , synonyms :: Bool
      -- ^ If 'True', type synonyms are present in the resulting 'Forest';
      -- if 'False', a synonym will be expanded and its RHS will appear in
      -- the out-list instead.
    }

-- |
-- @
-- defaultOpts = ReifyOpts
--   { stop = S.fromList []
--   , prim = False
--   , synonyms = False
--   }
-- @
defaultOpts :: ReifyOpts
defaultOpts = ReifyOpts mempty False False

ttReify = ttReifyOpts defaultOpts

ttReifyOpts args n' = do
    n <- asDatatype n'
    fmap concat $ mapM (go mempty) n
  where
    go xs ty
        | ty `S.member` stop args = do
            m <- getArity ty
            pure [Node (TypeL ty m) []]
        | Just r <- M.lookup ty xs = pure [Node (Recursive r) []]
        | otherwise = do
            x <- reify ty
            case x of
                TyConI dec -> do
                    let cons = decode dec
                        n = TypeL ty (arity dec)
                    children <- concat <$> mapM (go (M.insert ty n xs)) cons
                    if isTySyn dec && not (synonyms args)
                        then pure children
                        else pure [Node n children]
                PrimTyConI n arr _
                    | prim args -> pure [Node (TypeL n arr) []]
                    | otherwise -> pure []
                ClassOpI {} -> fail "can't reify a class method"
                ClassI {} -> fail "can't reify a typeclass"
                DataConI {} -> fail "can't reify a data constructor"
                VarI {} -> fail "can't reify an ordinary function/variable"
                FamilyI {} -> fail "sorry, data/type instances are currently unsupported"
                x -> error $ show x
      where
        isTySyn TySynD {} = True
        isTySyn _ = False

getArity n = do
    x <- reify n
    case x of
        TyConI dec -> pure (arity dec)
        PrimTyConI _ n _ -> pure n

arity (DataD _ _ xs _KIND _ _) = length xs
arity (NewtypeD _ _ xs _KIND _ _) = length xs
arity (TySynD _ xs _) = length xs
arity x = error $ show x

decode (DataD _ _ _ _KIND cons _) = concatMap decodeCon cons
decode (NewtypeD _ _ _ _KIND con _) = decodeCon con
decode (TySynD _ _ x) = getTypes x
decode x = error $ show x

decodeCon (NormalC _ fs) = concatMap (\(_, b) -> getTypes b) fs
decodeCon (RecC _ fs) = concatMap (\(_, _, b) -> getTypes b) fs
decodeCon (InfixC (_, f1) _ (_, f2)) = getTypes f1 ++ getTypes f2
#if MIN_VERSION_template_haskell(2,11,0)
decodeCon (GadtC _ cons ty) = concatMap (\(_, b) -> getTypes b) cons ++ getTypes ty
decodeCon (RecGadtC _ cons ty) = concatMap (\(_, _, b) -> getTypes b) cons ++ getTypes ty
#endif
decodeCon (ForallC _ _ c) = decodeCon c
