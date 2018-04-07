{-# Language MagicHash #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}

{-
- using TH to make a cheating version of `lift` for Name
- GHC expands all the strings contained in a Name into huge cons-trees, but
- it appears that if we use stringE in those cases instead it massively
- speeds up compilation and prevents stack overflows
-}
module Language.Haskell.TypeTree.CheatingLift
    ( liftName
    ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Prelude.Compat

#if !MIN_VERSION_template_haskell(2,10,0)
import GHC.Exts
#endif

#if MIN_VERSION_template_haskell(2,11,0)
#define _KIND _
#else
#define _KIND
#endif

$(do TyConI (DataD _ _ _ _KIND [NormalC x _] _) <- reify ''Name
     arg1 <- newName "arg"
     arg2 <- newName "arg"
     sequence
         [ sigD (mkName "liftName") [t|Name -> ExpQ|]
         , funD
               (mkName "liftName")
               [ clause
                     [conP x [varP arg1, varP arg2]]
                     (normalB
                          [|appsE
                                [ conE (mkName "Name")
                                , $(appE (varE $ mkName "liftOcc") (varE arg1))
                                , $(appE (varE $ mkName "liftFlv") (varE arg2))
                                ]|])
                     []
               ]
         ])

liftOcc :: OccName -> ExpQ
liftOcc (OccName s) = [|OccName $(stringE s)|]

liftFlv :: NameFlavour -> ExpQ
liftFlv NameS = [|NameS|]
liftFlv (NameG x (PkgName s) (ModName y)) =
    [|NameG $(liftNS x) (PkgName $(stringE s)) (ModName $(stringE y))|]
liftFlv (NameQ (ModName x)) = [|NameQ (ModName $(stringE x))|]
liftFlv (NameU i) = [|NameU $(litE $ intPrimL i')|]
    where
        i' = intPrimToInt i
liftFlv (NameL i) = [|NameL $(litE $ intPrimL i')|]
    where
        i' = intPrimToInt i

#if MIN_VERSION_template_haskell(2,10,0)
intPrimToInt = fromIntegral
#else
-- GHC <7.10 doesn't have kind-polymorphic `lift'
intPrimToInt i = fromIntegral (I# i)
#endif

liftNS VarName = [|VarName|]
liftNS DataName = [|DataName|]
liftNS TcClsName = [|TcClsName|]
