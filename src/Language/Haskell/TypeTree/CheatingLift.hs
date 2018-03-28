{-# Language TemplateHaskell #-}

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

$(do TyConI (DataD _ _ _ _ [NormalC x _] _) <- reify ''Name
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
                                [ conE $(liftData x)
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
    [|NameG $(liftData x) (PkgName $(stringE s)) (ModName $(stringE y))|]
liftFlv (NameQ (ModName x)) = [|NameQ (ModName $(stringE x))|]
liftFlv (NameU i) = [|NameU i|]
liftFlv (NameL i) = [|NameL i|]
