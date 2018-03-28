{-# LANGUAGE CPP #-}

#ifndef MIN_VERSION_cabal_doctest
#define MIN_VERSION_cabal_doctest(x,y,z) 0
#endif

module Main (main) where

#if MIN_VERSION_cabal_doctest(1,0,0)
import Distribution.Extra.Doctest (defaultMainWithDoctests)
#else
#ifdef MIN_VERSION_Cabal
import Warning ()
#endif
import Distribution.Simple
defaultMainWithDoctests _ = defaultMain
#endif

main = defaultMainWithDoctests "doctest"
