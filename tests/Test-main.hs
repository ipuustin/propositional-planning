{- |
Module         : Main
Copyright      : Copyright (C) 2013 Ismo Puustinen
License        : BSD3
Maintainer     : Ismo Puustinen <ismo@iki.fi>
Stability      : experimental
Portability    : portable

Main module for the test suite.
-}


module Main

where

import AI.Planning
import AI.Planning.SatPlan
import Problems

import Data.List
import System.Environment
import Test.QuickCheck

-- main program

runTest test = case test of
    "qc" -> quickCheck contradict
    "flprob" ->
        case runSat flprob 10 of
            Just a -> putStrLn $ "Flashlight problem: " ++ show a
            Nothing -> putStrLn "Flashlight problem: no plan found"
    "bwprob1" ->
        case runSat bwprob1 10 of
            Just a -> putStrLn $ "Block World problem 1: " ++ show a
            Nothing -> putStrLn "Block World problem 1: no plan found"
    "bwprob2" ->
        case runSat bwprob2 10 of
            Just a -> putStrLn $ "Block World problem 2: " ++ show a
            Nothing -> putStrLn "Block World problem 2: no plan found"
    "bwprob3" ->
        case runSat bwprob3 10 of
            Just a -> putStrLn $ "Block World problem 3: " ++ show a
            Nothing -> putStrLn "Block World problem 3: no plan found"


main = do
    putStrLn "Running tests"
    args <- getArgs
    mapM runTest args


-- QuickCheck tests

instance Arbitrary Expr where
    arbitrary = do
        var <- elements ["X", "Y", "Z"]
        return $ Variable var

-- quickcheck contradict
contradict v1 v2 = if v1 == v2
    then
          isContradiction $ Conjunction v1 (Negation v2)
    else
          not $ isContradiction $ Conjunction v1 (Negation v2)
