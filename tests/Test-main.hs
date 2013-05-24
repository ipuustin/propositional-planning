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
import Control.Monad

-- main program

runTest test = case test of
    "qc" -> do
                    putStrLn "Contradiction:"
                    quickCheck prop_iscontradiction
                    putStrLn "CNF:"
                    quickCheck prop_iscnf
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
    _ -> putStrLn $ "Unknown test case " ++ test


main = do
    putStrLn "Running tests"
    args <- getArgs
    mapM runTest args


-- QuickCheck tests

compoundExpr 0 =
        oneof [
                return $ Variable "A",
                return $ Variable "B",
                return $ Variable "C",
                return $ Variable "D"
               ]

compoundExpr n = do
        let n' = div n 2
        frequency [
                (1, liftM Negation (compoundExpr n')),
                (2, liftM2 Conjunction (compoundExpr n') (compoundExpr n')),
                (2, liftM2 Disjunction (compoundExpr n') (compoundExpr n')),
                (2, liftM2 Implication (compoundExpr n') (compoundExpr n')),
                (2, liftM2 Biconditional (compoundExpr n') (compoundExpr n'))
               ]

instance Arbitrary Expr where
    arbitrary = sized compoundExpr

{-
instance Arbitrary Expr where
    arbitrary = oneof [
                        return $ Variable "A",
                        return $ Variable "B",
                        return $ Variable "C",
                        return $ Variable "D",
                        liftM Negation arbitrary,
                        liftM2 Conjunction arbitrary arbitrary,
                        liftM2 Disjunction arbitrary arbitrary,
                        liftM2 Implication arbitrary arbitrary,
                        liftM2 Biconditional arbitrary arbitrary
                       ]
-}

-- quickcheck contradict
prop_iscontradiction e = if isTautology e
    then
          isContradiction $ Negation e
    else
          not $ isContradiction $ Negation e


prop_cnf (Variable a) = True
prop_cnf (Negation (Variable a)) = True
prop_cnf (Negation _) = False
prop_cnf (Conjunction a b) = (prop_cnf a) && (prop_cnf b)
prop_cnf (Disjunction a b) = (prop_cnf a) && (prop_cnf b)
prop_cnf (Implication a b) = False
prop_cnf (Biconditional a b) = False

prop_iscnf e = prop_cnf $ toCnf e
