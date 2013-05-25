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

import AI.Planning as Plan
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
                    putStrLn "CNF negation pushing:"
                    quickCheck prop_cnfpushnegation
                    putStrLn "CNF:"
                    quickCheckWith (stdArgs{maxSize = 17}) prop_iscnf
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


-- quickcheck contradict
prop_iscontradiction e = if isTautology e
    then
          isContradiction $ Negation e
    else
          not $ isContradiction $ Negation e


isEquivalent e1 e2 = Plan.isTautology $ Biconditional e1 e2

iscnf (Variable a) = True
iscnf (Negation (Variable a)) = True
iscnf (Negation _) = False
iscnf (Conjunction a b) = (iscnf a) && (iscnf b)
iscnf (Disjunction (Conjunction a b) _) = False
iscnf (Disjunction _ (Conjunction a b)) = False
iscnf (Disjunction a b) = (iscnf a) && (iscnf b)
iscnf (Implication a b) = False
iscnf (Biconditional a b) = False

prop_iscnf e = 
    let 
        e' = toCnf e
    in
        iscnf e' && isEquivalent e e'


isCnfNegationPushed (Negation (Variable a)) = True
isCnfNegationPushed (Negation _) = False

isCnfNegationPushed (Variable a) = True
isCnfNegationPushed (Conjunction a b) = (isCnfNegationPushed a) && (isCnfNegationPushed b)
isCnfNegationPushed (Disjunction a b) = (isCnfNegationPushed a) && (isCnfNegationPushed b)

prop_cnfpushnegation e =
    let
        e' = Plan.cnfPushNegation $ cnfReplace e
    in
        isCnfNegationPushed e' && isEquivalent e e'