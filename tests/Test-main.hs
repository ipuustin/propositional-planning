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
-- import AI.Planning.SatPlan as SatPlan
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
                    quickCheckWith (stdArgs{maxSize = 10}) prop_iscnf
                    putStrLn "Problem solution founding:"
                    quickCheck prop_solutionfound
    "flprob" ->
        case runSat flprob 10 of
            Just a -> putStrLn $ "Flashlight problem: " ++ show a
            Nothing -> putStrLn "Flashlight problem: no plan found"
{-
    -- Block world tets are being moved to automatic testing
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
-}
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



-- generate test problems in BlockWorld domain
-- block world -- (http://icaps06.icaps-conference.org/dc-papers/paper5.pdf)

assignVariables :: String -> [String] -> String
assignVariables fn vs = fn ++ "(" ++ intercalate "," vs ++ ")"

emptySlot :: [String] -> String -> [Expr]
emptySlot bs s = [ Negation $ Variable ("In("++b++","++s++")") | b <- bs ]

setBoxToSlot bs s b = boxInSlot : otherBoxes
    where boxInSlot = Variable ("In("++b++","++s++")")
          otherBoxes = [ Negation $ Variable ("In("++ob++","++s++")") | ob <- bs, ob /= b ]

emptyHandler bs = [ Negation $ Variable ("Holding("++b++")") | b <- bs ]

setBoxToHandler b bs = boxInHandler : otherBoxes
    where boxInHandler = Variable ("Holding("++b++")")
          otherBoxes = [ Negation $ Variable ("Holding("++ob++")") | ob <- bs, ob /= b ]

getBox :: Char -> String
getBox a = head $ generateVariables "box" [a]

getSlot :: Integer -> String
getSlot x = head $ generateVariables "slot" [x]

generateActions :: [String] -> [String] -> [Action]
generateActions ss bs = pickups ++ putdowns
    where pickups  = [ Action ("Pickup("++b++","++s++")")
                             (pickupPreconditions s b)
                             (pickupEffects s b)
                             1
                    | b <- bs, s <- ss ]
          putdowns = [ Action ("Putdown("++b++","++s++")")
                             (putdownPreconditions s b)
                             (putdownEffects s b)
                             1
                    | b <- bs, s <- ss ]

          pickupPreconditions s b = setBoxToSlot bs s b ++ emptyHandler bs
          pickupEffects s b = emptySlot bs s ++ setBoxToHandler b bs

          putdownPreconditions s b = setBoxToHandler b bs ++ emptySlot bs s
          putdownEffects s b = setBoxToSlot bs s b ++ emptyHandler bs

{-
  1. generate a set of boxes and slots
  2. from these boxes and slots, choose initial state and goal state and generate the actions
-}

-- | Put boxes to slots and set the handler to empty
initState :: [String] -> [String] -> [Expr]
initState bs ss = emptyHandler bs ++ slotData ss bs
      where slotData ss bs = emptySlots ss bs ++ fullSlots ss bs
            emptySlots ss bs = concat $ map (emptySlot bs) $ (drop (length bs) ss)
            fullSlots ss bs = concat $ map (processPair bs) (zip ss bs)
            processPair bs (slot, box) = setBoxToSlot bs slot box

-- | Generate initial and end states. Everything needs to be done inside one
-- Gen monad, since the states are interdependent.
generateStates :: [String] -> [[Char]] -> Gen ([Expr], [Expr])
generateStates bs ss = do
      let allSlots = permutations ss
      initialSlots <- elements allSlots
      goalSlots <- elements allSlots
      let initialState = initState bs initialSlots
      let goalState = initState bs goalSlots
      return (initialState, goalState)

-- generate instances of Problem with different begin and end states
instance Arbitrary Problem where
      arbitrary = do
                  (bwinitialstate, bwgoalstate) <- generateStates bs ss
                  return $ Problem bwinitialstate bwactions bwgoalstate
          where bs = Plan.generateVariables "box" [1 .. length ss - 1 ] -- 2
                ss = Plan.generateVariables "slot" ['a' .. 'c'] -- 3
                bwactions = generateActions ss bs


-- | Check if solutions are found to example problems (should be but currently
-- isn't -- there's a bug somewhere !)
prop_solutionfound p =
      let r = runSat p 15
      in case r of
          Just as -> True
          Nothing -> False