{- |
Module         : Problems
Copyright      : Copyright (C) 2012 Ismo Puustinen
License        : BSD3
Maintainer     : Ismo Puustinen <ismo@iki.fi>
Stability      : experimental
Portability    : portable

Test problems for the planning library. These are kept in a separate file so
that both tests and benchmarks can use them (with different build
dependencies).
-}

module Problems (ActionData(..),
                          Action(..),
                          Expr(..),
                          Problem(..),
                          runSat,
                          flprob,
                          bwprob1,
                          bwprob2,
                          bwprob3)

where

import Data.List
import Test.QuickCheck

import AI.Planning
import AI.Planning.SatPlan

-- flashlight domain, expected outcome:
-- Just [(0,"RemoveCap()"),(1,"Insert(Battery1)"),(1,"Insert(Battery2)"),(1,"Insert(Battery3)"),(1,"Insert(Battery4)"),(2,"PlaceCap()")]

flactions = [a, b, c, d, e, f]
    where a = Action "PlaceCap()" [Negation (Variable "On(Cap)")] [Variable "On(Cap)"] 1
          b = Action "RemoveCap()" [Variable "On(Cap)"] [Negation (Variable "On(Cap)")] 1
          c = Action "Insert(Battery1)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery1)")] [Variable "In(Battery1)"] 1
          d = Action "Insert(Battery2)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery2)")] [Variable "In(Battery2)"] 1
          e = Action "Insert(Battery3)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery3)")] [Variable "In(Battery3)"] 1
          f = Action "Insert(Battery4)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery4)")] [Variable "In(Battery4)"] 1


flinitialstate = [ Variable "On(Cap)",
                   Negation (Variable "In(Battery1)"),
                   Negation (Variable "In(Battery2)"),
                   Negation (Variable "In(Battery3)"),
                   Negation (Variable "In(Battery4)")
				 ]

flgoalstate = [ Variable "On(Cap)",
                Variable "In(Battery1)",
                Variable "In(Battery2)",
                Variable "In(Battery3)",
                Variable "In(Battery4)"
              ]

flprob = Problem flinitialstate flactions flgoalstate

-- blocks on table domain

tbinitialstate = [ Variable "On(A,Table)", Variable "On(B,Table)", Variable "Clear(A)", Variable "Clear(B)" ]
tbgoalstate = [ Variable "On(A,B)"]

-- expected outcome:
-- Just [(0,"Action()")]

actions1 = [a]
    where a = Action "Action()" [Variable "Precondition()"] [Variable "Effect()"] 1

initialstate1 = [Variable "Precondition()", Negation (Variable "Effect()") ]

goalstate1 = [Variable "Effect()"]

prob1 = Problem initialstate1 actions1 goalstate1



-- expected outcome:
-- Just [(0,"Action()")]

actions2 = [a]
    where a = Action "Action()" [Variable "Precondition()"] [Negation (Variable "Effect()")] 1

initialstate2 = [Variable "Precondition()", Variable "Effect()"]

goalstate2 = [Negation (Variable "Effect()")]

prob2 = Problem initialstate2 actions2 goalstate2



-- expected outcome:
-- Nothing

actions3 = [a]
    where a = Action "Action()" [Variable "Precondition()"] [Variable "Effect()"] 1

initialstate3 = [Variable "Precondition()", Variable "Effect()"]

goalstate3 = [Negation (Variable "Effect()")]

prob3 = Problem initialstate3 actions3 goalstate3


-- TODO: these are being moved to automatic testing, see if any interesting
-- manual cases are required.

assignVariables :: String -> [String] -> String
assignVariables fn vs = fn ++ "(" ++ intercalate "," vs ++ ")"

-- block world -- (http://icaps06.icaps-conference.org/dc-papers/paper5.pdf)

boxes = generateVariables "box" ['a'..'b']
slots = generateVariables "slot" [1..3]

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

bwactions = pickups ++ putdowns
    where pickups  = [ Action ("Pickup("++b++","++s++")")
                             (pickupPreconditions s b)
                             (pickupEffects s b)
                             1
                    | b <- boxes, s <- slots ]
          putdowns = [ Action ("Putdown("++b++","++s++")")
                             (putdownPreconditions s b)
                             (putdownEffects s b)
                             1
                    | b <- boxes, s <- slots ]

          pickupPreconditions s b = setBoxToSlot boxes s b ++ emptyHandler boxes
          pickupEffects s b = emptySlot boxes s ++ setBoxToHandler b boxes

          putdownPreconditions s b = setBoxToHandler b boxes ++ emptySlot boxes s
          putdownEffects s b = setBoxToSlot boxes s b ++ emptyHandler boxes

bwstate1 = emptyHandler boxes ++ slot3 ++ slot2 ++ slot1
    where slot1 = setBoxToSlot boxes (getSlot 1) (getBox 'a')
          slot2 = setBoxToSlot boxes (getSlot 2) (getBox 'b')
          slot3 = emptySlot boxes $ getSlot 3

bwstate2 = emptyHandler boxes ++ slot3 ++ slot2 ++ slot1
    where slot1 = setBoxToSlot boxes (getSlot 1) (getBox 'b')
          slot2 = setBoxToSlot boxes (getSlot 2) (getBox 'a')
          slot3 = emptySlot boxes $ getSlot 3

bwstate3 = emptyHandler boxes ++ slot3 ++ slot2 ++ slot1
    where slot1 = emptySlot boxes $ getSlot 1
          slot2 = setBoxToSlot boxes (getSlot 2) (getBox 'a')
          slot3 = setBoxToSlot boxes (getSlot 3) (getBox 'b')

-- not working for some reason
bwprob1 = Problem bwstate1 bwactions bwstate2

bwprob2 = Problem bwstate2 bwactions bwstate3

bwprob3 = Problem bwstate1 bwactions bwstate3

bwstate2b = setBoxToHandler (getBox 'a') boxes ++ slot3 ++ slot2 ++ slot1
    where slot3 = emptySlot boxes $ getSlot 3
          slot2 = emptySlot boxes $ getSlot 2
          slot1 = setBoxToSlot boxes (getSlot 1) (getBox 'b')

-- not working!
bwprob1b = Problem bwstate1 bwactions bwstate2b

