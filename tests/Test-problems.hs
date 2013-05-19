import AI.Planning
import AI.Planning.SatPlan
import Criterion.Main
import Data.List

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



assignVariables :: String -> [String] -> String
assignVariables fn vs = fn ++ "(" ++ (intercalate "," vs) ++ ")"

-- block world -- (http://icaps06.icaps-conference.org/dc-papers/paper5.pdf)

-- FIXME: the Negation(Variable("In()")) clauses are missing

emptySlot :: [String] -> String -> [Expr]
emptySlot bs s = [ Negation $ Variable ("In("++b++","++s++")") | b <- bs ]

setBoxToSlot bs s b = boxInSlot : otherBoxes
    where boxInSlot = Variable ("In("++b++","++s++")")
          otherBoxes = [ Negation $ Variable ("In("++ob++","++s++")") | ob <- bs, ob /= b ]

emptyHandler bs = [ Negation $ Variable ("Holding("++b++")") | b <- bs ]

setBoxToHandler b bs = boxInHandler : otherBoxes
    where boxInHandler = Variable ("Holding("++b++")")
          otherBoxes = [ Negation $ Variable ("Holding("++ob++")") | ob <- bs, ob /= b ]

boxes = generateVariables "box" ['a'..'b']
slots = generateVariables "slot" [1..3]

getBox a = head $ generateVariables "box" [a]
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
    where slot1 = setBoxToSlot boxes (getSlot 2) (getBox 'a')
          slot2 = setBoxToSlot boxes (getSlot 3) (getBox 'b')
          slot3 = emptySlot boxes $ getSlot 1

-- not working for some reason
bwprob1 = Problem bwstate1 bwactions bwstate2

bwprob2 = Problem bwstate2 bwactions bwstate3

bwprob3 = Problem bwstate1 bwactions bwstate3

-- main program benchmarks flashlight problem

main = defaultMain [
		bench "flashlight problem" $ nf (runSat flprob) 10,
		bench "block world problem 2" $ nf (runSat bwprob2) 10,
    bench "block world problem 3" $ nf (runSat bwprob3) 10
	]
