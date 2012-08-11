import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import Debug.Trace as Trace
-- import qualified Text.Groom as Groom

-- package "hatt"
import Data.Logic.Propositional as Prop

-- package "incremental-sat-solver"
import Data.Boolean.SatSolver

type Cost = Int
type Precondition = Expr
type Effect = Expr

class ActionData a where
  preconditions :: a -> [Precondition]
  effects       :: a -> [Effect]
  name          :: a -> String
  cost          :: a -> Int

instance ActionData Action where
    preconditions (Action _ p _ _) = p
    effects (Action _ _ e _) = e
    name (Action n _ _ _) = n
    cost (Action _ _ _ c) = c

data Action = Action String [Precondition] [Effect] Cost
            deriving (Show, Eq)

-- Result of the whole computation is a list of actions the agent
-- must take to complete the plan, or Impossible if the goal could not
-- be reached.
data Plan = Plan [Action] | Impossible deriving (Show)

-- The problem is the initial state, list of possible actions, and the
-- desired goal state
data Problem = Problem [Expr] [Action] [Expr]

type VariableMapping = [(Int, Expr)]

type LeveledVariable = (Int, Expr)

-- helper functions

subset smallgroup biggroup = all (`elem` biggroup) smallgroup

commonelement group1 = any (`elem` group1)


-- convert any propositional logic string to conjunctive normal form

-- first replace the biconditionals and conditionals, move negations
-- invard to the literals

cnfreplace (Negation a) = case a of
                Negation i -> cnfreplace i
                Conjunction i j -> Disjunction (cnfreplace (Negation i)) (cnfreplace (Negation j))
                Disjunction i j -> Conjunction (cnfreplace (Negation i)) (cnfreplace (Negation j))
                _ -> Negation $ cnfreplace a

cnfreplace (Conditional a b) = cnfreplace $ Disjunction (Negation a) b

cnfreplace (Biconditional a b) = cnfreplace $ Conjunction (Conditional a b) (Conditional b a) 

cnfreplace (Conjunction a b) = Conjunction (cnfreplace a) (cnfreplace b)

cnfreplace (Disjunction a b) = Disjunction (cnfreplace a) (cnfreplace b)

cnfreplace (Variable x) = Variable x

-- finally distribute disjunction over conjunction wherever possible

cnfdist (Conjunction a b) = Conjunction (cnfdist a) (cnfdist b)

cnfdist (Disjunction a b) = dist a b
    where dist (Conjunction i j) (Conjunction k l) =
                    Disjunction (cnfdist $ Conjunction i j) (cnfdist $ Conjunction k l)
          dist (Conjunction i j) k = Conjunction (cnfdist $ Disjunction i k) (cnfdist $ Disjunction j k)
          dist i (Conjunction j k) = Conjunction (cnfdist $ Disjunction i j) (cnfdist $ Disjunction i k)
          dist a b = Disjunction (cnfdist a) (cnfdist b)

cnfdist e = e -- negations and variables

tocnf :: Expr -> Expr
tocnf e = cnfdist $ cnfreplace e

-- add the level integer to variables (literals) to indicate time

tolvar :: Show a => a -> Expr -> Expr
tolvar x (Negation a) = Negation (tolvar x a)
tolvar x (Conditional a b) = Conditional (tolvar x a) (tolvar x b)
tolvar x (Biconditional a b) = Biconditional (tolvar x a) (tolvar x b)
tolvar x (Conjunction a b) = Conjunction (tolvar x a) (tolvar x b)
tolvar x (Disjunction a b) = Disjunction (tolvar x a) (tolvar x b)
tolvar x (Variable a) = Variable $ a ++ "_" ++ show x


-- gather all possible fluents (conditions) from the actions

findfluents :: ActionData a => [a] -> [Expr]
findfluents as = foldl getpreds [] as -- contains duplicates
    where getpreds acc a = acc ++ preconditions a ++ effects a


gatherconjunction :: [Expr] -> Expr
gatherconjunction (a:[]) = a
gatherconjunction [] = Variable "TODO"
gatherconjunction (a:as) = foldl Conjunction a as

gatherdisjunction :: [Expr] -> Maybe Expr
gatherdisjunction (a:[]) = Just a
gatherdisjunction [] = Nothing
gatherdisjunction (a:as) = Just $ foldl Disjunction a as

-- successor-state axioms, precondition axioms, action exclusion axioms

createsuccessorstateaxiom :: Expr -> [Action] -> [Action] -> Int -> Expr
createsuccessorstateaxiom f doers undoers t = let
          next = t + 1
          actioncauses = gatherdisjunction $ map (Variable . name) doers
          actiondeletes = gatherdisjunction $ map (Variable . name) undoers
    in
          case (actioncauses, actiondeletes) of
                (Just ac, Just ad) -> Biconditional (tolvar next f) (tolvar t $ Disjunction ac (Disjunction f (Negation ad)))
                (Just ac, Nothing) -> Biconditional (tolvar next f) (tolvar t $ Disjunction ac f)
                (Nothing, Just ad) -> Biconditional (tolvar next f) (tolvar t $ Disjunction f (Negation ad))
                (Nothing, Nothing) -> Biconditional (tolvar next f) (tolvar t f)

findsuccessors :: [Action] -> [Expr] -> Int -> Expr
findsuccessors as fs t = let
          axioms = foldl getfluentaxiom [] fs
          getfluentaxiom acc f = createsuccessorstateaxiom f (doers f) (undoers f) t :acc
          doers f = filter (hasineffects f) as
          undoers f = filter (hasineffects $ cnfreplace $ Negation f) as
          hasineffects f a = f `elem` effects a
    in
          gatherconjunction axioms

findallsuccessors :: [Action] -> [Expr] -> Int -> Expr
findallsuccessors as fs tmax = let
          preconditionexpr t = undefined
          exclusionexpr t = undefined
          successorexpr t = findsuccessors as fs t
          exprsatlevel t = Conjunction (successorexpr t) (Conjunction (preconditionexpr t) (exclusionexpr t))
          allexprs = [exprsatlevel x | x <- [0 .. tmax]]
    in
          gatherconjunction allexprs

-- create the CNF and the mapping from the problem

translatetosat :: Problem -> Int -> (Expr, VariableMapping)
translatetosat (Problem initials actions goals) time = (cnfexpr, mapping)
    where i:is = map (tocnf . tolvar 0) initials
          g:gs = map (tocnf . tolvar time) goals
          startexpr = foldl Conjunction i is
          successorexpr = undefined
          goalexpr = foldl Conjunction g gs
          cnfexpr = Conjunction startexpr (Conjunction successorexpr goalexpr)
          mapping = []
          fluents = List.nub $ findfluents actions ++ initials ++ goals



-- testing

flactions = [a, b, c, d]
    where a = Action "PlaceCap()" [Negation (Variable "On(Cap)")] [Variable "On(Cap)"] 1
          b = Action "RemoveCap()" [Variable "On(Cap)"] [Negation (Variable "On(Cap)")] 1
          c = Action "Insert(Battery1)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery1)")] [Variable "In(Battery1)"] 1
          d = Action "Insert(Battery2)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery2)")] [Variable "In(Battery2)"] 1

flinitialstate = [Variable "On(Cap)", Negation (Variable "In(Battery1)"), Negation (Variable "In(Battery2)")]

flgoalstate = [Variable "On(Cap)", Variable "In(Battery1)", Variable "In(Battery2)"]

