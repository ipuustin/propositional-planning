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

commonelement group1 group2 = any (`elem` group1) group2


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




tolvar :: Show a => a -> Expr -> Expr
tolvar x (Negation a) = Negation (tolvar x a)
tolvar x (Conditional a b) = Conditional (tolvar x a) (tolvar x b)
tolvar x (Biconditional a b) = Biconditional (tolvar x a) (tolvar x b)
tolvar x (Conjunction a b) = Conjunction (tolvar x a) (tolvar x b)
tolvar x (Disjunction a b) = Disjunction (tolvar x a) (tolvar x b)
tolvar x (Variable a) = Variable $ a ++ "_" ++ (show x)


findpredicates :: ActionData a => [a] -> [Expr]
findpredicates as = List.nub $ foldl getpreds [] as
    where getpreds acc a = acc ++ (preconditions a) ++ (effects a)


gatherconjunction :: [Expr] -> Expr
gatherconjunction (a:[]) = a
gatherconjunction [] = Variable "TODO"
gatherconjunction (a:as) = foldl Conjunction a as

gatherdisjunction :: [Action] -> Expr
gatherdisjunction (a:[]) = Variable $ name a
gatherdisjunction [] = Variable "TODO"
gatherdisjunction (a:as) = foldl Disjunction (Variable $ name a) (map (Variable . name) as)

createsuccessorstateaxiom :: Expr -> [Action] -> [Action] -> Int -> Expr
createsuccessorstateaxiom f doers undoers t = axiom
    where prev = t - 1
          actioncauses f = gatherdisjunction doers
          actiondeletes = gatherdisjunction undoers
          axiom = Biconditional (tolvar t f) (tolvar prev $ Disjunction (actioncauses f) (Disjunction f (Negation actiondeletes)))



findsuccessors :: [Action] -> [Expr] -> Int -> Int -> Expr
findsuccessors as fs time currenttime = expression
    where axioms = foldl getfluentaxiom [] fs
          getfluentaxiom acc f = (createsuccessorstateaxiom f (doers f) (undoers f) currenttime) : acc
          doers f = filter (hasineffects f) as
          undoers f = filter (hasineffects (Negation f)) as
          hasineffects f a = any (== f) (effects a)
          expression = gatherconjunction axioms

findaxioms :: [Expr] -> [Action] -> Int -> Expr
findaxioms predicates actions time = Conjunction successorexpr (Conjunction preconditionexpr exclusionexpr)
    where successorexpr = findsuccessors actions predicates time 1
          preconditionexpr = undefined
          exclusionexpr = undefined

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
          predicates = findpredicates actions
-- successor-state axioms, precondition axioms, action exclusion axioms



-- testing

flactions = [a, b, c, d]
    where a = Action "PlaceCap()" [Negation (Variable "On(Cap)")] [Variable "On(Cap)"] 1
          b = Action "RemoveCap()" [Variable "On(Cap)"] [Negation (Variable "On(Cap)")] 1
          c = Action "Insert(Battery1)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery1)")] [Variable "In(Battery1)"] 1
          d = Action "Insert(Battery2)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery2)")] [Variable "In(Battery2)"] 1

flinitialstate = [Variable "On(Cap)", Negation (Variable "In(Battery1)"), Negation (Variable "In(Battery2)")]

flgoalstate = [Variable "On(Cap)", Variable "In(Battery1)", Variable "In(Battery2)"]

