import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import Debug.Trace as Trace
-- import qualified Text.Groom as Groom

-- package "hatt"
import Data.Logic.Propositional as Prop

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


-- testing

flactions = [a, b, c, d]
    where a = Action "PlaceCap()" [Negation (Variable "On(Cap)")] [Variable "On(Cap)"] 1
          b = Action "RemoveCap()" [Variable "On(Cap)"] [Negation (Variable "On(Cap)")] 1
          c = Action "Insert(Battery1)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery1)")] [Variable "In(Battery1)"] 1
          d = Action "Insert(Battery2)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery2)")] [Variable "In(Battery2)"] 1

flinitialstate = [Variable "On(Cap)", Negation (Variable "In(Battery1)"), Negation (Variable "In(Battery2)")]

flgoalstate = [Variable "On(Cap)", Variable "In(Battery1)", Variable "In(Battery2)"]

