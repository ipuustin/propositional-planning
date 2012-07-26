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

-- mutex support for actions


-- testing

flactions = [a, b, c, d]
    where a = Action "PlaceCap()" [Negation (Variable "On(Cap)")] [Variable "On(Cap)"] 1
          b = Action "RemoveCap()" [Variable "On(Cap)"] [Negation (Variable "On(Cap)")] 1
          c = Action "Insert(Battery1)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery1)")] [Variable "In(Battery1)"] 1
          d = Action "Insert(Battery2)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery2)")] [Variable "In(Battery2)"] 1

flinitialstate = [Variable "On(Cap)", Negation (Variable "In(Battery1)"), Negation (Variable "In(Battery2)")]

flgoalstate = [Variable "On(Cap)", Variable "In(Battery1)", Variable "In(Battery2)"]

