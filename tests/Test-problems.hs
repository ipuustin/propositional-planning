import AI.Planning.SatPlan


-- flashlight domain, expected outcome:
-- Just [(0,"RemoveCap()"),(1,"Insert(Battery1)"),(1,"Insert(Battery2)"),(2,"PlaceCap()")]

flactions = [a, b, c, d]
    where a = Action "PlaceCap()" [Negation (Variable "On(Cap)")] [Variable "On(Cap)"] 1
          b = Action "RemoveCap()" [Variable "On(Cap)"] [Negation (Variable "On(Cap)")] 1
          c = Action "Insert(Battery1)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery1)")] [Variable "In(Battery1)"] 1
          d = Action "Insert(Battery2)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery2)")] [Variable "In(Battery2)"] 1

flinitialstate = [Variable "On(Cap)", Negation (Variable "In(Battery1)"), Negation (Variable "In(Battery2)")]

flgoalstate = [Variable "On(Cap)", Variable "In(Battery1)", Variable "In(Battery2)"]

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

