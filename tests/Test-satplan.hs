import AI.Planning.SatPlan


-- testing

flactions = [a, b, c, d]
    where a = Action "PlaceCap()" [Negation (Variable "On(Cap)")] [Variable "On(Cap)"] 1
          b = Action "RemoveCap()" [Variable "On(Cap)"] [Negation (Variable "On(Cap)")] 1
          c = Action "Insert(Battery1)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery1)")] [Variable "In(Battery1)"] 1
          d = Action "Insert(Battery2)" [Negation (Variable "On(Cap)"), Negation (Variable "In(Battery2)")] [Variable "In(Battery2)"] 1

flinitialstate = [Variable "On(Cap)", Negation (Variable "In(Battery1)"), Negation (Variable "In(Battery2)")]

flgoalstate = [Variable "On(Cap)", Variable "In(Battery1)", Variable "In(Battery2)"]

flprob = Problem flinitialstate flactions flgoalstate



actions1 = [a]
    where a = Action "Action()" [Variable "Precondition()"] [Variable "Effect()"] 1

initialstate1 = [Variable "Precondition()", Negation (Variable "Effect()") ]

goalstate1 = [Variable "Effect()"]

prob1 = Problem initialstate1 actions1 goalstate1



actions2 = [a]
    where a = Action "Action()" [Variable "Precondition()"] [Negation (Variable "Effect()")] 1

initialstate2 = [Variable "Precondition()", Variable "Effect()"]

goalstate2 = [Negation (Variable "Effect()")]

prob2 = Problem initialstate2 actions2 goalstate2

