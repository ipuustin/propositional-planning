import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import Debug.Trace as Trace
-- package "hatt"
import Data.Logic.Propositional as Prop
import Text.Regex
import Control.Monad

-- package incremental-sat-solver
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

-- The problem is the initial state, list of possible actions, and the
-- desired goal state
data Problem = Problem [Expr] [Action] [Expr]

-- Map the levels to literals and the other way around
type VariableMap = (Map Int String, Map String Int)


-- convert any propositional logic string to conjunctive normal form

-- first replace the biconditionals and conditionals, move negations
-- invard to the literals

cnfReplace (Negation a) = case a of
                Negation i -> cnfReplace i
                Conjunction i j -> Disjunction (cnfReplace (Negation i)) (cnfReplace (Negation j))
                Disjunction i j -> Conjunction (cnfReplace (Negation i)) (cnfReplace (Negation j))
                _ -> Negation $ cnfReplace a
cnfReplace (Conditional a b) = cnfReplace $ Disjunction (Negation a) b
cnfReplace (Biconditional a b) = cnfReplace $ Conjunction (Conditional a b) (Conditional b a) 
cnfReplace (Conjunction a b) = Conjunction (cnfReplace a) (cnfReplace b)
cnfReplace (Disjunction a b) = Disjunction (cnfReplace a) (cnfReplace b)
cnfReplace (Variable x) = Variable x

-- distribute disjunction over conjunction wherever possible

cnfDist (Conjunction a b) = Conjunction (cnfDist a) (cnfDist b)

cnfDist (Disjunction (Conjunction x y) a) = Conjunction (cnfDist $ Disjunction x a) (cnfDist $ Disjunction y a) 
cnfDist (Disjunction a (Conjunction x y)) = Conjunction (cnfDist $ Disjunction a x) (cnfDist $ Disjunction a y) 

cnfDist (Disjunction a b) = let
        a' = cnfDist a
        b' = cnfDist b
    in
        if (a /= a' || b /= b') then
            cnfDist $ Disjunction a' b'
        else
            Disjunction a' b'

-- variables and negations
cnfDist x = x

toCnf :: Expr -> Expr
toCnf e = cnfDist $ cnfReplace e


exprMap f (Negation a) = Negation (exprMap f a)
exprMap f (Conditional a b) = Conditional (exprMap f a) (exprMap f b)
exprMap f (Biconditional a b) = Biconditional (exprMap f a) (exprMap f b)
exprMap f (Conjunction a b) = Conjunction (exprMap f a) (exprMap f b)
exprMap f (Disjunction a b) = Disjunction (exprMap f a) (exprMap f b)
exprMap f (Variable a) = Variable $ f a

exprWalk f (Variable a) = [f a]
exprWalk f (Negation a) = exprWalk f a
exprWalk f (Conjunction a b) = exprWalk f a ++ exprWalk f b
exprWalk f (Disjunction a b) = exprWalk f a ++ exprWalk f b
exprWalk f (Biconditional a b) = exprWalk f a ++ exprWalk f b
exprWalk f (Conditional a b) = exprWalk f a ++ exprWalk f b



-- add the level integer to variables (literals) to indicate time
-- TODO: could this be a monad ("variable in context")?
toLVar x = exprMap (\v -> v ++ "_" ++ show x)

-- gather all possible fluents (conditions) from the actions

findFluents :: ActionData a => [a] -> [Expr]
findFluents = foldl getpreds [] -- contains duplicates?
        where getpreds acc a = acc ++ preconditions a ++ effects a


safeGatherConjunction :: [Expr] -> Expr
safeGatherConjunction (a:[]) = a
safeGatherConjunction (a:as) = foldl Conjunction a as


gatherConjunction :: [Expr] -> Maybe Expr
gatherConjunction (a:[]) = Just a
gatherConjunction [] = Nothing
gatherConjunction (a:as) = Just $ foldl Conjunction a as

gatherDisjunction :: [Expr] -> Maybe Expr
gatherDisjunction (a:[]) = Just a
gatherDisjunction [] = Nothing
gatherDisjunction (a:as) = Just $ foldl Disjunction a as

-- successor-state axioms, precondition axioms, action exclusion axioms

createSuccessorStateAxiom :: Expr -> [Action] -> [Action] -> Int -> Expr
createSuccessorStateAxiom f doers undoers t = let
          next = t + 1
          actioncauses = gatherDisjunction $ map (Variable . name) doers
          actiondeletes = gatherDisjunction $ map (Variable . name) undoers
    in
          case (actioncauses, actiondeletes) of
                (Just ac, Just ad) -> Biconditional (toLVar next f) (toLVar t $ Disjunction ac (Conjunction f (Negation ad)))
                (Just ac, Nothing) -> Biconditional (toLVar next f) (toLVar t $ Disjunction ac f)
                (Nothing, Just ad) -> Biconditional (toLVar next f) (toLVar t $ Conjunction f (Negation ad))
                (Nothing, Nothing) -> Biconditional (toLVar next f) (toLVar t f)


findSuccessors :: [Action] -> [Expr] -> Int -> Maybe Expr
findSuccessors as fs t = let
          axioms = foldl getFluentAxiom [] fs
          getFluentAxiom acc f = createSuccessorStateAxiom f (doers f) (undoers f) t :acc
          doers f = filter (hasInEffects f) as
          undoers f = filter (hasInEffects $ cnfReplace $ Negation f) as
          hasInEffects f a = f `elem` effects a
    in
          gatherConjunction axioms


-- effects of one action are in contradiction with preconditions of another action

interference :: Action -> Action -> Bool
interference a1 a2 = let
          ef1 = effects a1
          ef2 = effects a2
          pre1 = preconditions a1
          pre2 = preconditions a2
    in any Prop.isContradiction [Conjunction ex1 ex2 | ex1 <- ef1, ex2 <- pre2]
        || any Prop.isContradiction [Conjunction ex1 ex2 | ex1 <- pre1, ex2 <- ef2]

-- TODO: now we get duplicates not(a1 & a2) && not(a2 and a1) ?

findExclusions :: [Action] -> Maybe Expr
findExclusions actions = let
          mutexes = [(a1, a2) | a1 <- actions, a2 <- actions, a1 /= a2 && interference a1 a2]
          pair (a1, a2) = Negation $ Conjunction (Variable $ name a1) (Variable $ name a2)
    in
          gatherConjunction $ map pair mutexes


findPreconditions :: [Action] -> Maybe Expr
findPreconditions as = let
          axioms = [Conditional (Variable $ name a) (safeGatherConjunction $ preconditions a) | a <- as, not . null $ preconditions a]
    in
          gatherConjunction axioms


createConjunction :: Maybe Expr -> Maybe Expr -> Maybe Expr
createConjunction ma mb = case (ma, mb) of
    (Just a, Nothing) -> Just a
    (Nothing, Just b) -> Just b
    (Just a, Just b) -> Just $ Conjunction a b
    (Nothing, Nothing) -> Nothing


findAllSuccessors :: [Action] -> [Expr] -> Int -> Maybe Expr
findAllSuccessors as fs tmax = let
          preconditionexpr = findPreconditions as
          exclusionexpr = findExclusions as
          successorexpr = findSuccessors as fs
          exprsatlevel t = createConjunction (successorexpr t) (fmap (toLVar t) $ createConjunction preconditionexpr exclusionexpr)
    in
          foldl createConjunction Nothing [exprsatlevel x | x <- [0 .. tmax]]


createMapping :: Expr -> VariableMap
createMapping expr = let vs = List.nub $ exprWalk show expr
    in (Map.fromList $ zip [1..] vs, Map.fromList $ zip vs [1..])

-- create the CNF and the mapping from the problem

translateToSat :: Problem -> Int -> Maybe (Expr, VariableMap)
translateToSat prob tmax =
    do
        cnfexpr <- fmap cnfReplace $ translateToExpr prob tmax
        let mapping = createMapping cnfexpr
        return (cnfexpr, mapping)


translateToExpr :: Problem -> Int -> Maybe Expr
translateToExpr (Problem initials actions goals) tmax = let
          i:is = map (toCnf . toLVar 0) initials
          g:gs = map (toCnf . toLVar tmax) goals
          fluents = List.nub $ findFluents actions ++ initials ++ goals
          startexpr = foldl Conjunction i is
          successorexpr = findAllSuccessors actions fluents (tmax-1)
          goalexpr = foldl Conjunction g gs
    in
          createConjunction successorexpr $ Just $ Conjunction startexpr goalexpr


disjunctionToList :: Map String Int -> Expr -> [Int]
disjunctionToList stoi (Disjunction a b) = disjunctionToList stoi a ++ disjunctionToList stoi b
disjunctionToList stoi (Variable a) = case Map.lookup (show a) stoi of Just i -> [i]
disjunctionToList stoi (Negation (Variable a)) = case Map.lookup (show a) stoi of Just i -> [-i]


convertToList :: Map String Int -> Expr -> [[Int]]
convertToList stoi (Conjunction a b) = convertToList stoi a ++ convertToList stoi b
convertToList stoi (Disjunction a b) = [disjunctionToList stoi $ Disjunction a b]
convertToList stoi (Variable a) = [disjunctionToList stoi $ Variable a]
convertToList stoi (Negation (Variable a)) = [disjunctionToList stoi $ Negation (Variable a)]


convertToBoolean stoi (Negation a) = Not (convertToBoolean stoi a)
convertToBoolean stoi (Conjunction a b) = (convertToBoolean stoi a) :&&: (convertToBoolean stoi b)
convertToBoolean stoi (Disjunction a b) = (convertToBoolean stoi a) :||: (convertToBoolean stoi b)
convertToBoolean stoi (Variable a) = case Map.lookup (show a) stoi of
        Just i -> Var i


-- run the sat solver

convertToSolver stoi expr = convertToBoolean stoi expr

satSolve :: Problem -> Int -> Maybe [(Int, String)]
satSolve prob@(Problem i as g) t = do
                    (expr, vmap) <- translateToSat prob t
                    s <- assertTrue (convertToSolver (snd vmap) expr) newSatSolver
                    res <- solve s
                    return $ List.sort $ filter isaction $ map (getResultPair res) (Map.toAscList $ fst vmap)
        where look result (i, s) = do
                    b <- lookupVar i result
                    [literal, level] <- matchRegex reg s
                    if (b)
                        then return (read level :: Int, literal)
                        else return (-1, "")
              getResultPair result pair = case look result pair of
                    Just s -> s
              actionnames = map name as
              isaction x = snd x `elem` actionnames
              reg = mkRegex "\"(.*)_([0-9]*)\"" -- capture "foobar" and "23" from ""foobar_23""


-- run the sat solver with increasing number of levels until success or
-- level cap is reached

runSat :: Problem -> Int -> Maybe [(Int, String)]
runSat prob tmax = runSatInstance 0 tmax
        where runSatInstance t tmax = case satSolve prob t of
                    Nothing -> if t < tmax then runSatInstance (t+1) tmax else Nothing
                    result -> result

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

