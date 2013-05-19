{- |
Module         : AI.Planning.SatPlan
Copyright      : Copyright (C) 2012 Ismo Puustinen
License        : BSD3
Maintainer     : Ismo Puustinen <ismo@iki.fi>
Stability      : experimental
Portability    : portable

A library for solving planning problems using the "planning as satisfiability"
(SATPLAN) algorithm.
-}

module AI.Planning.SatPlan (Action(..),
                            Problem(..),
                            ActionData(..),
                            Expr(..),
                            runSat,
                            satSolve)

where

import AI.Planning

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List

import Control.Monad
import Text.Regex

-- package incremental-sat-solver
import Data.Boolean.SatSolver as Sat

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
cnfReplace (Implication a b) = cnfReplace $ Disjunction (Negation a) b
cnfReplace (Biconditional a b) = cnfReplace $ Conjunction (Implication a b) (Implication b a)
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
        if a /= a' || b /= b' then
            cnfDist $ Disjunction a' b'
        else
            Disjunction a' b'

-- variables and negations
cnfDist x = x

toCnf :: Expr -> Expr
toCnf e = cnfDist $ cnfReplace e

exprMap :: (String -> String) -> Expr -> Expr
exprMap f (Negation a) = Negation (exprMap f a)
exprMap f (Implication a b) = Implication (exprMap f a) (exprMap f b)
exprMap f (Biconditional a b) = Biconditional (exprMap f a) (exprMap f b)
exprMap f (Conjunction a b) = Conjunction (exprMap f a) (exprMap f b)
exprMap f (Disjunction a b) = Disjunction (exprMap f a) (exprMap f b)
exprMap f (Variable a) = Variable $ f a

exprWalk :: (String -> t) -> Expr -> [t]
exprWalk f (Variable a) = [f a]
exprWalk f (Negation a) = exprWalk f a
exprWalk f (Conjunction a b) = exprWalk f a ++ exprWalk f b
exprWalk f (Disjunction a b) = exprWalk f a ++ exprWalk f b
exprWalk f (Biconditional a b) = exprWalk f a ++ exprWalk f b
exprWalk f (Implication a b) = exprWalk f a ++ exprWalk f b



-- add the level integer to variables (literals) to indicate time
-- TODO: could this be a monad ("variable in context")?
toLVar :: Int -> Expr -> Expr
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


-- create all possible mappings of strings to booleans
createBooleanMappings :: [String] -> [Map String Bool]
createBooleanMappings vs = map (Map.fromList . zip vs) assignments
    where assignments = replicateM (length vs) [True, False]


-- evaluate the Expr value with certain mapping - a truth table row
evalExpr :: Expr -> Map String Bool -> Bool
evalExpr (Variable a) mapping = case Map.lookup a mapping of Just b -> b
evalExpr (Negation a) mapping = not $ evalExpr a mapping
evalExpr (Conjunction a b) mapping = (&&) (evalExpr a mapping) (evalExpr b mapping)
evalExpr (Disjunction a b) mapping = (||) (evalExpr a mapping) (evalExpr b mapping)
evalExpr (Biconditional a b) mapping = (==) (evalExpr a mapping) (evalExpr b mapping)
evalExpr (Implication a b) mapping = not (evalExpr a mapping) || evalExpr b mapping


-- if there is an assignment of values that makes the expression true, the expression is not a contradiction
isContradiction :: Expr -> Bool
isContradiction expr = let
          -- walk through the expression and get all unique variables out
          values = List.nub $ exprWalk id expr
          -- assign Trues and Falses to the variables
          mappings = createBooleanMappings values
    in
          -- build a boolean expression using the assignments, see if False with all values
          not $ any (evalExpr expr) mappings


-- effects of one action are in contradiction with preconditions of another action
interference :: Action -> Action -> Bool
interference a1 a2 = let
          ef1 = effects a1
          ef2 = effects a2
          pre1 = preconditions a1
          pre2 = preconditions a2
    in any isContradiction [Conjunction ex1 ex2 | ex1 <- ef1, ex2 <- pre2]
        || any isContradiction [Conjunction ex1 ex2 | ex1 <- pre1, ex2 <- ef2]

-- TODO: now we get duplicates not(a1 & a2) && not(a2 and a1) ?

findExclusions :: [Action] -> Maybe Expr
findExclusions actions = let
          mutexes = [(a1, a2) | a1 <- actions, a2 <- actions, a1 /= a2 && interference a1 a2]
          pair (a1, a2) = Negation $ Conjunction (Variable $ name a1) (Variable $ name a2)
    in
          gatherConjunction $ map pair mutexes


findPreconditions :: [Action] -> Maybe Expr
findPreconditions as = let
          axioms = [Implication (Variable $ name a) (safeGatherConjunction $ preconditions a) | a <- as, not . null $ preconditions a]
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


-- translate from Expr format to integers (for incremental SAT solver), keep the mapping
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


convertToBoolean :: Map String Int -> Expr -> Boolean
convertToBoolean stoi (Negation a) = Not (convertToBoolean stoi a)
convertToBoolean stoi (Conjunction a b) = convertToBoolean stoi a :&&: convertToBoolean stoi b
convertToBoolean stoi (Disjunction a b) = convertToBoolean stoi a :||: convertToBoolean stoi b
convertToBoolean stoi (Variable a) = case Map.lookup (show a) stoi of
        Just i -> Sat.Var i


-- | Run the sat solver once for a certain action level.
satSolve :: Problem -> Int -> Maybe [(Int, String)]
satSolve prob@(Problem i as g) t = do
                    (expr, vmap) <- translateToSat prob t
                    s <- assertTrue (convertToBoolean (snd vmap) expr) newSatSolver
                    res <- solve s
                    return $ List.sort $ filter isaction $ map (getResultPair res) (Map.toAscList $ fst vmap)
        where look result (i, s) = do
                    b <- lookupVar i result
                    [literal, level] <- matchRegex reg s
                    return (if b then (read level :: Int, literal) else (-1, ""))
              getResultPair result pair = case look result pair of
                    Just s -> s
              actionnames = map name as
              isaction x = snd x `elem` actionnames
              reg = mkRegex "\"(.*)_([0-9]*)\"" -- capture "foobar" and "23" from ""foobar_23""


-- | Run the sat solver with increasing number of levels until success or
-- level cap is reached.
runSat :: Problem -> Int -> Maybe [(Int, String)]
runSat prob tmax = runSatInstance 0 tmax
        where runSatInstance t tmax = case satSolve prob t of
                    Nothing -> if t < tmax then runSatInstance (t+1) tmax else Nothing
                    result -> result

