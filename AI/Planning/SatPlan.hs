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
import Data.Maybe

import Text.Regex

-- import Debug.Trace

-- package incremental-sat-solver
import Data.Boolean.SatSolver as Sat

-- Map the levels to literals and the other way around
type VariableMap = (Map Int String, Map String Int)

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
safeGatherConjunction [] = undefined

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
          hasInEffects f a = f `elem` effects a -- FIXME: do a tautology check? benchmark?
          -- hasInEffects f a = any isTautology $ map (\x -> Biconditional x f) $ effects a  
    in
          gatherConjunction axioms



-- | effects of one action are in contradiction with preconditions of another action
interference :: Action -> Action -> Bool
interference a1 a2 = let
          ef1 = effects a1
          ef2 = effects a2
          pre1 = preconditions a1
          pre2 = preconditions a2
    in any isContradiction [Conjunction ex1 ex2 | ex1 <- ef1, ex2 <- pre2]
        || any isContradiction [Conjunction ex1 ex2 | ex1 <- pre1, ex2 <- ef2]

-- TODO: now we get duplicates not(a1 & a2) && not(a2 and a1) ?

-- | make sure conflicting actions are not run at the same time
findExclusions :: [Action] -> Maybe Expr
findExclusions actions = let
          mutexes = [(a1, a2) | a1 <- actions, a2 <- actions, a1 /= a2 && interference a1 a2]
          pair (a1, a2) = Negation $ Conjunction (Variable $ name a1) (Variable $ name a2)
    in
          gatherConjunction $ map pair mutexes


-- | for each action, if an action is taken all its preconditions must be true (A -> pre(A))
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


translateToExpr :: Problem -> Int -> Maybe Expr
translateToExpr (Problem initials actions goals) tmax = let
          i:is = map (cnfReplace . toLVar 0) initials
          g:gs = map (cnfReplace . toLVar tmax) goals
          fluents = List.nub $ findFluents actions ++ initials ++ goals
          startexpr = foldl Conjunction i is
          successorexpr = findAllSuccessors actions fluents (tmax-1)
          goalexpr = foldl Conjunction g gs
          expr = createConjunction successorexpr $ Just $ Conjunction startexpr goalexpr
    in
          expr
          -- trace ("expression:" ++ show expr) expr


-- | create the CNF and the mapping from the problem
translateToSat :: Problem -> Int -> Maybe (Expr, VariableMap)
translateToSat prob tmax =
    do
        cnfexpr <- fmap cnfReplace $ translateToExpr prob tmax
        let mapping = createMapping cnfexpr
        return (cnfexpr, mapping)


convertToBoolean :: Map String Int -> Expr -> Boolean
convertToBoolean stoi (Negation a) = Not (convertToBoolean stoi a)
convertToBoolean stoi (Conjunction a b) = convertToBoolean stoi a :&&: convertToBoolean stoi b
convertToBoolean stoi (Disjunction a b) = convertToBoolean stoi a :||: convertToBoolean stoi b
convertToBoolean stoi (Variable a) = Sat.Var $ fromMaybe undefined $ Map.lookup (show a) stoi
convertToBoolean _ (Implication _ _) = undefined
convertToBoolean _ (Biconditional _ _) = undefined


-- | Run the sat solver once for a certain action level.
satSolve :: Problem -> Int -> Maybe [(Int, String)]
satSolve prob@(Problem _ as _) t = do
                    (expr, vmap) <- translateToSat prob t
                    s <- assertTrue (convertToBoolean (snd vmap) expr) newSatSolver
                    res <- solve s
                    return $ List.sort $ filter isaction $ map (getResultPair res) (Map.toAscList $ fst vmap)
        where look result (idx, s) = do
                    b <- lookupVar idx result
                    [literal, level] <- matchRegex reg s
                    return (if b then (read level :: Int, literal) else (-1, ""))
              getResultPair result pair = fromMaybe undefined $ look result pair
              actionnames = map name as
              isaction x = snd x `elem` actionnames
              reg = mkRegex "\"(.*)_([0-9]*)\"" -- capture "foobar" and "23" from ""foobar_23""


-- | Run the sat solver with increasing number of levels until success or
-- level cap is reached.
runSat :: Problem -> Int -> Maybe [(Int, String)]
runSat prob tmax = runSatInstance 0
        where runSatInstance t = case satSolve prob t of
                    Nothing -> if t < tmax then runSatInstance (t+1) else Nothing
                    result -> result

