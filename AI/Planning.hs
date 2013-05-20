{- |
Module         : AI.Planning
Copyright      : Copyright (C) 2012 Ismo Puustinen
License        : BSD3
Maintainer     : Ismo Puustinen <ismo@iki.fi>
Stability      : experimental
Portability    : portable

A library for solving propositional logic planning problems.
-}

module AI.Planning (ActionData(..),
                    Action(..),
                    Expr(..),
                    Problem(..),
                    toCnf,
                    cnfReplace,
                    exprMap,
                    exprWalk,
                    exprEval,
                    isContradiction,
                    generateVariables)

where


import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import Control.Monad


type Cost = Int
type Precondition = Expr
type Effect = Expr

data Expr = Conjunction Expr Expr
          | Disjunction Expr Expr
          | Negation Expr
          | Implication Expr Expr
          | Biconditional Expr Expr
          | Variable String
          deriving (Show, Eq)

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

-- | Action contains the action name, the preconditions the action has, the
-- effects the action has, and the action cost.
data Action = Action String [Precondition] [Effect] Cost
            deriving (Show, Eq)

-- | The problem is the initial state, list of possible actions, and the
-- desired goal state.
data Problem = Problem [Expr] [Action] [Expr]



-- helper functions


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

-- | Convert any propositional logic string to conjunctive normal form.
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


-- evaluate the Expr value with certain mapping - a truth table row
exprEval :: Expr -> Map String Bool -> Bool
exprEval (Variable a) mapping = case Map.lookup a mapping of Just b -> b
exprEval (Negation a) mapping = not $ exprEval a mapping
exprEval (Conjunction a b) mapping = (&&) (exprEval a mapping) (exprEval b mapping)
exprEval (Disjunction a b) mapping = (||) (exprEval a mapping) (exprEval b mapping)
exprEval (Biconditional a b) mapping = (==) (exprEval a mapping) (exprEval b mapping)
exprEval (Implication a b) mapping = not (exprEval a mapping) || exprEval b mapping


-- create all possible mappings of strings to booleans
createBooleanMappings :: [String] -> [Map String Bool]
createBooleanMappings vs = map (Map.fromList . zip vs) assignments
    where assignments = replicateM (length vs) [True, False]

-- if there is an assignment of values that makes the expression true, the expression is not a contradiction
isContradiction :: Expr -> Bool
isContradiction expr = let
          -- walk through the expression and get all unique variables out
          values = List.nub $ exprWalk id expr
          -- assign Trues and Falses to the variables
          mappings = createBooleanMappings values
    in
          -- build a boolean expression using the assignments, see if False with all values
          not $ any (exprEval expr) mappings


-- generate variable names given name and possible values
generateVariables :: Show a => String -> [a] -> [String]
generateVariables fn pvs = [fn ++ "_" ++ show vn | vn <- pvs]



