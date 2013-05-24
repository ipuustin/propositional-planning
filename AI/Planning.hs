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
                    cnfPushNegation, -- testing
                    cnfDist, -- testing
                    exprMap,
                    exprWalk,
                    exprEval,
                    isContradiction,
                    isTautology,
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

-- | move negations invard to the literals
cnfPushNegation (Negation a) = case a of
                Negation i -> cnfPushNegation i
                Conjunction i j -> Disjunction (cnfPushNegation (Negation i)) (cnfPushNegation (Negation j))
                Disjunction i j -> Conjunction (cnfPushNegation (Negation i)) (cnfPushNegation (Negation j))
                x -> Negation x
cnfPushNegation (Conjunction a b) = Conjunction (cnfPushNegation a) (cnfPushNegation b)
cnfPushNegation (Disjunction a b) = Disjunction (cnfPushNegation a) (cnfPushNegation b)
cnfPushNegation x = x

-- | replace the biconditionals and conditionals
cnfLimit :: Expr -> Expr
cnfLimit (Negation a) = Negation $ cnfLimit a
cnfLimit (Implication a b) = cnfLimit $ Disjunction (Negation a) b
cnfLimit (Biconditional a b) = cnfLimit $ Conjunction (Implication a b) (Implication b a)
cnfLimit (Conjunction a b) = Conjunction (cnfLimit a) (cnfLimit b)
cnfLimit (Disjunction a b) = Disjunction (cnfLimit a) (cnfLimit b)
cnfLimit (Variable x) = Variable x

cnfReplace e = cnfPushNegation $ cnfLimit e

-- | distribute disjunction over conjunction wherever possible
cnfDist :: Expr -> Expr
cnfDist (Conjunction a b) = Conjunction (cnfDist a) (cnfDist b)
{-
cnfDist (Disjunction (Conjunction a b) (Conjunction c d))
      = Conjunction 
          (Conjunction 
              (cnfDist $ Disjunction a c) 
              (cnfDist $ Disjunction b c)) 
          (Conjunction 
              (cnfDist $ Disjunction a d) 
              (cnfDist $ Disjunction b d))
-}
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

-- | Future fmap?
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

-- if there is an assignment of values that makes the expression false, the expression is not a tautology
isTautology :: Expr -> Bool
isTautology expr = let
          values = List.nub $ exprWalk id expr
          mappings = createBooleanMappings values
    in
          all (exprEval expr) mappings

-- TODO: suspicious, write tests
removeDuplicates :: [Expr] -> [Expr]
removeDuplicates [] = []
removeDuplicates (e:es) = e : removeDuplicates (filter (\y -> not(isTautology $ Biconditional e y)) es)


-- generate variable names given name and possible values
generateVariables :: Show a => String -> [a] -> [String]
generateVariables fn pvs = [fn ++ "_" ++ show vn | vn <- pvs]
