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
                    Problem(..))

where

-- package "hatt"
import Data.Logic.Propositional

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

-- | Action contains the action name, the preconditions the action has, the
-- effects the action has, and the action cost.
data Action = Action String [Precondition] [Effect] Cost
            deriving (Show, Eq)

-- | The problem is the initial state, list of possible actions, and the
-- desired goal state.
data Problem = Problem [Expr] [Action] [Expr]
