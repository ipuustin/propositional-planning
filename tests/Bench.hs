{- |
Module         : Main (Criterion)
Copyright      : Copyright (C) 2013 Ismo Puustinen
License        : BSD3
Maintainer     : Ismo Puustinen <ismo@iki.fi>
Stability      : experimental
Portability    : portable

Test problems for the planning library. These are kept in a separate file so
that both tests and benchmarks can use them (with different build
dependencies).
-}

import AI.Planning
import AI.Planning.SatPlan
import Problems

import Criterion.Main
import Data.List

main = defaultMain [
        bench "flashlight problem" $ nf (runSat flprob) 10,
        bench "block world problem 2" $ nf (runSat bwprob2) 10,
        bench "block world problem 3" $ nf (runSat bwprob3) 10
    ]
