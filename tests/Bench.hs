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
        bench "flashlight problem (using incremental-sat-solver)" $ nf (runSat flprob) 10,
        bench "block world problem 2 (using incremental-sat-solver)" $ nf (runSat bwprob2) 10,
        bench "block world problem 3 (using incremental-sat-solver)" $ nf (runSat bwprob3) 10,
        bench "flashlight problem (using toysolver)" $ nfIO $ runSat' flprob 10,
        bench "block world problem 1 (using toysolver)" $ nfIO $ runSat' bwprob1 10,
        bench "block world problem 2 (using toysolver)" $ nfIO $ runSat' bwprob2 10,
        bench "block world problem 3 (using toysolver)" $ nfIO $ runSat' bwprob3 10,
        bench "flashlight problem (using Surely)" $ nf  (runSatSurely flprob) 10,
        bench "block world problem 1 (using Surely)" $ nf (runSatSurely bwprob1) 10,
        bench "block world problem 2 (using Surely)" $ nf (runSatSurely bwprob2) 10,
        bench "block world problem 3 (using Surely)" $ nf (runSatSurely bwprob3) 10
    ]
