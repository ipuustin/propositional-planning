propositional-planning
======================

This is a Haskell library for solving classical planning problems. At
the moment the algorithm implemented is "planning as satisfiability"
(SATPLAN, see <http://en.wikipedia.org/wiki/Satplan>).

Some example problems are located in "tests" directory. For instance, to
solve the flashlight battery loading test problem, load the
tests/Test-problems.hs file and say:

    runSat flprob 10

The future versions of the library might have also support for other
kinds of planning, such as graph planning (GRAPHPLAN).
