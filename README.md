# Lambda calculus evaluator Alonzo N.B.E

Named after Alonzo Church and the normalization strategy that is being used.

Features:

 * Normalization by evaluation
 * Bidirectional typing
 * Avoids introduction of external dependencies,
   therefore fairly easy to build.
 * On an error, marks the failure point and resets parsing on the next blank line.
 * Informs about missing declarations and judgements
 * `Main.txt` documentation that you scroll side-by-side with source code.
   You can use scrollbind in Vim to do this.

Planned:

 * Amicable to user errors

Objectives:

 * Leave a succinct, readable and documented
   implementation of lambda calculus.
 * Explore user-interfaces in proof assistants.
 * Maybe come up with some real usecase for a lambda calculus implementation.

Obstacles:

 1. Insufficiently documented.
    1. References to papers and pages introducing algorithms
       or techniques being used are partially missing.
    2. The source code remains very lightly documented.
 2. It'd be nice to inline annotate structures.
 3. Pretty printing not present.
 4. Objectives are still open.
    Not entirely clear what is the extent of the exploration.
    No conclusion decided.

`cabal install .` produces an executable named `lc-nbe`

## References and papers

All the references in this project.
The `[N]` marking used in this directory with some number `N` indexes this list.

 1. [Checking Dependent Types with Normalization by Evaluation: A Tutorial](http://www.davidchristiansen.dk/tutorials/nbe/),
    [(Haskell Version)](http://davidchristiansen.dk/tutorials/implementing-types-hs.pdf) | David Thrane Christiansen
 2. [FUNCTIONAL PEARLS: Monadic Parsing in Haskell](http://www.cs.nott.ac.uk/~pszgmh/pearl.pdf) | Graham Hutton, Erik Meijer
