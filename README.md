# Lambda calculus evaluator Alonzo N.B.E

Named after Alonzo Church and the normalization strategy that is being used.

Features:

 * Skeleton functionality.

Planned:

 * Normalization by evaluation (needs typechecking to ensure results are valid)
 * Bidirectional typing
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
    2. The source code remains undocumented.
       Thinking of doing it with `Main.txt` you're supposed to scroll
       side-by-side with code, but would be readable individually as well.
 2. Stops on the first syntax error.
 3. No typechecking implemented.
 4. Pretty printing not present.
 5. Does not inform about missing judgements or definitions.
 6. No inference functionality.
 7. Objectives are still open.
    Not entirely clear what is the extent of the exploration.
    No conclusion decided.

`cabal install .` produces an executable named `lc-nbe`

## References and papers

This is a collected list of all the references in this project.
The `[N]` marking used in this directory with some number `N` indexes this list.

 1. [Checking Dependent Types with Normalization by Evaluation: A Tutorial](http://www.davidchristiansen.dk/tutorials/nbe/)
    [(Haskell Version)](http://davidchristiansen.dk/tutorials/implementing-types-hs.pdf) | David Thrane Christiansen
 2. [FUNCTIONAL PEARLS: Monadic Parsing in Haskell](http://www.cs.nott.ac.uk/~pszgmh/pearl.pdf) | Graham Hutton, Erik Meijer
