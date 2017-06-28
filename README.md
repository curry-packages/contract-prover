contract-prover
===============

This package contains a tool to optimize contracts in FlatCurry programs
by proving contracts with an SMT solver. If the proof is successful,
the contract check will be eliminated so that the resulting program
will run more efficiently.

The tool is invoked via

    > curry-ctopt <Curry module>

This analyzes the FlatCurry code of the module, attempts to prove
some contracts (and deletes their check in case of success),
and replaces to FlatCurry program by the optimized version.
Hence, this call might be integrated into the compilation chain
of a Curry system.
