contract-prover
===============

Overview
--------

This package contains a tool to verify and add contracts in FlatCurry programs
by proving contracts with an SMT solver. If a proof is successful,
no contract check will be performed at run time, otherwise
a dynamic (strict) contract check will be added.
The static verification of contracts has the advantage that
the resulting program will run more efficiently compared
to a program with dynamic contract checking only.

A detailed description of the ideas of this tool can be found in
the journal paper:

> M. Hanus: Combining Static and Dynamic Contract Checking for Curry,
> Fundamenta Informaticae 173(4), pp. 285-314, 2020,
> DOI [10.3233/FI-2020-1925](http://dx.doi.org/10.3233/FI-2020-1925)

The tool is invoked via

    > curry-contracts <Curry module>

This analyzes the FlatCurry code of the module, attempts to prove
the contracts in this module (unless option `--add` is set),
and adds dynamic contract checking if a proof is not successful.
Finally, the FlatCurry program is replaced by the transformed version
(unless option `--target=NONE` is set).
Hence, this tool might be integrated into the compilation chain
of a Curry system.
In addition to the transformation of the FlatCurry program,
successful proofs will be stored in files so that they can
be re-used by other tools. For instance, if the postcondition
of an operation `f` defined in module `M` is verified,
a file `PROOF_M_f_SatisfiesPostCondition.smt` is generated.
This file contains the SMT script of this proof.

The directory `examples` contains various examples where the
contract prover can eliminate all contracts at compile time.

Dynamic contracts
-----------------

As mentioned above, the tool adds checks for contracts at run time
if it cannot be verified that these contracts always hold.
This is done by transforming the FlatCurry code of the modules
by inserting Curry code which checks the contracts when the
correspondings operations are invoked at run time.
When a contract is not satisfied,
this checking code terminates the program with an error message
about the violated contract. The error message also shows
the arguments (and result in case of a violated postcondition)
of the operation, if this is possible with the operation `Prelude.show`
(i.e., if the types are not polymorphic and not functional).
Thus, for user-defined types occurring in contracts,
it is assumed that instances of class `Show` exist for these types.


------------------------------------------------------------------------------

Web Demo Installation
---------------------

If you want to try the contract prover on simple programs via a web interface,
you can use a
[Web Demo Installation](https://cpm.curry-lang.org/webapps/contracts/)
of the prover.

------------------------------------------------------------------------------

Implementation
--------------

In contrast to the first contract prover described in
[LOPSTR 2017 paper](https://dx.doi.org/10.1007/978-3-319-94460-9_19),
which tried to remove contracts added by the Curry preprocessor,
this version tries to verify contracts before they are added
to the Curry program and adds dynamic checks only for unverified contracts
(see the auxiliary operations defined in `include/ContractChecker.curry`).

The strategy is as follows:

1. For each postcondition `f'post`, try to verify it.
   If this is not successful, a dynamic check is added to `f`.

2. For each function call `(f args)`, where a preconditon `f'pre` exists,
   try to verify this precondition in the given context of the call.
   If it cannot be verified, transform the function call into

       checkPreCond (f args) (f'pre args) "f" (args)

   See `include/ContractChecker.curry` for the definition of `checkPreCond`.

---------------------------------------------------------------------------

Notes:
------

- Contracts can also be stored in separate files.
  When checking a module `m`, if there is a Curry module `m_SPEC`
  in the load path for module `m` or in the package directory `include`,
  the contents of `m_SPEC` is added to `m` before it is checked.

- Contracts for operators can also be specified by
  operations named by `op_xh1...hn'`, where each
  `hi` is a two digit hexadecimal number and the name
  of the operator corresponds to the ord values of `h1...hn`.
  For instance, a precondition for the operator `!!` can be named
  `op_x2121'pre`. To generate such names automatically,
  one can use the option `--name` of the tool.

---------------------------------------------------------------------------

Directories of the package:
---------------------------

* examples: some examples (and test suite)

* include: an include file for the SMT solver and a small Curry program
  containing operations which perform dynamic contract checking
  for unverified contracts

* src: source code of the implementation

---------------------------------------------------------------------------
