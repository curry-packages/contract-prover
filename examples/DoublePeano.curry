-- Example with postconditions containing user-defined data and operations.
--
-- This is a variation over an example from
--
-- Antoy, S. and Hanus, M. and Libby, S.:
-- Proving Non-Deterministic Computations in Agda
-- Proc. of the 24th International Workshop on Functional and
-- (Constraint) Logic Programming (WFLP 2016),
-- EPTCS Vol. 234, pp. 180-195, DOI: 10.4204/EPTCS.234.13
--
-- where a proof for the postcondition is manually constructed
-- by translating Curry into Agda.

-- Peano numbers:
data Nat = Z | S Nat

-- Non-deterministically returns the argument or the incremented argument.
eo :: Nat -> Nat
eo n = n ? (S n)

-- Is the argument an even number?
even :: Nat -> Bool
even Z         = True
even (S Z)     = False
even (S (S x)) = even x

-- Doubles a number.
double :: Nat -> Nat
double Z     = Z
double (S x) = S (S (double x))

-- Postcondition: the result of `double` is always even.
double'post :: Nat -> Nat -> Bool
double'post _ x = even x

-- Double applied to non-deterministic argument:
double_eo :: Nat -> Nat
double_eo n = double (eo n)

-- With the postcondition for `double`, this postcondition can easily
-- be verified:
double_eo'post :: Nat -> Nat -> Bool
double_eo'post _ x = even x
