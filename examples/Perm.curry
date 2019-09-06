-- Example with postconditions for non-deterministic operations.
-- This example is also considered in
--
-- Antoy, S. and Hanus, M. and Libby, S.:
-- Proving Non-Deterministic Computations in Agda
-- Proc. of the 24th International Workshop on Functional and
-- (Constraint) Logic Programming (WFLP 2016),
-- EPTCS Vol. 234, pp. 180-195, DOI: 10.4204/EPTCS.234.13
--
-- where a proof for the postcondition of `perm` is manually constructed
-- by translating Curry into Agda. Depending on the representation
-- of non-deterministic operations in Agda, the proof of the postcondition
-- `perm'post` requires between a few lines and one page of Agda code.
-- With our contract verifier, the postcondition can be verified
-- in a fully automatic manner.

--- Non-deterministic list insertion
ins :: a -> [a] -> [a]
ins x ys     = x : ys
ins x (y:ys) = y : ins x ys

ins'post :: a -> [a] -> [a] -> Bool
ins'post _ xs ys = length xs + 1 == length ys

--- Compute permutation via non-deterministic list insertion
perm :: [a] -> [a]
perm []     = []
perm (x:xs) = ins x (perm xs)

-- The postcondition states that permutations have the same length
-- as the input list.
perm'post :: [a] -> [a] -> Bool
perm'post xs ys = length xs == length ys

