
-- This program contains an example of a non-deterministic contract.
-- Such a contract must be satisfied for each non-deterministic choice.

-- The proof of non-deterministic contracts require the translation
-- of non-deterministic operations into SMT. Therefore, we introduce
-- this choice operation (it is identical to `Prelude.?`).
choice :: a -> a -> a
choice x _ = x
choice _ y = y

-- A non-deterministic precondition is satisfied if each non-deterministic
-- choice is satisfied. Hence, this precondition expresses the requirement
-- that the argument must be positive and less than 100.
f'pre :: Int -> Bool
f'pre x = choice (x>0) (x<100)

f :: Int -> Int
f x = x

-- The argument satisfies both choices for the precondition.
-- Hence, dynamic contract checking can be eliminated.
h :: Int
h = f 1
