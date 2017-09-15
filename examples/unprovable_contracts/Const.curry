{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- This is an example where the consideration of the evaluation strategy
-- is important to check the contracts.

const x y = y

f'post x z = x>0
f x | x>0 = 0

-- The postcondition holds in a strict language (where (f x) is evaluated)
-- but it does not hold in a non-strict language like Curry:
g'post x z = x>0
g x = const (f x) 42
