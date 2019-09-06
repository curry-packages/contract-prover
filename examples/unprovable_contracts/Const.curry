
-- This is an example where the consideration of the evaluation strategy
-- is important to check the contracts.

const :: a -> b -> b
const x y = y

f :: Int -> Int
f x | x>0 = 0

f'post :: Int -> Int -> Bool
f'post x z = x>0

-- The postcondition holds in a strict language (where (f x) is evaluated)
-- but it does not hold in a non-strict language like Curry:
g :: Int -> Int
g x = const (f x) 42

g'post :: Int -> Int -> Bool
g'post x z = x>0
