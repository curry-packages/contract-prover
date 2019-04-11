
-- A simple example from the introduction of
-- [Ngueyen/Tobin-Hochstaedt/Van Horn, ICFP'14]

-- Contract: pos -> neg
f'pre :: Int -> Bool
f'pre n = n > 0

f'post :: Int -> Int -> Bool
f'post _ r = r < 0

--- A simple function that negates its input:
f :: Int -> Int
f n = n * (-1)

---------------------------------------------------------------------------
-- The same example with pos/neg predicates and higher-order equations
-- for contracts:

--- Is the argument positive?
pos :: Int -> Bool
pos n = n > 0

--- Is the argument negative?
neg :: Int -> Bool
neg n = n < 0

-- Contract: pos -> neg (defined by higher-order equations)
g'pre :: Int -> Bool
g'pre = pos

g'post :: Int -> Int -> Bool
g'post _ = neg

--- A simple function that negates its input:
g :: Int -> Int
g n = n * (-1)

