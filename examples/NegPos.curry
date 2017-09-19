{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- A simple example from the introduction of
-- [Ngueyen/Tobin-Hochstaedt/Van Horn, ICFP'14]

-- Contract: pos -> neg
f'pre n = n > 0
f'post n f = f < 0

--- A simple function that negates its input:
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
g'pre = pos
g'post _ = neg

--- A simple function that negates its input:
g n = n * (-1)

