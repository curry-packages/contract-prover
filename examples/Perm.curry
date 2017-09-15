{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}


ins'post :: a -> [a] -> [a] -> Bool
ins'post _ xs ys = length xs + 1 == length ys

--- Non-deterministic list insertion
ins :: a -> [a] -> [a]
ins x ys     = x : ys
ins x (y:ys) = y : ins x ys


perm'post :: [a] -> [a] -> Bool
perm'post xs ys = length xs == length ys

--- Compute permutation via Non-deterministic list insertion
perm :: [a] -> [a]
perm []   = []
perm (x:xs) = ins x (perm xs)
