{-# OPTIONS_CYMAKE -Wno-overlapping #-}

-- Contract verification requires option "-s"

ins'post :: a -> [a] -> [a] -> Bool
ins'post _ xs ys = length xs + 1 == length ys

--- Non-deterministic list insertion
ins :: a -> [a] -> [a]
ins x ys     = x : ys
ins x (y:ys) = y : ins x ys

