-- The definition of the function `split` from library `List`.
split :: (a -> Bool) -> [a] -> [[a]]
split _ []     = [[]]
split p (x:xs) | p x       = [] : split p xs
               | otherwise = let sp = split p xs
                             in (x : head sp) : tail sp

-- This postcondition is useful to verify that the calls to head and split
-- are non-failing (compare package `failfree`).
split'post :: (a -> Bool) -> [a] -> [[a]] -> Bool
split'post p xs ys = not (null ys)
