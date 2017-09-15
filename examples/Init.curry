{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- Contract for operation `init`:
init'pre :: [a] -> Bool
init'pre xs = not (null xs)

init'post :: [a] -> [a] -> Bool
init'post xs ys = length ys + 1 == length xs

--- Returns the input list with the last element removed.
init :: [a] -> [a]
init [_]          = []
init (x:xs@(_:_)) = x : init xs

--main1 = length (init [1..2000])

