
-- Contract for operation `init`:
init'pre :: [a] -> Bool
init'pre xs = not (null xs)

init'post :: [a] -> [a] -> Bool
init'post xs ys = length ys + 1 == length xs

--- Returns the input list with the last element removed.
init :: [a] -> [a]
init [_]          = []
init (x:xs@(_:_)) = x : init xs

-- Example call:
main1 :: Int
main1 = length (init (0 : [1..2000]))
