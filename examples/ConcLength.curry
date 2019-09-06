
-- Postcondition for `conc`:
conc'post :: [a] -> [a] -> [a] -> Bool
conc'post xs ys zs = length zs == length xs + length ys

--- Returns the input list with the last element removed.
conc :: [a] -> [a] -> [a]
conc []     ys = ys
conc (x:xs) ys = x : conc xs ys

main1 :: Int
main1 = length (conc [1..2000] [1..1000])
