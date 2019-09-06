
-- We locally define the operations null and length on integer lists
-- to avoid problems with polymorphism in Z3:
inull :: [Int] -> Bool
inull []    = True
inull (_:_) = False

-- last with recursive precondition:

minimum'pre :: [Int] -> Bool
minimum'pre xs = not (inull xs)

minimum :: [Int] -> Int
minimum [x]          = x
minimum (x:xs@(_:_)) = min x (minimum xs)

-- Example call:
main1 :: Int
main1 = minimum (0 : [1..100000])
