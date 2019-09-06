
-- last with recursive precondition:

last'pre :: [a] -> Bool
last'pre xs = not (null xs)

last :: [a] -> a
last [x]      = x
last (_:x:xs) = last (x:xs)

-- Example call:
main1 :: Int
main1 = last (0 : [1..100000])

-- To show:
-- not (null xs) /\ xs=(y:ys) /\ ys=(z:zs)  =>  not (null (z:zs))
