
-- Without precondition verification, the precondition of `fib`
-- must be checked in each recursive call:

fib'pre :: Int -> Bool
fib'pre n = n >= 0

fib'post :: Int -> Int -> Bool
fib'post _ f = f >= 0

fib :: Int -> Int
fib x | x == 0    = 0
      | x == 1    = 1
      | otherwise = fib (x-1) + fib (x-2)


main1 :: Int
main1 = fib 25

main2 :: Int
main2 = fib (fib 5)


