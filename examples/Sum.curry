
-- sum with recursive precondition:

-- Precondition: the argument is not negative
sum'pre :: Int -> Bool
sum'pre n = n>=0

-- Postcondition: the result satisfies the Gauss sum formula
sum'post :: Int -> Int -> Bool
sum'post n f = f == n * (n+1) `div` 2

sum :: Int -> Int
sum n = if n==0 then 0 else n + sum (n-1)

main1 :: Int
main1 = sum 100

-- The contract prover can verify all contracts.
-- Hence, it actually verified the (partial) correctness of sum.
