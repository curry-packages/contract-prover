
-- Precondition: the argument is not negative
mc91'pre :: Int -> Bool
mc91'pre n = n >= 0

-- Postcondition: if n<=100, the result is 91, otherwise it is n-10
mc91'post :: Int -> Int -> Bool
mc91'post n r = (n<=100 && r==91) || (n>100 && r==n-10)

mc91 :: Int -> Int
mc91 n = if n > 100 then n-10
                    else mc91 (mc91 (n+11))

-- The contract prover can verify all contracts (with demand information
-- or options -s), hence it actually verified the (partial) correctness
-- of the McCarthy 91 function.

