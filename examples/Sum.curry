{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- sum with recursive precondition:

-- Precondition: the argument is not negative
sum'pre n    = n>=0

-- Postcondition: the result satisfies the Gauss sum formula
sum'post n f = f * 2 == n * (n+1)

sum n = if n==0 then 0 else n + sum (n-1)

main1 = sum 100

-- The contract prover can verify all contracts,
-- hence it actually verified the (partial) correctness of sum.
