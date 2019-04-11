
-- Precondition: both arguments are non-negative
ack'pre :: Int -> Int -> Bool
ack'pre m n = m>=0 && n>=0

-- Postcondition: the result is greater than the sum of its arguments
ack'post :: Int -> Int -> Int -> Bool
ack'post m n r = r > m+n

-- The definition of the Ackermann function. Note that we can
-- simplify the condition due to the precondition, i.e., we don't have
-- to check that m>0 in the second and third guard:
ack :: Int -> Int -> Int
ack m n | m==0 = n+1
        | n==0 = ack (m-1) 1
        | n>0  = ack (m-1) (ack m (n-1))

-- All contracts are verified (with optione -s)
