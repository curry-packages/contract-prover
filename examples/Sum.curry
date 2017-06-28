{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- sum with recursive precondition:

sum'pre n = n>=0
sum'post n f = f >= 0

sum n = if n==0 then 0 else n + sum (n-1)

main1 = sum 100
