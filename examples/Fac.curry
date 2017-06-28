{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- fac with recursive precondition:

fac'pre n = n >= 0
fac'post n f = f > 0

--- Factorial function
fac n = if n==0 then 1 else n * fac (n-1)

main1 = fac 100

main2 = fac (fac 4)

-- Here we cannot eliminate the precondition check:
--main3 x = fac x


