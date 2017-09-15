{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- non-deterministic number generation (all numbers between 0 and n)

allNats n = if n==0 then 0 else n ? allNats (n-1)

allNats'pre n = n >= 0

main1 = allNats 100000 =:= 0
