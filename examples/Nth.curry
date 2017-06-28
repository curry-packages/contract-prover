{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- nth with recursive precondition:

nth'pre xs n = n >= 0

nth (x:xs) n | n==0 = x
             | n>0  = nth xs (n-1)

main1 = nth [1..] 100000
-- PAKCS@belair: 0.58
