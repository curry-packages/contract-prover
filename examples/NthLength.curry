{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- nth with recursive precondition:

nth'pre xs n = n >= 0 && length (take (n+1) xs) == n+1

nth (x:xs) n | n==0 = x
             | n>0  = nth xs (n-1)

--main1 = nth [1..] 1000
