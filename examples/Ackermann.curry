{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

ack'pre m n = m>=0 && n>=0
ack'post m n r = r >= m+n+1

ack :: Int -> Int -> Int
ack m n | m==0 = n+1
        | m>0 && n==0 = ack (m-1) 1
        | m>0 && n>0  = ack (m-1) (ack m (n-1))

-- All contracts are verified (with optione -s)
