{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- take with recursive precondition:

ctake'pre n xs = n >= 0

ctake 0 xs = []
ctake n (x:xs) | n>0 = x : ctake (n-1) xs

main1 = isList (ctake 100000 [1..])

isList :: [a] -> Bool
isList [] = True
isList (_:xs) = isList xs
