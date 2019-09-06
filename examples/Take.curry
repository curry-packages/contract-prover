
-- take with recursive precondition:

ctake'pre :: Int -> [a] -> Bool
ctake'pre n _ = n >= 0

ctake :: Int -> [a] -> [a]
ctake 0 _      = []
ctake n (x:xs) | n>0 = x : ctake (n-1) xs

main1 :: Bool
main1 = isList (ctake 100000 [1..])

-- Just check the list structure:
isList :: [a] -> Bool
isList []     = True
isList (_:xs) = isList xs

