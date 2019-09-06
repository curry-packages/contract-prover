
-- nth with recursive precondition:

nth'pre :: [Int] -> Int -> Bool
nth'pre xs n = n >= 0

nth :: [Int] -> Int -> Int
nth (x:xs) n | n==0 = x
             | n>0  = nth xs (n-1)

main1 :: Int
main1 = nth [1..] 100000
-- PAKCS@belair: 0.58
