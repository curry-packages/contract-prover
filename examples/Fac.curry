
-- Without precondition verification, the precondition of fac
-- must be checked in each recursive call.

fac'pre :: Int -> Bool
fac'pre n = n >= 0

fac'post :: Int -> Int -> Bool
fac'post n f = f > 0

--- Factorial function
fac :: Int -> Int
fac n = if n==0 then 1 else n * fac (n-1)

main1 = fac 100

main2 = fac (fac 4)

-- Here we cannot eliminate the precondition check:
--main3 x = fac x


-- Although difference not measurable, it is important to verify
-- as many precondition as possible, since this provide more reliable
-- software which does not crash at run-time
