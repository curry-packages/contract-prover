{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- Postcondition for `conc`:
conc'post :: [a] -> [a] -> [a] -> Bool
conc'post xs ys zs = length zs == length xs + length ys

--- Returns the input list with the last element removed.
conc :: [a] -> [a] -> [a]
conc [] ys = ys
conc (x:xs) ys = x : conc xs ys

nrev'post xs ys = length xs == length ys

nrev :: [a] -> [a]
nrev [] = []
nrev (x:xs) = conc (nrev xs) [x]

-- Linear reverse:

rev'post xs ys = length xs == length ys
rev xs = revAcc [] xs

revAcc'post xs ys zs = length xs + length ys == length zs
revAcc xs [] = xs
revAcc xs (y:ys) = revAcc (y:xs) ys

main1 = isList (rev [1..1000])

-- Just check the list structure:
isList :: [a] -> Bool
isList [] = True
isList (_:xs) = isList xs
