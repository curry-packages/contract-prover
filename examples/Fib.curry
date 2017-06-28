{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- fac with recursive precondition:

fib'pre n = n>=0
fib'post n f = f>=0

fib x | x == 0 = 0
      | x == 1 = 1
      | otherwise = fib (x-1) + fib (x-2)


main = fib 25

main2 = fib (fib 5)


