-- Simple coin with postcondition:

coin'post :: Int -> Bool
coin'post r = r > 0

coin :: Int
coin = 1 ? 2

