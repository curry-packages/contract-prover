{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- Simple coin with postcondition:

coin'post r = r > 0

coin = 1 ? 2

