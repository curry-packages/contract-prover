--- This example demonstrates that our tool verifies
--- the *partial* correctness of postconditions.
--- For a non-terminating function, any postcondition can be verified.
--- Nevertheless, this is fine since our tool omits the
--- postcondition check which will never be reached.

loop :: Int
loop = loop

-- Arbitrary postcondition:
loop'post :: Int -> Bool
loop'post z = z<0
