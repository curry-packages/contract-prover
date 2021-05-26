-- Auxiliary operations for contract checking.
-- If the contract tool adds some unverified contracts to a program,
-- the definition of these operations are also added.

--- Auxiliary operation to check the validity of a precondition for
--- some function call.
--- For this purpose, a function call
---
---     (f x1 ... xn)
---
--- is transformed into the new call
---
---     checkPreCond (f x1 ... xn) (f'pre x1 ... xn) "f" (x1,...,xn)
---
checkPreCond :: Show b => a -> Bool -> String -> b -> a
checkPreCond x pc fn args =
  if pc
    then x
    else error $ "Precondition of operation '" ++ fn ++
                 "' not satisfied for arguments:\n" ++ show args


--- Auxiliary operation to check the validity of a given postcondition.
--- For this purpose, each rule
---
---     f x1 ... xn = rhs
---
--- is transformed into the new rule
---
---     f x1 ... xn = checkPostCond rhs (f'post x1 ... xn) "f" (x1,...,xn)
---
checkPostCond :: (Show a, Show b) => a -> (a -> Bool) -> String -> b -> a
checkPostCond rhs fpost fname args =
  if fpost rhs
    then rhs
    else error $ "Postcondition of operation '" ++ fname ++
                 "' failed for arguments/result:\n" ++
                 show args ++ " -> " ++ show rhs
