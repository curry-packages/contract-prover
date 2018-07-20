{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=defaultrules #-}

--- This library defines a very simple structure for Boolean expressions

import Data.Char         ( isAlpha )
import Data.List         ( intercalate, union )

---------------------------------------------------------------------------
--- Datatype for Boolean expressions.
data BoolExp = BVar Int
             | BTerm String [BoolExp]
             | Conj [BoolExp]
             | Disj [BoolExp]
             | Not  BoolExp
             | Binding String [(Int,BoolExp)] BoolExp

--- A Boolean true.
bTrue :: BoolExp
bTrue = BTerm "true" []

--- A Boolean false.
bFalse :: BoolExp
bFalse = BTerm "false" []

--- An equality between two Boolean terms.
bEqu :: BoolExp -> BoolExp -> BoolExp
bEqu b1 b2 = BTerm "=" [b1, b2]

--- An equality between a variable and a Boolean term.
bEquVar :: Int -> BoolExp -> BoolExp
bEquVar v bexp = BTerm "=" [BVar v, bexp]

--- A binding for a list of binding variables.
bindingBE :: String -> [(Int,BoolExp)] -> BoolExp -> BoolExp
bindingBE bkind bs exp | null bs   = exp
                     | otherwise = Binding bkind bs exp

--- A "let" binding.
letBinding :: [(Int,BoolExp)] -> BoolExp -> BoolExp
letBinding = bindingBE "let"

--- A "forall" binding.
forallBinding :: [(Int,BoolExp)] -> BoolExp -> BoolExp
forallBinding = bindingBE "forall"

--- An "exists" binding.
existsBinding :: [(Int,BoolExp)] -> BoolExp -> BoolExp
existsBinding = bindingBE "exists"

--- An assertion of a Boolean expression.
assertSMT :: BoolExp -> BoolExp
assertSMT be = BTerm "assert" [be]

---------------------------------------------------------------------------
-- All symbols occurring in a Boolean expression.
allSymbolsOfBE :: BoolExp -> [String]
allSymbolsOfBE (BVar _)         = []
allSymbolsOfBE (BTerm s args)   = foldr union [s] (map allSymbolsOfBE args)
allSymbolsOfBE (Conj args)      = foldr union [] (map allSymbolsOfBE args)
allSymbolsOfBE (Disj args)      = foldr union [] (map allSymbolsOfBE args)
allSymbolsOfBE (Not arg)        = allSymbolsOfBE arg
allSymbolsOfBE (Binding _ bs e) =
  foldr union [] (map allSymbolsOfBE (e : map snd bs))

---------------------------------------------------------------------------
-- Simplify Boolean expression for better readability.
simpBE :: BoolExp ->DET BoolExp
simpBE (Conj (bs1 ++ [BTerm "true" []] ++ bs2)) = simpBE (Conj (bs1 ++ bs2))
simpBE (Conj (_ ++ [BTerm "false" []] ++ _)) = bFalse
simpBE (Conj (bs1 ++ [Conj bs2] ++ bs3)) = simpBE (Conj (bs1 ++ bs2 ++ bs3))
simpBE (Conj bs) = Conj (map simpBE bs)
simpBE (Disj (bs1 ++ [BTerm "false" []] ++ bs2)) = simpBE (Disj (bs1 ++ bs2))
simpBE (Disj (_ ++ [BTerm "true" []] ++ _)) = bTrue
simpBE (Disj (bs1 ++ [Disj bs2] ++ bs3)) = simpBE (Disj (bs1 ++ bs2 ++ bs3))
simpBE (Disj bs) = Disj (map simpBE bs)
simpBE (Not (Not b)) = b
simpBE (Binding _ [] e) = e
simpBE (BTerm s args) = BTerm s (map simpBE args)
simpBE'default be = be

---------------------------------------------------------------------------
-- Shows a simplified Boolean expression.
showBoolExp :: BoolExp -> String
showBoolExp = smtBE --prettyBE
              . simpBE

-- Prints a Boolean expression in SMT-like notation:
smtBE :: BoolExp -> String
smtBE (BVar i) = 'x' : show i
smtBE (BTerm f args)
  | f == "="  = asLisp ["=", smtBE (head args), smtBE (args!!1)]
  | f == "let" = asLisp ["let", asLisp (map (\ (BTerm _ [v,e]) -> asLisp [smtBE v, smtBE e]) (tail args)), smtBE (head args)]
  | otherwise = if null args then f
                             else asLisp $ f : map smtBE args
smtBE (Conj bs) = case bs of
  []  -> "true"
  [b] -> smtBE b
  _   -> asLisp $ "and" : map smtBE bs
smtBE (Disj bs) = case bs of
  []  -> "false"
  [b] -> smtBE b
  _   -> asLisp $ "or" : map smtBE bs
smtBE (Not b) = asLisp ["not", smtBE b]
smtBE (Binding s bs e) =
  asLisp [s,
          asLisp (map (\ (v,b) -> asLisp [smtBE (BVar v), smtBE b]) bs),
          smtBE e]

asLisp :: [String] -> String
asLisp = withBracket . unwords

-- "Pretty" prints a Boolean expression
prettyBE :: BoolExp -> String
prettyBE (BVar i) = 'x' : show i
prettyBE (BTerm f args)
  | f == "="  = prettyBE (head args) ++ " = " ++ prettyBE (args!!1)
  | null args = f
  | not (isAlpha (head f)) && length args == 2
  = prettyBE (args!!0) ++ f ++ prettyBE (args!!1)
  | otherwise = f ++ withBracket (intercalate "," (map prettyBE args))
prettyBE (Conj bs) = case bs of
  []  -> "true"
  [b] -> prettyBE b
  _   -> withBracket (intercalate " && " (map prettyBE bs))
prettyBE (Disj bs) = case bs of
  []  -> "false"
  [b] -> prettyBE b
  _   -> withBracket (intercalate " || " (map prettyBE bs))
prettyBE (Not b) = withBracket ("not " ++ prettyBE b)
prettyBE (Binding s bs e) = withBracket $ unwords $
  [s,
   "{", intercalate ";"
          (map (\ (v,b) -> unwords [prettyBE (BVar v), "=", prettyBE b]) bs),
   "}",
   prettyBE e]

withBracket :: String -> String
withBracket s = '(' : s ++ ")"
