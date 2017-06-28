{-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=defaultrules #-}

--- This library defines a very simple structure for Boolean expressions

import Char         ( isAlpha )
import List         ( intercalate, union )

---------------------------------------------------------------------------
--- Datatype for Boolean expressions.
data BoolExp = BVar Int
             | BTerm String [BoolExp]
             | Conj [BoolExp]
             | Disj [BoolExp]
             | Not  BoolExp

-- A Boolean true.
bTrue :: BoolExp
bTrue = BTerm "true" []

-- A Boolean false.
bFalse :: BoolExp
bFalse = BTerm "false" []

-- An equality between two Boolean terms.
bEqu :: BoolExp -> BoolExp -> BoolExp
bEqu b1 b2 = BTerm "=" [b1, b2]

-- An equality between a variable and a Boolean term.
bEquVar :: Int -> BoolExp -> BoolExp
bEquVar v bexp = BTerm "=" [BVar v, bexp]

---------------------------------------------------------------------------
-- All symbols occurring in a Boolean expression.
allSymbolsOfBE :: BoolExp -> [String]
allSymbolsOfBE (BVar _)       = []
allSymbolsOfBE (BTerm s args) = foldr union [s] (map allSymbolsOfBE args)
allSymbolsOfBE (Conj args)    = foldr union [] (map allSymbolsOfBE args)
allSymbolsOfBE (Disj args)    = foldr union [] (map allSymbolsOfBE args)
allSymbolsOfBE (Not arg)      = allSymbolsOfBE arg

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

withBracket :: String -> String
withBracket s = '(' : s ++ ")"
