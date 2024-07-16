-----------------------------------------------------------------------------
--- Some operations to construct type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version May 2021
---------------------------------------------------------------------------

module FlatCurry.Typed.Build where

import Data.IORef
import Data.List         ( find, nub )
import Data.Maybe        ( fromJust )

-- Imports from dependencies:
import FlatCurry.Annotated.Goodies
import System.CurryPath ( getLoadPathForModule, lookupModuleSource
                        , stripCurrySuffix )
import System.FilePath  ( (</>) )

import FlatCurry.Typed.Goodies ( pre )
--import FlatCurry.Typed.Names
--import FlatCurry.Typed.Simplify
import FlatCurry.Typed.Types

infixr 9 ~>

----------------------------------------------------------------------------
-- Smart constructors for type expressions.

--- A base FlatCurry type.
baseType :: QName -> TypeExpr
baseType t = TCons t []

--- A function type.
(~>) :: TypeExpr -> TypeExpr -> TypeExpr
t1 ~> t2 = FuncType t1 t2

--- Type `()` as a FlatCurry type.
unitType :: TypeExpr
unitType = baseType (pre "()")

--- Type `Char` as a FlatCurry type.
charType :: TypeExpr
charType = baseType (pre "Char")

--- Type `Bool` as a FlatCurry type.
boolType :: TypeExpr
boolType = baseType (pre "Bool")

--- Constructs a list type from an element type.
listType :: TypeExpr -> TypeExpr
listType a = TCons (pre "[]") [a]

--- Type `String` as a FlatCurry type.
stringType :: TypeExpr
stringType = listType charType

--- Constructs a tuple type from list of component types.
tupleType :: [TypeExpr] -> TypeExpr
tupleType ts
 | n==0 = baseType (pre "()")
 | n==1 = head ts
 | otherwise = TCons (tupleCons n) ts
 where n = length ts

--- Generates an `n`-ary tuple constructor (only meaningful for `n>1`).
tupleCons :: Int -> QName
tupleCons n = pre ('(' : take (n-1) (repeat ',') ++ ")")

----------------------------------------------------------------------------
-- Smart constructors for expressions.

--- Constructs a tuple expression.
tupleExpr :: [TAExpr] -> TAExpr
tupleExpr xs = case length xs of
    0 -> AComb unitType ConsCall (pre "()", unitType) []
    1 -> head xs
    n -> let tys = map annExpr xs
             tt  = tupleType tys
             ft  = foldr FuncType tt tys
         in AComb tt ConsCall (tupleCons n, ft) xs

-- Transforms a string into type-annotated FlatCurry representation.
string2TAFCY :: String -> TAExpr
string2TAFCY [] = AComb stringType ConsCall (pre "[]",stringType) []
string2TAFCY (c:cs) =
  AComb stringType ConsCall
        (pre ":", FuncType charType (FuncType stringType stringType))
        [ALit charType (Charc c), string2TAFCY cs]

----------------------------------------------------------------------------
