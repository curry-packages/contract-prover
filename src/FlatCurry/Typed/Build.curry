-----------------------------------------------------------------------------
--- Some operations to construct type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version April 2019
---------------------------------------------------------------------------

module FlatCurry.Typed.Build where

import FilePath     ( (</>) )
import IOExts
import List         ( find, nub )
import Maybe        ( fromJust )

-- Imports from dependencies:
import FlatCurry.Annotated.Files   ( readTypedFlatCurry )
import FlatCurry.Annotated.Goodies
import System.CurryPath ( getLoadPathForModule, lookupModuleSource
                        , stripCurrySuffix )

import FlatCurry.Typed.Goodies ( pre )
--import FlatCurry.Typed.Names
--import FlatCurry.Typed.Simplify
import FlatCurry.Typed.Types

----------------------------------------------------------------------------
-- Smart constructors for type expressions.

--- A base FlatCurry type.
baseType :: QName -> TypeExpr
baseType t = TCons t []

-- Type `()` as a FlatCurry type.
unitType :: TypeExpr
unitType = baseType (pre "()")

-- Type `Char` as a FlatCurry type.
charType :: TypeExpr
charType = baseType (pre "Char")

-- Type `Bool` as a FlatCurry type.
boolType :: TypeExpr
boolType = baseType (pre "Bool")

--- Constructs a list type from an element type.
listType :: TypeExpr -> TypeExpr
listType a = TCons (pre "[]") [a]

-- Type `String` as a FlatCurry type.
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

-- Transforms a string into typed FlatCurry representation.
string2TFCY :: String -> TAExpr
string2TFCY [] = AComb stringType ConsCall (pre "[]",stringType) []
string2TFCY (c:cs) =
  AComb stringType ConsCall
        (pre ":", FuncType charType (FuncType stringType stringType))
        [ALit charType (Charc c), string2TFCY cs]

----------------------------------------------------------------------------