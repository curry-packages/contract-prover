-----------------------------------------------------------------------------
--- Definition of some standard names in type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version April 2019
---------------------------------------------------------------------------

module FlatCurry.Typed.Names where

import FlatCurry.Typed.Types

----------------------------------------------------------------------------
--- Is a qualified FlatCurry name primitive?
isPrimOp :: QName -> Bool
isPrimOp (mn,fn) = mn=="Prelude" && fn `elem` map fst preludePrimOps

--- Primitive operations of the prelude and their SMT names.
preludePrimOps :: [(String,String)]
preludePrimOps = unaryPrimOps ++ binaryPrimOps ++
  [("otherwise","true")
  ,("apply","apply") -- TODO...
  ]

--- Primitive unary operations of the prelude and their SMT names.
unaryPrimOps :: [(String,String)]
unaryPrimOps =
  [("_impl#negate#Prelude.Num#Prelude.Int","-")
  ,("not","not")
  ]

--- Primitive binary operations of the prelude and their SMT names.
binaryPrimOps :: [(String,String)]
binaryPrimOps =
  [("&&","and")
  ,("||","or")
  ,("==","=")
  ,("_impl#==#Prelude.Eq#Prelude.Int","=")
  ,("_impl#==#Prelude.Eq#Prelude.Char","=")
  ,("/=","/=")  -- will be translated as negated '='
  ,("_impl#/=#Prelude.Eq#Prelude.Int","/=")
  ,("_impl#/=#Prelude.Eq#Prelude.Char","/=")
  ,("_impl#+#Prelude.Num#Prelude.Int","+")
  ,("_impl#-#Prelude.Num#Prelude.Int","-")
  ,("_impl#*#Prelude.Num#Prelude.Int","*")
  ,("_impl#negate#Prelude.Num#Prelude.Int","-")
  ,("_impl#div#Prelude.Integral#Prelude.Int","div")
  ,("_impl#mod#Prelude.Integral#Prelude.Int","mod")
  ,("_impl#rem#Prelude.Integral#Prelude.Int","rem")
  ,("_impl#>#Prelude.Ord#Prelude.Int",">")
  ,("_impl#<#Prelude.Ord#Prelude.Int","<")
  ,("_impl#>=#Prelude.Ord#Prelude.Int",">=")
  ,("_impl#<=#Prelude.Ord#Prelude.Int","<=")
  ,("_impl#>#Prelude.Ord#Prelude.Float",">")
  ,("_impl#<#Prelude.Ord#Prelude.Float","<")
  ,("_impl#>=#Prelude.Ord#Prelude.Float",">=")
  ,("_impl#<=#Prelude.Ord#Prelude.Float","<=")
  ,("_impl#>#Prelude.Ord#Prelude.Char",">")
  ,("_impl#<#Prelude.Ord#Prelude.Char","<")
  ,("_impl#>=#Prelude.Ord#Prelude.Char",">=")
  ,("_impl#<=#Prelude.Ord#Prelude.Char","<=")
  ]

--- Primitive type constructors from the prelude and their SMT names.
transPrimTCons :: [(String,String)]
transPrimTCons =
  [("Int","Int")
  ,("Float","Real")
  ,("Char","Int")  -- Char is represented as Int
  ,("[]","List")
  ,("()","Unit")
  ,("(,)","Pair")
  ]

--- Some primitive constructors from the prelude and their SMT names.
transPrimCons :: [(String,String)]
transPrimCons =
  [("True","true")
  ,("False","false")
  ,("[]","nil")
  ,(":","insert")
  ,("()","unit")
  ,("(,)","mk-pair")
  ,("LT","LT")
  ,("EQ","EQ")
  ,("GT","GT")
  ,("Nothing","Nothing")
  ,("Just","Just")
  ,("Left","Left")
  ,("Right","Right")
  ] ++
  map (\i -> ('(' : take (i-1) (repeat ',') ++ ")", "Tuple" ++ show i)) [3..15]

----------------------------------------------------------------------------
