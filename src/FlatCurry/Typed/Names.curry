-----------------------------------------------------------------------------
--- Definition of some standard names in type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version September 2024
---------------------------------------------------------------------------

module FlatCurry.Typed.Names
  ( isPrimOp, preludePrimOps, unaryPrimOps, binaryPrimOps
  , transPrimTCons, transPrimCons )
where

import FlatCurry.Names2SMT   ( unaryPrimOps, binaryPrimOps )
import FlatCurry.Typed.Types

----------------------------------------------------------------------------
--- Is a qualified FlatCurry name primitive?
isPrimOp :: QName -> Bool
isPrimOp (mn,fn) = mn=="Prelude" && fn `elem` map fst preludePrimOps

--- Primitive operations of the prelude and their SMT names.
preludePrimOps :: [(String,String)]
preludePrimOps = unaryPrimOps ++ binaryPrimOps ++
  [("otherwise","true")
  ,("if_then_else","ite")
  ,("choose","choose")
  ,("lchoice","lchoice")
  ,("rchoice","rchoice")
  ,("apply","apply") -- TODO...
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
  ,("Maybe","Maybe")
  ,("Either","Either")
  ,("Ordering","Ordering")
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
