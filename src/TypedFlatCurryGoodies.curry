-----------------------------------------------------------------------------
--- Some goodies to deal with type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version September 2017
---------------------------------------------------------------------------

module TypedFlatCurryGoodies where

import Data.List       ( find, nub )
import Data.Maybe      ( fromJust )
import System.Process  ( exitWith )

-- Imports from dependencies:
import FlatCurry.Files
import FlatCurry.Typed.Files (readTypedFlatCurryAsAnnotated)
import FlatCurry.Annotated.Goodies
import FlatCurry.Annotated.Types
import FlatCurry.Annotated.TypeInference ( inferProg )

-- Type synomyms for type-annotated FlatCurry entities:
type TAProg       = AProg       TypeExpr
type TAFuncDecl   = AFuncDecl   TypeExpr
type TARule       = ARule       TypeExpr
type TAExpr       = AExpr       TypeExpr
type TABranchExpr = ABranchExpr TypeExpr
type TAPattern    = APattern    TypeExpr

--- Extract all user-defined typed FlatCurry functions that might be called
--- by a given list of functions.
getAllFunctions :: [TAFuncDecl] -> [TAProg] -> [QName]
                -> IO [TAFuncDecl]
getAllFunctions currfuncs _ [] = return (reverse currfuncs)
getAllFunctions currfuncs currmods (newfun:newfuncs)
  | newfun `elem` standardConstructors ++ map funcName currfuncs
    || isPrimOp newfun
  = getAllFunctions currfuncs currmods newfuncs
  | fst newfun `elem` map progName currmods
  = maybe
      (-- if we don't find the qname, it must be a constructor:
       getAllFunctions currfuncs currmods newfuncs)
      (\fdecl -> getAllFunctions
                    (fdecl : currfuncs)
                    currmods (newfuncs ++ nub (funcsOfFuncDecl fdecl)))
      (find (\fd -> funcName fd == newfun)
            (progFuncs
               (fromJust (find (\m -> progName m == fst newfun) currmods))))
  | otherwise -- we must load a new module
  = do let mname = fst newfun
       putStrLn $ "Loading module '" ++ mname ++ "'..."
       newmod <- readTypedFlatCurryAsAnnotated mname
       getAllFunctions currfuncs (newmod:currmods) (newfun:newfuncs)

--- Returns the names of all functions/constructors occurring in the
--- body of a function declaration.
funcsOfFuncDecl :: TAFuncDecl -> [QName]
funcsOfFuncDecl fd =
  nub (trRule (\_ _ e -> funcsOfExp e) (\_ _ -> []) (funcRule fd))
 where
  funcsOfExp = trExpr (\_ _ -> [])
                      (\_ _ -> [])
                      (\_ _ (qn,_) fs -> qn : concat fs)
                      (\_ bs fs -> concatMap snd bs ++ fs)
                      (\_ _ -> id)
                      (\_ -> (++))
                      (\_ _ fs fss -> concat (fs:fss))
                      (\_ -> id)
                      (\_ fs _ -> fs)

--- Returns `True` if the expression is non-deterministic,
--- i.e., if `Or` or `Free` occurs in the expression.
ndExpr :: TAExpr -> Bool
ndExpr = trExpr (\_ _ -> False)
                (\_ _ -> False)
                (\_ _ _ nds -> or nds)
                (\_ bs nd -> nd || any snd bs)
                (\_ _ _ -> True)
                (\_ _ _ -> True)
                (\_ _ nd bs -> nd || or bs)
                (\_ -> id)
                (\_ nd _ -> nd)

----------------------------------------------------------------------------
--- Is a qualified FlatCurry name primitive?
isPrimOp :: QName -> Bool
isPrimOp (mn,fn) = mn=="Prelude" && fn `elem` map fst preludePrimOps

--- Primitive operations of the prelude and their SMT names.
preludePrimOps :: [(String,String)]
preludePrimOps =
  [("==","=")
  ,("+","+")
  ,("-","-")
  ,("negate","-")
  ,("*","*")
  ,("div","div")
  ,("mod","mod")
  ,("rem","rem")
  ,(">",">")
  ,(">=",">=")
  ,("<","<")
  ,("<=","<=")
  ,("not","not")
  ,("&&","and")
  ,("||","or")
  ,("apply","") -- SMT name not used
  ]

--- Primitive constructors and their SMT names.
primCons :: [(String,String)]
primCons =
  [("True","true")
  ,("False","false")
  ,("[]","nil")
  ,(":","insert")
  ]

-- Some standard constructors from the prelude.
standardConstructors :: [QName]
standardConstructors = [pre "[]", pre ":", pre "()"]

----------------------------------------------------------------------------

pre :: String -> QName
pre f = ("Prelude",f)

showQName :: QName -> String
showQName (mn,fn) = mn ++ "." ++ fn

----------------------------------------------------------------------------
