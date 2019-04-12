-----------------------------------------------------------------------------
--- Some goodies to deal with type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version April 2019
---------------------------------------------------------------------------

module TypedFlatCurryGoodies where

import Directory    ( doesFileExist )
import FilePath     ( (</>) )
import IOExts
import List         ( find, nub, union )
import Maybe        ( fromJust )
import System       ( exitWith )

-- Imports from dependencies:
import Data.FiniteMap
import FlatCurry.Annotated.Files   ( readTypedFlatCurry )
import FlatCurry.Annotated.Goodies
import FlatCurry.Annotated.Types
import FlatCurry.Annotated.TypeSubst
import System.CurryPath ( getLoadPathForModule, lookupModuleSource
                        , stripCurrySuffix )

import PackageConfig ( packagePath )
import ProverOptions
import VerifierState


-- Type synomyms for type-annotated FlatCurry entities:
type TAProg       = AProg       TypeExpr
type TAFuncDecl   = AFuncDecl   TypeExpr
type TARule       = ARule       TypeExpr
type TAExpr       = AExpr       TypeExpr
type TABranchExpr = ABranchExpr TypeExpr
type TAPattern    = APattern    TypeExpr

----------------------------------------------------------------------------
--- Reads a typed FlatCurry program together with a possible `_SPEC` program
--- (containing further contracts) or exits with a failure message
--- in case of some typing error.
readTypedFlatCurryWithSpec :: Options -> String -> IO TAProg
readTypedFlatCurryWithSpec opts mname = do
  printWhenStatus opts $ "Loading typed FlatCurry program '" ++ mname ++ "'"
  prog     <- readTypedFlatCurry mname
  loadpath <- getLoadPathForModule specName
  mbspec   <- lookupModuleSource (loadpath ++ [packagePath </> "include"])
                                 specName
  maybe (return prog)
        (\ (_,specname) -> do
           let specpath = stripCurrySuffix specname
           printWhenStatus opts $ 
             "'" ++ (if optVerb opts > 1 then specpath else specName) ++ "'..."
           specprog <- readTypedFlatCurry specpath
           return (unionTAProg prog (rnmProg mname specprog))
        )
        mbspec
 where
  specName = mname ++ "_SPEC"

--- Returns the union of two typed FlatCurry programs.
unionTAProg :: TAProg -> TAProg -> TAProg
unionTAProg (AProg name imps1 types1 funcs1 ops1)
            (AProg _    imps2 types2 funcs2 ops2) =
  AProg name (filter (/=name) (union imps1 imps2))
        (types1++types2) (funcs1++funcs2) (ops1++ops2)

----------------------------------------------------------------------------
--- Extract all user-defined typed FlatCurry functions that might be called
--- by a given list of functions.
getAllFunctions :: IORef VState -> [TAFuncDecl] -> [QName] -> IO [TAFuncDecl]
getAllFunctions vstref currfuncs newfuns = do
  currmods <- readIORef vstref >>= return . currTAProgs
  getAllFuncs currmods newfuns
 where
  getAllFuncs _ [] = return (reverse currfuncs)
  getAllFuncs currmods (newfun:newfuncs)
    | newfun `elem` standardConstructors ++ map funcName currfuncs
      || isPrimOp newfun
    = getAllFunctions vstref currfuncs newfuncs
    | fst newfun `elem` map progName currmods
    = maybe
        (-- if we don't find the qname, it must be a constructor:
         getAllFunctions vstref currfuncs newfuncs)
        (\fdecl -> getAllFunctions vstref
                      (fdecl : currfuncs)
                      (newfuncs ++ nub (funcsOfFuncDecl fdecl)))
        (find (\fd -> funcName fd == newfun)
              (progFuncs
                 (fromJust (find (\m -> progName m == fst newfun) currmods))))
    | otherwise -- we must load a new module
    = do let mname = fst newfun
         opts <- readTransInfoRef vstref >>= return . tiOptions
         printWhenStatus opts $
           "Loading module '" ++ mname ++ "' for '"++ snd newfun ++"'"
         newmod <- readTypedFlatCurry mname
         modifyIORef vstref (addProgToState newmod)
         getAllFunctions vstref currfuncs (newfun:newfuncs)

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
  ,("_impl#==#Prelude.Eq#Prelude.Int","=")
  ,("/=","/=")  -- will be translated as negated '='
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
  ,("not","not")
  ,("&&","and")
  ,("||","or")
  ,("otherwise","true")
  ,("apply","apply") -- SMT name not used
  ]

--- Primitive constructors from the prelude and their SMT names.
primCons :: [(String,String)]
primCons =
  [("True","true")
  ,("False","false")
  ,("[]","nil")
  ,(":","insert")
  ,("(,)","mk-pair")
  ,("LT","LT")
  ,("EQ","EQ")
  ,("GT","GT")
  ,("Nothing","Nothing")
  ,("Just","Just")
  ,("Left","Left")
  ,("Right","Right")
  ]

-- Some standard constructors from the prelude.
standardConstructors :: [QName]
standardConstructors =
  map (pre . fst) primCons ++ [pre "()", pre "(,)", pre "(,,)"]

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
--- Is the type expression a base type?
isBaseType :: TypeExpr -> Bool
isBaseType (TVar _)         = False
isBaseType (TCons _ targs)  = null targs
isBaseType (FuncType _ _)   = False
isBaseType (ForallType _ _) = False

----------------------------------------------------------------------------
--- Compute type matching, i.e., if `matchType t1 t2 = s`, then `t2 = s(t1)`.
matchType :: TypeExpr -> TypeExpr -> Maybe AFCSubst
matchType t1 t2 = case (t1,t2) of
  (TVar v        , _) -> Just $ if t1 == t2 then emptyAFCSubst
                                            else addToFM emptyAFCSubst v t2
  (TCons tc1 ts1 , TCons tc2 ts2) | tc1 == tc2 -> matchTypes ts1 ts2
  (FuncType a1 r1, FuncType a2 r2) -> matchTypes [a1,r1] [a2,r2]
  (ForallType _ _, _) -> error "matchType: ForallType occurred"
  (_, ForallType _ _) -> error "matchType: ForallType occurred"
  _ -> Nothing

matchTypes :: [TypeExpr] -> [TypeExpr] -> Maybe AFCSubst
matchTypes []       []       = Just emptyAFCSubst
matchTypes []       (_:_)    = Nothing
matchTypes (_:_)    []       = Nothing
matchTypes (t1:ts1) (t2:ts2) = do
  s <- matchType t1 t2
  t <- matchTypes (map (subst s) ts1)(map (subst s) ts2)
  return (plusFM s t)

----------------------------------------------------------------------------

--- Generates an `n`-ary tuple constructor (only meaningful for `n>1`).
tupleCons :: Int -> QName
tupleCons n = pre ('(' : take (n-1) (repeat ',') ++ ")")

--- Transforms a name into a qualified name from the prelude.
pre :: String -> QName
pre f = ("Prelude",f)

----------------------------------------------------------------------------
