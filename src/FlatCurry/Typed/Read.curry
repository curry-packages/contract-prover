-----------------------------------------------------------------------------
--- Some operations to read type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version October 2021
---------------------------------------------------------------------------

module FlatCurry.Typed.Read where

import Data.IORef
import Data.List         ( find, nub )
import Data.Maybe        ( fromJust )

-- Imports from dependencies:
import FlatCurry.TypeAnnotated.Files ( readTypeAnnotatedFlatCurry )
import FlatCurry.Annotated.Goodies
import System.CurryPath              ( getLoadPathForModule, lookupModuleSource
                                     , runModuleActionQuiet, stripCurrySuffix )
import System.FilePath               ( (</>) )

import FlatCurry.Typed.Goodies
import FlatCurry.Typed.Names
import FlatCurry.Typed.Simplify
import FlatCurry.Typed.Types
import PackageConfig ( packagePath )
import ToolOptions
import VerifierState

----------------------------------------------------------------------------
--- Reads a typed FlatCurry program together with a possible `_SPEC` program
--- (containing further contracts) and simplify some expressions
--- (see module `FlatCurry.Typed.Simplify`).
readSimpTypedFlatCurryWithSpec :: Options -> String -> IO TAProg
readSimpTypedFlatCurryWithSpec opts mname =
  readTypedFlatCurryWithSpec opts mname >>= return . simpProg

--- Reads a typed FlatCurry program together with a possible `_SPEC` program
--- (containing further contracts).
--- All leading `ForallType` quantifiers are removed from function
--- signatures since they are not relevant here.
readTypedFlatCurryWithSpec :: Options -> String -> IO TAProg
readTypedFlatCurryWithSpec opts mname = do
  printWhenStatus opts $ "Loading typed FlatCurry program '" ++ mname ++ "'"
  prog  <- readTypedFlatCurryWithoutForall mname
  loadpath <- getLoadPathForModule specName
  mbspec   <- lookupModuleSource (loadpath ++ [packagePath </> "include"])
                                 specName
  maybe (return prog)
        (\ (_,specname) -> do
           let specpath = stripCurrySuffix specname
           printWhenStatus opts $ "Adding '" ++
             (if optVerb opts > 1 then specpath else specName) ++ "'"
           specprog <- runModuleActionQuiet readTypedFlatCurryWithoutForall
                                            specpath
           return (unionTAProg prog (rnmProg mname specprog))
        )
        mbspec
 where
  specName = mname ++ "_SPEC"

--- Reads a typed FlatCurry program and remove all leading
--- `ForallType` quantifiers from function signatures.
readTypedFlatCurryWithoutForall :: String -> IO TAProg
readTypedFlatCurryWithoutForall mname = do
  prog  <- readTypeAnnotatedFlatCurry mname
  return $ updProgFuncs (map (updFuncType stripForall)) prog

-- Strip outermost `ForallType` quantifications.
stripForall :: TypeExpr -> TypeExpr
stripForall texp = case texp of
  ForallType _ te  -> stripForall te
  _                -> texp

----------------------------------------------------------------------------
--- Extract all user-defined typed FlatCurry functions that might be called
--- by a given list of functions.
getAllFunctions :: IORef VState -> [QName] -> IO [TAFuncDecl]
getAllFunctions vstref newfuns = do
  currmods <- readIORef vstref >>= return . currTAProgs
  getAllFuncs currmods [] newfuns
 where
  getAllFuncs _ currfuncs [] = return (reverse currfuncs)
  getAllFuncs currmods currfuncs (newfun:newfuncs)
    | newfun `elem` map (pre . fst) transPrimCons ++ map funcName currfuncs
      || isPrimOp newfun
    = getAllFuncs currmods currfuncs newfuncs
    | fst newfun `elem` map progName currmods
    = maybe
        (-- if we don't find the qname, it must be a constructor:
         getAllFuncs currmods currfuncs newfuncs)
        (\fdecl -> getAllFuncs currmods (fdecl : currfuncs)
                               (newfuncs ++ nub (funcsOfFuncDecl fdecl)))
        (find (\fd -> funcName fd == newfun)
              (progFuncs
                 (fromJust (find (\m -> progName m == fst newfun) currmods))))
    | otherwise -- we must load a new module
    = do let mname = fst newfun
         opts <- readVerifyInfoRef vstref >>= return . toolOpts
         printWhenStatus opts $
           "Loading module '" ++ mname ++ "' for '"++ snd newfun ++"'"
         newmod <- readTypedFlatCurryWithoutForall mname >>= return . simpProg
         modifyIORef vstref (addProgToState newmod)
         getAllFuncs (newmod : currmods) currfuncs (newfun:newfuncs)

----------------------------------------------------------------------------
