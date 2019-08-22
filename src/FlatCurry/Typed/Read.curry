-----------------------------------------------------------------------------
--- Some operations to read type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version August 2019
---------------------------------------------------------------------------

module FlatCurry.Typed.Read where

import FilePath     ( (</>) )
import IOExts
import List         ( find, nub )
import Maybe        ( fromJust )

-- Imports from dependencies:
import FlatCurry.Annotated.Files   ( readTypedFlatCurry )
import FlatCurry.Annotated.Goodies
import System.CurryPath ( getLoadPathForModule, lookupModuleSource
                        , stripCurrySuffix )

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
           printWhenStatus opts $ "Adding '" ++
             (if optVerb opts > 1 then specpath else specName) ++ "'"
           specprog <- readTypedFlatCurry specpath
           return (unionTAProg prog (rnmProg mname specprog))
        )
        mbspec
 where
  specName = mname ++ "_SPEC"

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
         newmod <- readTypedFlatCurry mname >>= return . simpProg
         modifyIORef vstref (addProgToState newmod)
         getAllFuncs (newmod : currmods) currfuncs (newfun:newfuncs)

----------------------------------------------------------------------------
