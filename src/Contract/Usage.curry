------------------------------------------------------------------------
--- This module contains some operations to check the correct usage of
--- contracts (i.e., the occurrences and types of specification and
--- pre/postconditions) in a type-annotated FlatCurry program.
---
--- @author Michael Hanus
--- @version April 2019
------------------------------------------------------------------------

module Contract.Usage ( checkContractUsage ) where

import List

import FlatCurry.Annotated.Goodies
import FlatCurry.Typed.Types
import Contract.Names

--- Checks the intended usage of contracts.
checkContractUsage :: TAProg -> [(QName,String)]
checkContractUsage prog =
  let mn           = progName prog
      allops       = map nameArityOfFunDecl (progFuncs prog)
      allopsnames  = map fst3 allops
      specops      = map (\ (n,a,t) ->
                            (fromSpecName (decodeContractName n), a, t))
                         (funDeclsWithNameArity isSpecName prog)
      preops       = map (\ (n,a,t) ->
                            (fromPreCondName (decodeContractName n), a, t))
                         (funDeclsWithNameArity isPreCondName prog)
      postops      = map (\ (n,a,t) ->
                            (fromPostCondName (decodeContractName n), a-1, t))
                         (funDeclsWithNameArity isPostCondName prog)
      nonfailops   = map (\ (n,a,t) ->
                            (fromNonFailName (decodeContractName n), a, t))
                         (funDeclsWithNameArity isNonFailName prog)
      onlyprecond  = map fst3 preops     \\ allopsnames
      onlypostcond = map fst3 postops    \\ allopsnames
      onlyspec     = map fst3 specops    \\ allopsnames
      onlynonfail  = map fst3 nonfailops \\ allopsnames
      errmsg   = "No implementation for this "
      preerrs  = map (\ n -> ((mn, toPreCondName n), errmsg ++ "precondition"))
                     onlyprecond
      posterrs = map (\ n -> ((mn, toPostCondName n),errmsg ++ "postcondition"))
                     onlypostcond
      specerrs = map (\ n -> ((mn, toSpecName n), errmsg ++ "specification"))
                     onlyspec
      nferrs   = map (\ n -> ((mn, toNonFailName n),
                              errmsg ++ "non-fail condition"))
                     onlynonfail
   in preerrs ++ posterrs ++ specerrs ++ nferrs ++
      checkNonFailTypes  mn allops nonfailops ++
      checkPreTypes      mn allops preops ++
      checkPostTypes     mn allops postops ++
      checkSpecTypes     mn allops specops
 where
  fst3 (x,_,_) = x

checkNonFailTypes :: String -> [(String,Int,TypeExpr)]
                  -> [(String,Int,TypeExpr)] -> [(QName,String)]
checkNonFailTypes mn allops nfops = concatMap checkNonFailTypeOf nfops
 where
  checkNonFailTypeOf (n,_,t) =
    maybe (notFoundError "non-fail condition" (mn,n))
          (\ (_,_,ft) -> checkNonFailType n t ft)
          (find (\ (f,_,_) -> f == n) allops)

  checkNonFailType n pt ft
    | resultType pt /= TCons ("Prelude","Bool") []
    = illegalTypeError "Non-fail condition" (mn, toNonFailName n)
    | argTypes pt /= argTypes ft
    = wrongTypeError "non-fail condition" (mn, toNonFailName n)
    | otherwise
    = []
 
checkPreTypes :: String -> [(String,Int,TypeExpr)] -> [(String,Int,TypeExpr)]
              -> [(QName,String)]
checkPreTypes mn allops preops = concatMap checkPreTypeOf preops
 where
  checkPreTypeOf (n,_,t) =
    maybe (notFoundError "precondition" (mn,n))
          (\ (_,_,ft) -> checkPreType n t ft)
          (find (\ (f,_,_) -> f == n) allops)

  checkPreType n pt ft
    | resultType pt /= TCons ("Prelude","Bool") []
    = illegalTypeError "Precondition" (mn, toPreCondName n)
    | argTypes pt /= argTypes ft
    = wrongTypeError "precondition" (mn, toPreCondName n)
    | otherwise
    = []
 
checkPostTypes :: String -> [(String,Int,TypeExpr)] -> [(String,Int,TypeExpr)]
               -> [(QName,String)]
checkPostTypes mn allops postops = concatMap checkPostTypeOf postops
 where
  checkPostTypeOf (n,_,t) =
    maybe (notFoundError "postcondition" (mn,n))
          (\ (_,_,ft) -> checkPostType n t ft)
          (find (\ (f,_,_) -> f == n) allops)

  checkPostType n pt ft
    | resultType pt /= TCons ("Prelude","Bool") []
    = illegalTypeError "Postcondition" (mn, toPostCondName n)
    | argTypes pt /= argTypes ft ++ [resultType ft]
    = wrongTypeError "postcondition" (mn, toPostCondName n)
    | otherwise
    = []

checkSpecTypes :: String -> [(String,Int,TypeExpr)] -> [(String,Int,TypeExpr)]
               -> [(QName,String)]
checkSpecTypes mn allops specops = concatMap checkSpecTypeOf specops
 where
  checkSpecTypeOf (n,_,t) =
    maybe (notFoundError "specification" (mn,n))
          (\ (_,_,ft) -> checkSpecType n t ft)
          (find (\ (f,_,_) -> f == n) allops)

  checkSpecType n pt ft
    | pt /= ft
    = wrongTypeError "specification" (mn, toSpecName n)
    | otherwise
    = []

notFoundError :: String -> QName -> [(QName,String)]
notFoundError cond qn =
  [(qn, "Operation for " ++ cond ++ " not found!")]

illegalTypeError :: String -> QName -> [(QName,String)]
illegalTypeError cond qn = [(qn, cond ++ " has illegal type")]

wrongTypeError :: String -> QName -> [(QName,String)]
wrongTypeError cond qn = [(qn, "Type of " ++ cond ++ " does not match")]

-- Returns, for all function declarations which satisfy the predicate
-- given as the first argument, the function name, arity, and type.
funDeclsWithNameArity :: (String -> Bool) -> TAProg
                      -> [(String,Int,TypeExpr)]
funDeclsWithNameArity pred prog =
  map nameArityOfFunDecl
      (filter (pred . snd . funcName) (progFuncs prog))

-- Returns the unqualified name, arity, and type from a function declaration.
nameArityOfFunDecl :: TAFuncDecl -> (String,Int,TypeExpr)
nameArityOfFunDecl fd = (snd (funcName fd), length (argTypes ftype), ftype)
 where
  ftype = funcType fd

------------------------------------------------------------------------
