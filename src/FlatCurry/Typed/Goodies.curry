-----------------------------------------------------------------------------
--- Some goodies to deal with type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version April 2019
---------------------------------------------------------------------------

module FlatCurry.Typed.Goodies where

import List         ( maximum, nub, union )

-- Imports from dependencies:
import Data.FiniteMap
import FlatCurry.Annotated.Goodies
import FlatCurry.Annotated.Pretty    ( ppExp )
import FlatCurry.Annotated.TypeSubst
import Text.Pretty                   ( showWidth )

import FlatCurry.Typed.Types

----------------------------------------------------------------------------
--- Returns the union of two typed FlatCurry programs.
unionTAProg :: TAProg -> TAProg -> TAProg
unionTAProg (AProg name imps1 types1 funcs1 ops1)
            (AProg _    imps2 types2 funcs2 ops2) =
  AProg name (filter (/=name) (union imps1 imps2))
        (types1++types2) (funcs1++funcs2) (ops1++ops2)

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

--- Pretty prints an expression.
ppTAExpr :: TAExpr -> String
ppTAExpr e = showWidth 200 (ppExp e)

--- Sets the top annotation of a pattern.
setAnnPattern :: TypeExpr -> TAPattern -> TAPattern
setAnnPattern ann (ALPattern _ lit) = ALPattern ann lit
setAnnPattern ann (APattern _ aqn vars) = APattern ann aqn vars

----------------------------------------------------------------------------
--- Eta-expansion of user-defined function declarations.
etaExpandFuncDecl :: TAFuncDecl -> TAFuncDecl
etaExpandFuncDecl fdecl@(AFunc _ _ _ _ (AExternal _ _)) = fdecl
etaExpandFuncDecl (AFunc qn ar vis texp (ARule tr args rhs)) =
  AFunc qn (ar + length etavars) vis texp
        (ARule tr (args ++ etavars)
               (applyExp rhs (map (\ (v,t) -> AVar t v) etavars)))
 where
  freshvar = maximum (0 : map fst args ++ allVars rhs) + 1
  argtypes = argTypes texp
  etavars  = zip [freshvar ..] (drop ar argtypes)

--- Apply arguments to a given FlatCurry expression by transforming
--- this expression whenever possible.
applyExp :: TAExpr -> [TAExpr] -> TAExpr
applyExp exp [] = exp
applyExp exp vars@(v1:vs) = case exp of
  AComb te ct (qf,qt) cargs -> case ct of
    FuncPartCall m -> applyExp (AComb (dropArgTypes 1 te)
                                      (if m==1 then FuncCall
                                               else FuncPartCall (m-1))
                                      (qf,qt) 
                                      (cargs ++ [v1]))
                               vs
    _ -> applyExp (AComb (dropArgTypes 1 te) FuncCall
                         (pre "apply", FuncType (annExpr v1) te) [exp, v1]) vs
  ACase  te ct e brs -> ACase (adjustType te) ct e
                 (map (\ (ABranch p be) -> ABranch p (applyExp be vars)) brs)
  AOr    te e1 e2 -> AOr (adjustType te) (applyExp e1 vars) (applyExp e2 vars)
  ALet   te bs e  -> ALet   (adjustType te) bs (applyExp e vars)
  AFree  te fvs e -> AFree  (adjustType te) fvs (applyExp e vars)
  ATyped te e ty  -> ATyped (adjustType te) (applyExp e vars) (adjustType ty)
  AVar   te _     -> applyExp (AComb (dropArgTypes 1 te) FuncCall
                                     (pre "apply", FuncType (annExpr v1) te)
                                     [exp, v1]) vs
  ALit   _  _     -> error "etaExpandFuncDecl: cannot apply literal"
 where
  adjustType ty = dropArgTypes (length vars) ty 

--- Remove the given number of argument types from a (nested) functional type.
dropArgTypes :: Int -> TypeExpr -> TypeExpr
dropArgTypes n ty
  | n==0      = ty
  | otherwise = case ty of FuncType _ rt -> dropArgTypes (n-1) rt
                           _ -> error "dropArgTypes: too few argument types"

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
--- Transform name into Prelude-qualified name.
pre :: String -> QName
pre f = ("Prelude",f)

----------------------------------------------------------------------------
