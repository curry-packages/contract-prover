-----------------------------------------------------------------------------
--- This module contains a transformation from possibly
--- non-deterministically defined operations into purely deterministic
--- operations. The transformation is based on the "planned choices"
--- approach described in [this paper](http://dx.doi.org/10.4204/EPTCS.234.13):
--- 
--- S. Antoy, M. Hanus, and S. Libby:
--- _Proving non-deterministic computations in Agda_.
--- In Proc. of the 24th International Workshop on Functional and
--- (Constraint) Logic Programming (WFLP 2016),
--- volume 234 of Electronic Proceedings in Theoretical Computer Science,
--- pages 180--195. Open Publishing Association, 2017.
---
--- Thus, an additional "choice plan" argument is added to each
--- non-deterministic operation. This plan determines the
--- branches chosen by the operation to compute some value.
---
--- This transformation can be used to verify non-determinstic operations
--- by showing their correct behavior for all possible plans.
---
--- @author  Michael Hanus
--- @version August 2019
---------------------------------------------------------------------------

module FlatCurry.Typed.NonDet2Det
  ( nondetOfFuncDecls, addChoiceFuncDecl )
 where

import List ( maximum, nub )

-- Imports from dependencies:
import FlatCurry.Annotated.Goodies

import FlatCurry.Typed.Goodies ( funcsOfExpr, pre )
import FlatCurry.Typed.Types

----------------------------------------------------------------------------
--- Returns the non-determinism status for all functions in a
--- list of function declarations.
--- It is assumed that this list contains the declarations of all functions
--- occurring in these declarations.
--- It is implemented by a very simple fixpoint iteration.
--- This is sufficient for the small lists considered in this application.
nondetOfFuncDecls :: [TAFuncDecl] -> [(QName,Bool)]
nondetOfFuncDecls fds = ndIterate (map (\fd -> (funcName fd, False)) fds)
 where
  ndIterate nds =
    let newnds = map (\fd -> (funcName fd, isNonDetFunc nds fd)) fds
    in if newnds == nds then nds
                        else ndIterate newnds

  isNonDetFunc nds fdecl =
    choiceName `elem` fs || or (map (\f -> maybe False id (lookup f nds)) fs)
   where fs = choicesOfFuncDecl fdecl

--- Returns all operations occurring in a function declaration where
--- any occurrence of `Or` or `Free` is translated into an occurrence
--- of `Prelude.?`.
--- Thus, the result can be used to analyze whether a function definition
--- is non-deterministic or calls another non-deterministic operation.
choicesOfFuncDecl :: TAFuncDecl -> [QName]
choicesOfFuncDecl fd =
  nub (trRule (\_ _ e -> choicesOfExp e) (\_ _ -> []) (funcRule fd))
 where
  --- Returns all operations occurring in an expression where any occurrence
  --- of `Or` or `Free` is translated into an occurrence of `Prelude.?`.
  choicesOfExp =
    trExpr (\_ _ -> [])
           (\_ _ -> [])
           (\_ ct (qn,_) fs ->
              if isCombTypeFuncCall ct || isCombTypeFuncPartCall ct
                then qn : concat fs
                else concat fs)
           (\_ bs fs -> concatMap snd bs ++ fs)
           (\_ _ _ -> [choiceName])
           (\_ _ _ -> [choiceName])
           (\_ _ fs fss -> concat (fs:fss))
           (\_ -> id)
           (\_ fs _ -> fs)

choiceName :: QName
choiceName = pre "?"

hasNonDetInfo :: [(QName,Bool)] -> QName -> Bool
hasNonDetInfo ndinfo qn = maybe False id (lookup qn ndinfo)

----------------------------------------------------------------------------
--- Add a "choice plan" argument to a function declaration for all
--- non-deterministic functions (according to first argument).
addChoiceFuncDecl :: [(QName,Bool)] -> TAFuncDecl -> TAFuncDecl
addChoiceFuncDecl _ fdecl@(AFunc _ _ _ _ (AExternal _ _)) = fdecl
addChoiceFuncDecl ndinfo fdecl@(AFunc qn ar vis texp (ARule tr args rhs)) =
  if hasNonDetInfo ndinfo qn
    then AFunc qn (ar + 1) vis (FuncType cpType texp)
               (ARule tr (carg : args) (snd (choiceExp choices rhs)))
    else fdecl
 where
  cpVar  = maximum (0 : map fst args ++ allVars rhs) + 1
  cpType = TCons (pre "Choice") []
  carg   = (cpVar, cpType)
  -- number of non-deterministic operations in right-hand side:
  numnds = orOfExpr rhs +
           length (filter (hasNonDetInfo ndinfo) (funcsOfExpr rhs))
  choices = choicesFor numnds (AVar cpType cpVar)

  -- Add "choice plan" arguments for all non-deterministic operations
  -- and transform `Or` expressions into if-then-else w.r.t. a choice.
  -- The first argument is a list of disjoint choice expressions.
  choiceExp chs exp = case exp of
    ALit  _  _ -> (chs,exp)
    AVar  _  _ -> (chs,exp)
    AComb te ct (qf,qt) cargs ->
      if hasNonDetInfo ndinfo qf
        then let (ch1,targs) = choiceExps (tail chs) cargs in
             (ch1, AComb te ct (qf, FuncType cpType qt) (head chs : targs))
        else let (ch1,targs) = choiceExps chs cargs in
             (ch1, AComb te ct (qf,qt) targs)
    ACase te ct e brs ->
      let (ch1,e1:bes1) = choiceExps chs (e : map (\ (ABranch _ be) -> be) brs)
      in (ch1, ACase te ct e1
                 (map (\ (ABranch p _,be1) -> ABranch p be1) (zip brs bes1)))
    AOr te e1 e2 ->
      let (ch1,es) = choiceExps (tail chs) [e1,e2] in
      (ch1,
       AComb te FuncCall
             (pre "if_then_else",
              FuncType (TCons (pre "Bool") []) (FuncType te (FuncType te te)))
            (AComb boolType FuncCall (pre "choose",chooseType) [head chs] : es))
    ALet te bs e ->
      let (ch1,e1:bes1) = choiceExps chs (e : map snd bs)
      in (ch1, ALet te (zip (map fst bs) bes1) e1)
    AFree  te fvs e -> let (ch1,e1) = choiceExp chs e
                       in (ch1, AFree  te fvs e1)
    ATyped te e ty  -> let (ch1,e1) = choiceExp chs e
                       in (ch1, ATyped te e1 ty)
   where
    chooseType = FuncType cpType boolType
    boolType = TCons (pre "Bool") []

  choiceExps chs [] = (chs,[])
  choiceExps chs (e:es) = let (ch1,e1)  = choiceExp  chs e
                              (ch2,es1) = choiceExps ch1 es
                          in (ch2, e1:es1)

  -- Computes a list of disjoint choice plans for a given number of choices
  -- and a base choice variable.
  choicesFor :: Int -> TAExpr -> [TAExpr]
  choicesFor n ch
    | n <= 1
    = [ch]
    | otherwise
    = choicesFor (n `div` 2)
                 (AComb cpType FuncCall (pre "lchoice", lrchType) [ch]) ++
      choicesFor (n - n `div` 2)
                 (AComb cpType FuncCall (pre "rchoice", lrchType) [ch])
   where
    lrchType = FuncType cpType cpType


--- Returns the number of `Or` occurring in an expression.
orOfExpr :: TAExpr -> Int
orOfExpr = trExpr (\_ _ -> 0)
                  (\_ _ -> 0)
                  (\_ _ _ ns -> foldr (+) 0 ns)
                  (\_ bs n -> n + foldr (+) 0 (map snd bs))
                  (\_ _ n -> n)
                  (\_ n1 n2 -> 1 + n1 + n2)
                  (\_ _ n bs -> n + foldr (+) 0 bs)
                  (\_ n -> n)
                  (\_ n _ -> n)

--- Remove the given number of argument types from a (nested) functional type.
dropArgTypes :: Int -> TypeExpr -> TypeExpr
dropArgTypes n ty
  | n==0      = ty
  | otherwise = case ty of FuncType _ rt -> dropArgTypes (n-1) rt
                           _ -> error "dropArgTypes: too few argument types"

----------------------------------------------------------------------------
