-----------------------------------------------------------------------------
--- A tool to translate FlatCurry operations into SMT assertions.
---
--- @author  Michael Hanus
--- @version September 2017
---------------------------------------------------------------------------

module Curry2SMT where

import Maybe        ( fromMaybe )

-- Imports from dependencies:
import FlatCurry.Annotated.Goodies ( argTypes, resultType )
import FlatCurry.Annotated.Types

-- Imports from package modules:
import BoolExp
import TypedFlatCurryGoodies

-- Testing:
m1 :: IO ()
m1 = funcs2SMT [("Prelude","take")] >>= putStrLn

m2 :: IO ()
m2 = do let fnames = ["null","length","take"]
        funcs2SMT (map pre fnames) >>= putStrLn

--- Translates a list of operations specified by their qualified name
--- (together with all operations on which these operation depend on)
--- into an SMT string that axiomatizes their semantics.
funcs2SMT :: [QName] -> IO String
funcs2SMT qns = do
  funs <- getAllFunctions [] []  qns
  return $ unlines (map ftype2SMT funs ++ [""] ++ map fdecl2SMT funs)

-- Translate a function declaration into an SMT function type declaration
ftype2SMT :: TAFuncDecl -> String
ftype2SMT (AFunc qn _ _ texp _) =
  asLisp ["declare-fun", transOpName qn,
          asLisp (map (smtBE . type2SMTExp) (argTypes texp)),
          smtBE (type2SMTExp (resultType texp))]

-- Axiomatize a function rule as an SMT assertion.
fdecl2SMT :: TAFuncDecl -> String
fdecl2SMT (AFunc qn _ _ _ rule) = unlines
  ["; define '" ++ showQName qn ++ "' by axiomatization of defining rules:",
   smtBE (rule2SMT rule)]
 where
  rule2SMT (AExternal _ s) =
    assertSMT $ bEqu (BTerm (transOpName qn) []) (BTerm ("External:" ++ s) [])
  rule2SMT (ARule _ vs exp) =
    assertSMT $ forallBinding (map (\ (v,t) -> (v, type2SMTExp t)) vs)
                              (if ndExpr exp
                                 then exp2SMT (Just lhs) exp
                                 else bEqu lhs (exp2SMT Nothing exp))
   where
    lhs = BTerm (transOpName qn) (map (BVar . fst) vs)

-- Translate a typed FlatCurry expression into an SMT expression.
-- If the first argument contains an SMT expression, an equation between
-- this expression and the translated result expression is generated.
-- This is useful to axiomatize non-deterministic operations.
exp2SMT :: Maybe BoolExp -> TAExpr -> BoolExp
exp2SMT lhs exp = case exp of
  AVar _ i          -> makeRHS (BVar i)
  ALit _ l          -> makeRHS (lit2bool l)
  AComb _ _ (qn,_) args ->
    makeRHS (BTerm (transOpName qn) (map (exp2SMT Nothing) args))
  ACase _ _ e brs -> let be = exp2SMT Nothing e
                     in branches2SMT be brs
  ALet   _ bs e -> letBinding (map (\ ((v,_),be) -> (v, exp2SMT Nothing be)) bs)
                              (exp2SMT lhs e)
  ATyped _ e _ -> exp2SMT lhs e
  AFree  _ fvs e -> forallBinding (map (\ (v,t) -> (v, type2SMTExp t)) fvs)
                                  (exp2SMT lhs e)
  AOr    _ e1 e2 -> Disj [exp2SMT lhs e1, exp2SMT lhs e2]
 where
  makeRHS rhs = maybe rhs (\l -> bEqu l rhs) lhs

  branches2SMT _ [] = error "branches2SMT: empty branch list"
  branches2SMT be [ABranch p e] = branch2SMT be p e
  branches2SMT be (ABranch p e : brs@(_:_)) =
    BTerm "ite" [bEqu be (pat2bool p), branch2SMT be p e,
                 branches2SMT be brs]
  
  branch2SMT _  (ALPattern _ _) e = exp2SMT lhs e
  branch2SMT be (APattern _ (qf,_) ps) e = case ps of
    [] -> exp2SMT lhs e
    _  -> letBinding (map (\ (s,v) -> (v, BTerm s [be]))
                          (zip (selectors qf) (map fst ps)))
                     (exp2SMT lhs e)

selectors :: QName -> [String]
selectors qf | qf == ("Prelude",":") = ["head","tail"]
             | otherwise = error $ "Unknown selectors: " ++ snd qf

--- Translates a FlatCurry type expression into a corresponding
--- SMT expression.
type2SMTExp :: TypeExpr -> BoolExp
type2SMTExp (TVar _) = BTerm "TVar" []
type2SMTExp (FuncType dom ran) = BTerm "->" (map type2SMTExp [dom,ran])
type2SMTExp (TCons (mn,tc) targs)
  | mn=="Prelude" && length targs == 0 = BTerm tc []
  | mn=="Prelude" && tc == "[]" && length targs == 1
  = BTerm "List" [type2SMTExp (head targs)]
  | otherwise = BTerm (mn ++ "." ++ tc) [] -- TODO: complete

----------------------------------------------------------------------------

--- Translates a pattern into an SMT expression.
pat2bool :: TAPattern -> BoolExp
pat2bool (ALPattern _ l)    = lit2bool l
pat2bool (APattern _ (qf,_) ps) = BTerm (transOpName qf) (map (BVar . fst) ps)

--- Translates a literal into an SMT expression.
lit2bool :: Literal -> BoolExp
lit2bool (Intc i)   = BTerm (show i) []
lit2bool (Floatc i) = BTerm (show i) []
lit2bool (Charc i)  = BTerm (show i) []

--- Translates a qualified FlatCurry name into an SMT string.
transOpName :: QName -> String
transOpName (mn,fn)
 | mn=="Prelude" = fromMaybe (mn ++ "_" ++ fn)
                             (lookup fn (primCons ++ preludePrimOps))
 | otherwise     = mn ++ "_" ++ fn

--- Translates an SMT string into qualified FlatCurry name.
--- Returns Nothing if it was not a qualified name.
untransOpName :: String -> Maybe QName
untransOpName s = let (mn,ufn) = break (=='_') s in
 if null ufn
   then Nothing
   else Just (mn, tail ufn)

----------------------------------------------------------------------------
