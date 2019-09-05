---------------------------------------------------------------------------
--- A tool to prove pre- or postconditions via an SMT solver (Z3)
--- and to remove the statically proven conditions from a program.
---
--- @author  Michael Hanus
--- @version August 2019
---------------------------------------------------------------------------
-- A few things to be done to improve contract checking:
--
-- * eta-expand pre- and postconditions (before contract checking)
--   in order to generate correct SMT formulas
---------------------------------------------------------------------------

module ContractProver where

import Directory    ( doesFileExist )
import Integer      ( ilog )
import IOExts
import List         ( deleteBy, elemIndex, find, init, intersect, isSuffixOf
                    , maximum, minimum, nub, partition, splitOn, union )
import Maybe        ( catMaybes, isJust )
import ReadShowTerm ( showTerm )
import State
import System       ( exitWith, getArgs, getEnviron, system )

-- Imports from dependencies:
import Contract.Names
import Contract.Usage ( checkContractUsage )
import FilePath                    ( (</>) )
import FlatCurry.Files
import FlatCurry.Types
import qualified FlatCurry.Goodies as FCG
import FlatCurry.Annotated.Files ( readTypedFlatCurry, typedFlatCurryFileName )
import FlatCurry.Annotated.Goodies
import FlatCurry.Annotated.Types
import FlatCurry.Annotated.TypeSubst ( substRule )
import ShowFlatCurry                 ( showCurryModule )

-- Imports from package modules:
import ESMT
import Curry2SMT
import FlatCurry.Typed.Build
import FlatCurry.Typed.Read
import FlatCurry.Typed.Goodies
import FlatCurry.Typed.Names
import FlatCurry.Typed.Simplify ( simpProg, simpFuncDecl, simpExpr )
import FlatCurry.Typed.Types
import PackageConfig  ( packagePath )
import ToolOptions
import VerifierState

------------------------------------------------------------------------

banner :: String
banner = unlines [bannerLine, bannerText, bannerLine]
 where
   bannerText = "Contract Checking/Verification Tool (Version of 05/09/19)"
   bannerLine = take (length bannerText) (repeat '=')

-- Path name of module containing auxiliary operations for contract checking.
contractCheckerModule :: String
contractCheckerModule = packagePath </> "include" </> "ContractChecker"

---------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  (opts,progs) <- processOptions banner args
  let optname = optName opts
  if not (null optname)
    then putStrLn $ "Precondition for '" ++ optname ++ "':\n" ++
                    encodeContractName (optname ++ "'pre") ++ "\n" ++
                    "Postcondition for '" ++ optname ++ "':\n" ++
                    encodeContractName (optname ++ "'post")
    else do
      when (optVerb opts > 0) $ putStrLn banner
      z3exists <- fileInPath "z3"
      unless (z3exists || not (optVerify opts)) $ putStrLn $ unlines $
        [ "WARNING: CONTRACT VERIFICATION SKIPPED:"
        , "The SMT solver Z3 is required for the verifier"
        , "but the program 'z3' is not found in the PATH!"]
      let opts' = if z3exists then opts else opts { optVerify = False }
      mapM_ (proveContracts opts') progs

---------------------------------------------------------------------------

-- Optimize a module by proving its contracts and remove verified
-- postconditions or add unverified preconditions.
proveContracts :: Options -> String -> IO ()
proveContracts opts mainmodname = do
  prog <- readTypedFlatCurryWithSpec opts mainmodname
  let errs = checkContractUsage (progName prog)
               (map (\fd -> (snd (funcName fd), funcType fd)) (progFuncs prog))
  if null errs
    then proveContractsInProg opts prog
    else do putStr $ unlines (map showOpError errs)
            exitWith 1
 where
  showOpError (qf,err) =
    snd qf ++ " (module " ++ fst qf ++ "): " ++ err

proveContractsInProg :: Options -> TAProg ->  IO ()
proveContractsInProg opts oprog = do
  let sprog = simpProg oprog
  printWhenAll opts $ unlines $
    ["ORIGINAL PROGRAM:",   line, showCurryModule (unAnnProg oprog), line,
     "SIMPLIFIED PROGRAM:", line, showCurryModule (unAnnProg sprog), line]
  vstref <- newIORef (initVState (makeVerifyInfo opts (progFuncs sprog)))
  modifyIORef vstref (addProgToState sprog)
  prog1 <- verifyPostConditions opts oprog vstref
  prog2 <- verifyPreConditions  opts prog1 vstref
  prog3 <- addPreConditions     opts prog2 vstref
  let unewprog = unAnnProg prog3
      mname    = progName prog3
  printWhenAll opts $ unlines $
    ["TRANSFORMED PROGRAM WITH CONTRACT CHECKING:", line,
     showCurryModule unewprog, line]
  vst2 <- readIORef vstref
  when (areContractsAdded vst2) $ do
    when (optFCY opts) $
      writeTransformedFCY opts (flatCurryFileName mname) unewprog
    when (optTFCY opts) $
      writeTransformedTFCY opts (typedFlatCurryFileName mname) prog3
  printWhenStatus opts (showStats vst2)
 where
  line = take 78 (repeat '-')

-- Writes the transformed FlatCurry program together with the contents
-- of the auxiliary `contractCheckerModule`.
writeTransformedFCY :: Options -> String -> Prog -> IO ()
writeTransformedFCY opts progfile prog = do
  ccprog <- readFlatCurry contractCheckerModule
  let rnmccprog = FCG.rnmProg (FCG.progName prog) ccprog
      ccimps    = FCG.progImports rnmccprog
      ccfuncs   = FCG.progFuncs rnmccprog
  writeFCY progfile
           (FCG.updProgFuncs (++ ccfuncs)
                             (FCG.updProgImports (`union` ccimps) prog))
  printWhenStatus opts $ "Transformed program written to: " ++ progfile

-- Writes the transformed typed FlatCurry program together with the contents
-- of the auxiliary `contractCheckerModule`.
writeTransformedTFCY :: Options -> String -> TAProg -> IO ()
writeTransformedTFCY opts progfile prog = do
  ccprog <- readTypedFlatCurry contractCheckerModule
  let rnmccprog = rnmProg (progName prog) ccprog
      ccimps    = progImports rnmccprog
      ccfuncs   = progFuncs rnmccprog
  writeTFCY progfile
            (updProgFuncs (++ ccfuncs)
                          (updProgImports (`union` ccimps) prog))
  printWhenStatus opts $ "Transformed program written to: " ++ progfile
 where
  -- should go into FlatCurry.Annotated.Files
  writeTFCY file tprog = writeFile file (showTerm tprog)

---------------------------------------------------------------------------
-- The state of the transformation process contains
-- * the current assertion
-- * a fresh variable index
-- * a list of all introduced variables and their types:
data TransState = TransState
  { preCond    :: Term
  , freshVar   :: Int
  , varTypes   :: [(Int,TypeExpr)]
  }

makeTransState :: Int -> [(Int,TypeExpr)] -> TransState
makeTransState = TransState tTrue

-- Increments fresh variable index.
incFreshVarIndex :: TransState -> TransState
incFreshVarIndex st = st { freshVar = freshVar st + 1 }

-- Adds variables to the state.
addVarTypes :: [(Int,TypeExpr)] -> TransState -> TransState
addVarTypes vts st = st { varTypes = vts ++ varTypes st }

---------------------------------------------------------------------------
-- Adds a precondition check to a original call of the form
-- `AComb ty ct (qf,tys) args`.
addPreConditionCheck :: TypeExpr -> CombType -> QName -> TypeExpr -> [TAExpr]
                     -> TAExpr
addPreConditionCheck ty ct qf@(mn,fn) tys args =
  AComb ty FuncCall
    ((mn, "checkPreCond"),
     FuncType ty (FuncType boolType (FuncType stringType (FuncType tt ty))))
    [ AComb ty ct (toNoCheckQName qf,tys) args
    , AComb boolType ct (toPreCondQName qf, pctype) args
    , string2TFCY fn
    , tupleExpr args
    ]
 where
  argtypes = map annExpr args
  tt       = tupleType argtypes
  pctype   = foldr FuncType boolType argtypes

--- Transform a qualified name into a name of the corresponding function
--- without precondition checking by adding the suffix "'NOCHECK".
toNoCheckQName :: (String,String) -> (String,String)
toNoCheckQName (mn,fn) = (mn, fn ++ "'NOCHECK")

--- Drops a possible "'NOCHECK" suffix from a qualified name.
fromNoCheckQName :: (String,String) -> (String,String)
fromNoCheckQName (mn,fn) =
  (mn, let rf = reverse fn
       in reverse (drop (if take 8 rf == "KCEHCON'" then 8 else 0) rf))

-- Adds a postcondition check to a program rule of a given operation.
addPostConditionCheck :: QName -> TARule -> TAExpr
addPostConditionCheck _ (AExternal _ _) =
  error $ "Trying to add postcondition to external function!"
addPostConditionCheck qf@(mn,fn) (ARule ty lhs rhs) = --ALit boolType (Intc 42)
  AComb ty FuncCall
    ((mn, "checkPostCond"),
     FuncType ty (FuncType (FuncType ty boolType)
                           (FuncType stringType (FuncType tt ty))))
    [ rhs
    , AComb boolType (FuncPartCall 1) (toPostCondQName qf, ty) args
    , string2TFCY fn
    , tupleExpr args
    ]
 where
  args = map (\ (i,t) -> AVar t i) lhs
  tt = tupleType (map annExpr args)

---------------------------------------------------------------------------
-- Add (non-trivial) preconditions:
-- If an operation `f` has some precondition `f'pre`,
-- replace the rule `f xs = rhs` by the following rules:
--
--     f xs = checkPreCond (f'NOCHECK xs) (f'pre xs) "f" xs
--     f'NOCHECK xs = rhs
addPreConditions :: Options -> TAProg -> IORef VState -> IO TAProg
addPreConditions _ prog vstref = do
  newfuns  <- mapM addPreCondition (progFuncs prog)
  return (updProgFuncs (const (concat newfuns)) prog)
 where
  addPreCondition fdecl@(AFunc qf ar vis fty rule) = do
    ti <- readVerifyInfoRef vstref
    return $
      if toPreCondQName qf `elem` map funcName (preConds ti)
        then let newrule = checkPreCondRule qf rule
             in [updFuncRule (const newrule) fdecl,
                 AFunc (toNoCheckQName qf) ar vis fty rule]
        else [fdecl]

  checkPreCondRule :: QName -> TARule -> TARule
  checkPreCondRule qn (ARule rty rargs _) =
    ARule rty rargs (addPreConditionCheck rty FuncCall qn rty
                       (map (\ (v,t) -> AVar t v) rargs))
  checkPreCondRule qn (AExternal _ _) = error $
    "addPreConditions: cannot add precondition to external operation '" ++
    snd qn ++ "'!"

---------------------------------------------------------------------------
-- Try to verify preconditions: If an operation `f` occurring in some
-- right-hand side has a precondition, a proof for the validity of
-- this precondition is extracted.
-- If the proof is not successful, a precondition check is added to this call.
verifyPreConditions :: Options -> TAProg -> IORef VState -> IO TAProg
verifyPreConditions opts prog vstref = do
  newfuns  <- mapM (provePreCondition opts vstref) (progFuncs prog)
  return (updProgFuncs (const newfuns) prog)

provePreCondition :: Options -> IORef VState -> TAFuncDecl -> IO TAFuncDecl
provePreCondition opts vstref fdecl = do
  ti <- readVerifyInfoRef vstref
  printWhenIntermediate opts $
    "Operation to be checked: " ++ snd (funcName fdecl)
  newrule <- optPreConditionInRule opts ti (funcName fdecl)
                                           (funcRule fdecl) vstref
  return (updFuncRule (const newrule) fdecl)

optPreConditionInRule :: Options -> VerifyInfo -> QName -> TARule
                      -> IORef VState -> IO TARule
optPreConditionInRule _ _ _ rl@(AExternal _ _) _ = return rl
optPreConditionInRule opts ti qn@(_,fn) (ARule rty rargs rhs) vstref = do
  let targs = zip [1..] (map snd rargs)
      -- compute precondition of operation:
      s0 = makeTransState (maximum (0 : map fst rargs ++ allVars rhs) + 1) rargs
      (precondformula,s1) = preCondExpOf ti qn targs s0
      s2 = s1 { preCond = precondformula }
  newrhs <- optPreCondInExp s2 rhs
  return (ARule rty rargs newrhs)
 where
  optPreCondInExp pts exp = case exp of
    AComb ty ct (qf,tys) args ->
      if qf == ("Prelude","?") && length args == 2
        then optPreCondInExp pts (AOr ty (args!!0) (args!!1))
        else do
          nargs <- mapM (optPreCondInExp pts) args
          if toPreCondQName qf `elem` map funcName (preConds ti)
            then do
              printWhenIntermediate opts $ "Checking call to " ++ snd qf
              let ((bs,_)     ,pts1) = normalizeArgs nargs pts
                  (bindexps   ,pts2) = mapS (binding2SMT True ti) bs pts1
                  (precondcall,pts3) = preCondExpOf ti qf
                                     (zip (map fst bs) (map annExpr args)) pts2
              -- TODO: select from 'bindexps' only demanded argument positions
              let title = "SMT script to verify precondition of '" ++ snd qf ++
                          "' in function '" ++ fn ++ "'"
              pcproof <- checkImplication opts vstref title (varTypes pts3)
                           (preCond pts) (tConj bindexps) precondcall
              let pcvalid = isJust pcproof
              modifyIORef vstref
                          (addPreCondToStats (snd qf ++ "("++fn++")") pcvalid)
              if pcvalid
                then do
                  printWhenStatus opts $
                    fn ++ ": PRECONDITION OF '" ++ snd qf ++ "': VERIFIED"
                  return $ AComb ty ct (toNoCheckQName qf, tys) nargs
                else do
                  printWhenStatus opts $
                    fn ++ ": PRECOND CHECK ADDED TO '" ++ snd qf ++ "'"
                  return $ AComb ty ct (qf,tys) nargs
            else return $ AComb ty ct (qf,tys) nargs
    ACase ty ct e brs -> do
      ne <- optPreCondInExp pts e
      let freshvar = freshVar pts
          (be,pts1) = binding2SMT True ti (freshvar,ne) (incFreshVarIndex pts)
          pts2 = pts1 { preCond = tConj [preCond pts, be]
                      , varTypes = (freshvar,annExpr ne) : varTypes pts1 }
      nbrs <- mapM (optPreCondInBranch pts2 freshvar) brs
      return $ ACase ty ct ne nbrs
    AOr ty e1 e2 -> do
      ne1 <- optPreCondInExp pts e1
      ne2 <- optPreCondInExp pts e2
      return $ AOr ty ne1 ne2
    ALet ty bs e -> do
      nes <- mapM (optPreCondInExp pts) (map snd bs)
      ne  <- optPreCondInExp pts e
      return $ ALet ty (zip (map fst bs) nes) ne
    AFree ty fvs e -> do
      ne <- optPreCondInExp pts e
      return $ AFree ty fvs ne
    ATyped ty e et -> do
      ne <- optPreCondInExp pts e
      return $ ATyped ty ne et
    _ -> return exp

  optPreCondInBranch pts dvar branch = do
    let (ABranch p e, pts1) = renamePatternVars pts branch
    let npts = pts1 { preCond = tConj [preCond pts1, tEquVar dvar (pat2SMT p)] }
    ne <- optPreCondInExp npts e
    return (ABranch p ne)

-- Rename argument variables of constructor pattern
renamePatternVars :: TransState -> TABranchExpr -> (TABranchExpr,TransState)
renamePatternVars pts (ABranch p e) =
  if isConsPattern p
    then let args = map fst (patArgs p)
             minarg = minimum (0 : args)
             maxarg = maximum (0 : args)
             fv = freshVar pts
             rnm i = if i `elem` args then i - minarg + fv else i
             nargs = map (\ (v,t) -> (rnm v,t)) (patArgs p)
         in (ABranch (updPatArgs (map (\ (v,t) -> (rnm v,t))) p)
                     (rnmAllVars rnm e),
             pts { freshVar = fv + maxarg - minarg + 1
                 , varTypes = nargs ++ varTypes pts })
    else (ABranch p e, pts)

---------------------------------------------------------------------------
-- Try to verify postconditions: If an operation `f` has a postcondition,
-- a proof for the validity of the postcondition is extracted.
-- If the proof is not successful, a postcondition check is added to `f`.
verifyPostConditions :: Options -> TAProg -> IORef VState -> IO TAProg
verifyPostConditions opts prog vstref = do
  ti <- readVerifyInfoRef vstref
  -- Operations with postcondition checks:
  let fdecls = progFuncs prog
  newfuns <- provePostConds ti (postConds ti) fdecls
  return $ updProgFuncs (const newfuns) prog
 where
  provePostConds _  []         fdecls = return fdecls
  provePostConds ti (pof:pofs) fdecls =
    provePostCondition opts ti pof fdecls vstref >>= provePostConds ti pofs

provePostCondition :: Options -> VerifyInfo -> TAFuncDecl -> [TAFuncDecl]
                   -> IORef VState -> IO [TAFuncDecl]
provePostCondition opts ti postfun allfuns vstref = do
  maybe (putStrLn ("Postcondition: " ++ pcname ++ "\n" ++
                   "Operation of this postcondition not found!") >>
         return allfuns)
        --(\checkfun -> provePC checkfun) --TODO: simplify definition
        (\checkfun -> provePC (simpFuncDecl checkfun))
        (find (\fd -> toPostCondName (snd (funcName fd)) ==
                      decodeContractName pcname)
              allfuns)
 where
  pcname = snd (funcName postfun)

  provePC checkfun = do
    let (postmn,postfn) = funcName postfun
        mainfunc        = snd (funcName checkfun)
        orgqn           = (postmn, reverse (drop 5 (reverse postfn)))
    --putStrLn $ "Check postcondition of operation " ++ mainfunc
    let farity = funcArity checkfun
        ftype  = funcType checkfun
        targsr = zip [1..] (argTypes ftype ++ [resultType ftype])
        (bodyformula,s0) = extractPostConditionProofObligation ti [1 .. farity]
                             (farity+1) (funcRule checkfun)
        (precondformula,s1)  = preCondExpOf ti orgqn (init targsr) s0
        (postcondformula,s2) = (applyFunc postfun targsr `bindS`
                                pred2smt) s1
    let title = "verify postcondition of '" ++ mainfunc ++ "'..."
    printWhenIntermediate opts $ "Trying to " ++ title
    pcproof <- checkImplication opts vstref ("SMT script to " ++ title)
                 (varTypes s2) (tConj [precondformula, bodyformula]) tTrue
                 postcondformula
    modifyIORef vstref (addPostCondToStats mainfunc (isJust pcproof))
    maybe
      (do printWhenStatus opts $ mainfunc ++ ": POSTCOND CHECK ADDED"
          return (map (addPostConditionTo (funcName postfun)) allfuns) )
      (\proof -> do
         unless (optNoProof opts) $
           writeFile ("PROOF_" ++ showQNameNoDots orgqn ++ "_" ++
                      "SatisfiesPostCondition.smt") proof
         printWhenStatus opts $ mainfunc ++ ": POSTCONDITION VERIFIED"
         return allfuns )
      pcproof

-- If the function declaration is the declaration of the given function name,
-- decorate it with a postcondition check.
addPostConditionTo :: QName -> TAFuncDecl -> TAFuncDecl
addPostConditionTo pfname fdecl = let fn = funcName fdecl in
  if toPostCondQName fn == pfname
    then updFuncBody (const (addPostConditionCheck fn (funcRule fdecl))) fdecl
    else fdecl


extractPostConditionProofObligation :: VerifyInfo -> [Int] -> Int -> TARule
                                    -> (Term,TransState)
extractPostConditionProofObligation _ _ _ (AExternal _ s) =
  (tComb ("External: " ++ s) [], makeTransState 0 [])
extractPostConditionProofObligation ti args resvar (ARule ty orgargs orgexp) =
  let exp    = rnmAllVars renameRuleVar orgexp
      rtype  = resType (length orgargs) ty
      state0 = makeTransState (maximum (resvar : allVars exp) + 1)
                              ((resvar, rtype) : zip args (map snd orgargs))
  in binding2SMT True ti (resvar,exp) state0
 where
  maxArgResult = maximum (resvar : args)
  renameRuleVar r = maybe (r + maxArgResult + 1)
                          (args!!)
                          (elemIndex r (map fst orgargs))

  resType n te = if n==0
                   then te
                   else case te of FuncType _ rt -> resType (n-1) rt
                                   _ -> error "Internal errror: resType!"

-- Returns the precondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding the `freshvar` index to them.
preCondExpOf :: VerifyInfo -> QName -> [(Int,TypeExpr)] -> State TransState Term
preCondExpOf ti qf args =
  maybe (returnS tTrue)
        (\fd -> applyFunc fd args `bindS` pred2smt)
        (find (\fd -> decodeContractQName (funcName fd)
                        == toPreCondQName (fromNoCheckQName qf))
              (preConds ti))

-- Returns the postcondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding `freshvar` to them and
-- return the new freshvar value.
postCondExpOf :: VerifyInfo -> QName -> [(Int,TypeExpr)]
              -> State TransState Term
postCondExpOf ti qf args =
  maybe (returnS tTrue)
        (\fd -> applyFunc fd args `bindS` pred2smt)
        (find (\fd -> decodeContractQName (funcName fd)
                        == toPostCondQName (fromNoCheckQName qf))
              (postConds ti))

-- Applies a function declaration on a list of arguments,
-- which are assumed to be variable indices, and returns
-- the renamed body of the function declaration.
-- All local variables are renamed by adding `freshvar` to them.
-- Also the new fresh variable index is returned.
applyFunc :: TAFuncDecl -> [(Int,TypeExpr)] -> State TransState TAExpr
applyFunc fdecl targs s0 =
  let tsub = maybe (error $ "applyFunc: types\n" ++
                            show (argTypes (funcType fdecl)) ++ "\n" ++
                            show (map snd targs) ++ "\ndo not match!")
                   id
                   (matchTypes (argTypes (funcType fdecl)) (map snd targs))
      (ARule _ orgargs orgexp) = substRule tsub (funcRule fdecl)
      exp = rnmAllVars (renameRuleVar orgargs) orgexp
      s1  = s0 { freshVar = max (freshVar s0)
                                (maximum (0 : args ++ allVars exp) + 1) }
  in (simpExpr $ applyArgs exp (drop (length orgargs) args), s1)
 where
  args = map fst targs
  -- renaming function for variables in original rule:
  renameRuleVar orgargs r = maybe (r + freshVar s0)
                                  (args!!)
                                  (elemIndex r (map fst orgargs))

  applyArgs e [] = e
  applyArgs e (v:vs) =
    -- simple hack for eta-expansion since the type annotations are not used:
    let e_v =  AComb failed FuncCall
                     (pre "apply", failed) [e, AVar failed v]
    in applyArgs e_v vs

-- Translates a Boolean FlatCurry expression into an SMT formula.
pred2smt :: TAExpr -> State TransState Term
pred2smt exp = case exp of
  AVar _ i              -> returnS (TSVar i)
  ALit _ l              -> returnS (lit2SMT l)
  AComb _ ct (qf,ftype) args ->
    if qf == pre "not" && length args == 1
      then pred2smt (head args) `bindS` \barg -> returnS (tNot barg)
      else mapS pred2smt args `bindS` \bargs ->
           returnS (TComb (cons2SMT (ct /= ConsCall || not (null bargs))
                                    False qf ftype) bargs)
  _     -> error $ "Translation of some Boolean expressions into SMT " ++
                   "not yet supported:\n" ++ show (unAnnExpr exp)


-- Translates a binding between a variable (represented by its index
-- in the first component) and a FlatCurry expression (second component).
-- The FlatCurry expression is translated into an SMT formula so that
-- the binding is axiomiatized as an equation between the variable
-- and the translated expression.
-- The translated expression is normalized when necessary.
-- For this purpose, a "fresh variable index" is passed as a state.
-- Moreover, the returned state contains also the types of all fresh variables.
-- If the first argument is `False`, the expression is not strictly demanded,
-- i.e., possible contracts of it (if it is a function call) are ignored.
binding2SMT :: Bool -> VerifyInfo -> (Int,TAExpr) -> State TransState Term
binding2SMT odemanded vi (oresvar,oexp) =
  exp2smt odemanded (oresvar, simpExpr oexp)
 where
  exp2smt demanded (resvar,exp) = case exp of
    AVar _ i -> returnS $ if resvar==i then tTrue
                                       else tEquVar resvar (TSVar i)
    ALit _ l -> returnS (tEquVar resvar (lit2SMT l))
    AComb ty ct (qf,_) args ->
      if qf == pre "?" && length args == 2
        then exp2smt demanded (resvar, AOr ty (args!!0) (args!!1))
        else normalizeArgs args `bindS` \ (bs,nargs) ->
             -- TODO: select from 'bindexps' only demanded argument positions
             mapS (exp2smt (isPrimOp qf || optStrict (toolOpts vi)))
                  bs `bindS` \bindexps ->
             comb2smt qf ty ct nargs bs bindexps
    ALet _ bs e ->
      getS `bindS` \ts ->
      putS (addVarTypes (map fst bs) ts) `bindS_`
      mapS (exp2smt False)
           (map (\ ((i,_),ae) -> (i,ae)) bs) `bindS` \bindexps ->
      exp2smt demanded (resvar,e) `bindS` \bexp ->
      returnS (tConj (bindexps ++ [bexp]))
    AOr _ e1 e2  ->
      exp2smt demanded (resvar,e1) `bindS` \bexp1 ->
      exp2smt demanded (resvar,e2) `bindS` \bexp2 ->
      returnS (tDisj [bexp1, bexp2])
    ACase _ _ e brs   ->
      getS `bindS` \ts ->
      let freshvar = freshVar ts in
      putS (addVarTypes [(freshvar, annExpr e)] (incFreshVarIndex ts)) `bindS_`
      exp2smt demanded (freshvar,e) `bindS` \argbexp ->
      mapS branch2smt (map (\b->(freshvar,b)) brs) `bindS` \bbrs ->
      returnS (tConj [argbexp, tDisj bbrs])
    ATyped _ e _ -> exp2smt demanded (resvar,e)
    AFree _ _ _ -> error "Free variables not yet supported!"
   where
    comb2smt qf rtype ct nargs bs bindexps
     | qf == pre "otherwise"
       -- specific handling for the moment since the front end inserts it
       -- as the last alternative of guarded rules...
     = returnS (tEquVar resvar tTrue)
     | ct == ConsCall -- translate data constructor
     = returnS (tConj (bindexps ++
                      [tEquVar resvar
                               (TComb (cons2SMT (null nargs) False qf rtype)
                                      (map arg2smt nargs))]))
     | qf == pre "apply"
     = -- cannot translate h.o. apply: ignore it
       returnS tTrue
     | isPrimOp qf
     = returnS (tConj (bindexps ++
                      [tEquVar resvar (TComb (cons2SMT True False qf rtype)
                                             (map arg2smt nargs))]))
     | otherwise -- non-primitive operation: add contract only if demanded
     = let targs = zip (map fst bs) (map annExpr nargs) in
       preCondExpOf vi qf targs `bindS` \precond ->
       postCondExpOf vi qf (targs ++ [(resvar,rtype)]) `bindS` \postcond ->
       returnS (tConj (bindexps ++ if demanded then [precond,postcond] else []))
    
    branch2smt (cvar, (ABranch p e)) =
      exp2smt demanded (resvar,e) `bindS` \branchbexp ->
      getS `bindS` \ts ->
      putS ts { varTypes = patvars ++ varTypes ts} `bindS_`
      returnS (tConj [ tEquVar cvar (pat2SMT p), branchbexp])
     where
      patvars = if isConsPattern p
                  then patArgs p
                  else []
  
    arg2smt e = case e of AVar _ i -> TSVar i
                          ALit _ l -> lit2SMT l
                          _        -> error $ "Not normalized: " ++ show e

normalizeArgs :: [TAExpr] -> State TransState ([(Int,TAExpr)],[TAExpr])
normalizeArgs [] = returnS ([],[])
normalizeArgs (e:es) = case e of
  AVar _ i -> normalizeArgs es `bindS` \ (bs,nes) ->
              returnS ((i,e):bs, e:nes)
  _        -> getS `bindS` \ts ->
              let fvar = freshVar ts
                  nts  = addVarTypes [(fvar,annExpr e)] (incFreshVarIndex ts)
              in putS nts `bindS_`
                 normalizeArgs es `bindS` \ (bs,nes) ->
                 returnS ((fvar,e):bs, AVar (annExpr e) fvar : nes)


unzipBranches :: [TABranchExpr] -> ([TAPattern],[TAExpr])
unzipBranches []                 = ([],[])
unzipBranches (ABranch p e : brs) = (p:xs,e:ys)
 where (xs,ys) = unzipBranches brs

---------------------------------------------------------------------------
checkImplication :: Options -> IORef VState -> String -> [(Int,TypeExpr)]
                 -> Term -> Term -> Term -> IO (Maybe String)
checkImplication opts vstref scripttitle vartypes assertion impbindings imp =
  if optVerify opts
    then checkImplicationWithSMT opts vstref scripttitle vartypes
                                 assertion impbindings imp
    else return Nothing

-- Calls the SMT solver to check whether an assertion implies some
-- (pre/post) condition.
-- Returns `Nothing` if the proof was not successful, otherwise
-- the SMT script containing the proof (to obtain `unsat`) is returned.
checkImplicationWithSMT :: Options -> IORef VState -> String -> [(Int,TypeExpr)]
                        -> Term -> Term -> Term -> IO (Maybe String)
checkImplicationWithSMT opts vstref scripttitle vartypes
                        assertion impbindings imp = do
  let allsyms = catMaybes
                  (map (\n -> maybe Nothing Just (untransOpName n))
                       (map qidName
                         (allQIdsOfTerm (tConj [assertion, impbindings, imp]))))
  unless (null allsyms) $ printWhenIntermediate opts $
    "Translating operations into SMT: " ++ unwords (map showQName allsyms)
  (smtfuncs,fdecls,ndinfo) <- funcs2SMT opts vstref allsyms
  smttypes <- genSMTTypes vstref vartypes fdecls [assertion,impbindings,imp]
  let freshvar = maximum (map fst vartypes) + 1
      ([assertionC,impbindingsC,impC],newix) =
         nondetTransL ndinfo freshvar [assertion,impbindings,imp]
      smt = smttypes ++
            [ EmptyLine, smtfuncs, EmptyLine
            , Comment "Free variables:" ] ++
            map typedVar2SMT
                (vartypes ++ map toChoiceVar [freshvar .. newix-1]) ++
            [ EmptyLine
            , Comment "Boolean formula of assertion (known properties):"
            , sAssert assertionC, EmptyLine
            , Comment "Bindings of implication:"
            , sAssert impbindingsC, EmptyLine
            , Comment "Assert negated implication:"
            , sAssert (tNot impC), EmptyLine
            , Comment "check satisfiability:"
            , CheckSat
            , Comment "if unsat, we can omit this part of the contract check"
            ]
  smtstdtypes <- readInclude "Prelude.smt"
  smtchoice   <- if or (map snd ndinfo)
                   then readInclude "Prelude_Choice.smt"
                   else return ""
  let smtprelude = smtstdtypes ++ smtchoice
  callSMT opts $ "; " ++ scripttitle ++ "\n\n" ++ smtprelude ++ showSMT smt
 where
  readInclude f = readFile (packagePath </> "include" </> f)
  toChoiceVar i = (i, TCons (pre "Choice") [])

-- Computes SMT type declarations for all types occurring in the
-- variable types, function declarations, or as sorts in SMT terms.
genSMTTypes :: IORef VState -> [(Int,TypeExpr)] -> [TAFuncDecl] -> [Term]
            -> IO [Command]
genSMTTypes vstref vartypes fdecls smtterms = do
  let -- all types occurring in function declarations and variable types:
      alltypes = concatMap typesOfFunc fdecls ++ map snd vartypes
      alltcons = foldr union [] (map tconsOfTypeExpr alltypes)
      -- all sorts occurring in SMT terms:
      allsorts = concatMap sortIdsOfSort (concatMap sortsOfTerm smtterms)
      (pretypes,usertypes) = partition ((== "Prelude") . fst) alltcons
      presorts = nub (filter (`notElem` (map tcons2SMT pretypes)) allsorts) ++
                 map tcons2SMT pretypes
  vst <- readIORef vstref
  let udecls = map (maybe (error "Internal error: some datatype not found!") id)
                   (map (tdeclOf vst) usertypes)
  return $ concatMap preludeSort2SMT presorts ++
           [ EmptyLine ] ++
           (if null udecls
              then []
              else [ Comment "User-defined datatypes:" ] ++
                   map tdecl2SMT udecls)

-- Calls the SMT solver (with a timeout of 2secs) on a given SMTLIB script.
-- Returns `Just` the SMT script if the result is `unsat`, otherwise `Nothing`.
callSMT :: Options -> String -> IO (Maybe String)
callSMT opts smtinput = do
  printWhenIntermediate opts $ "SMT SCRIPT:\n" ++ showWithLineNums smtinput
  printWhenIntermediate opts $ "CALLING Z3..."
  (ecode,out,err) <- evalCmd "z3" ["-smt2", "-in", "-T:2"] smtinput
  when (ecode>0) $ do printWhenIntermediate opts $ "EXIT CODE: " ++ show ecode
                      writeFile "error.smt" smtinput
  printWhenIntermediate opts $ "RESULT:\n" ++ out
  unless (null err) $ printWhenIntermediate opts $ "ERROR:\n" ++ err
  let unsat = let ls = lines out in not (null ls) && head ls == "unsat"
  return $ if unsat
             then Just $ "; proved by: z3 -smt2 <SMTFILE>\n\n" ++ smtinput
             else Nothing

-- Translate a term w.r.t. non-determinism information by
-- adding fresh `Choice` variable arguments to non-deterministic operations.
-- The fresh variable index is passed as a state.
nondetTrans :: [(QName,Bool)] -> Int -> Term -> (Term,Int)
nondetTrans ndinfo ix trm = case trm of
  TConst _ -> (trm,ix)
  TSVar  _ -> (trm,ix)
  TComb f args -> let (targs,i1) = nondetTransL ndinfo ix args
                  in if maybe False
                              (\qn -> maybe False id (lookup qn ndinfo))
                              (untransOpName (qidName f))
                       then (TComb (addChoiceType f) (TSVar i1 : targs), i1+1)
                       else (TComb f targs, i1)
  Forall vs arg -> let (targ,ix1) = nondetTrans ndinfo ix arg
                   in (Forall vs targ, ix1)
  Exists vs arg -> let (targ,ix1) = nondetTrans ndinfo ix arg
                   in (Exists vs targ, ix1)
  ESMT.Let bs e -> let (tbt,ix1) = nondetTransL ndinfo ix (map snd bs)
                       (te,ix2)  = nondetTrans ndinfo ix1 e
                   in (ESMT.Let (zip (map fst bs) tbt) te, ix2)
 where
  addChoiceType (Id n)    = Id n
  addChoiceType (As n tp) = As n (SComb "Func" [SComb "Choice" [], tp])

nondetTransL :: [(QName,Bool)] -> Int -> [Term] -> ([Term],Int)
nondetTransL _ i [] = ([],i)
nondetTransL ndinfo i (t:ts) =
  let (t1,i1) = nondetTrans ndinfo i t
      (ts1,i2) = nondetTransL ndinfo i1 ts
  in (t1:ts1, i2)

-- Operations axiomatized by specific smt scripts (no longer necessary
-- since these scripts are now automatically generated by Curry2SMT.funcs2SMT).
-- However, for future work, it might be reasonable to cache these scripts
-- for faster contract checking.
axiomatizedOps :: [String]
axiomatizedOps = ["Prelude_null","Prelude_take","Prelude_length"]

---------------------------------------------------------------------------
-- Translate a typed variables to an SMT declaration:
typedVar2SMT :: (Int,TypeExpr) -> Command
typedVar2SMT (i,te) = DeclareVar (SV i (polytype2sort te))

-- Gets all type constructors of a type expression.
tconsOfTypeExpr :: TypeExpr -> [QName]
tconsOfTypeExpr (TVar _) = []
tconsOfTypeExpr (FuncType a b) =  union (tconsOfTypeExpr a) (tconsOfTypeExpr b)
tconsOfTypeExpr (TCons qName texps) =
  foldr union [qName] (map tconsOfTypeExpr texps)
tconsOfTypeExpr (ForallType _ te) =  tconsOfTypeExpr te

---------------------------------------------------------------------------
-- Auxiliaries:

--- Checks whether a file exists in one of the directories on the PATH.
fileInPath :: String -> IO Bool
fileInPath file = do
  path <- getEnviron "PATH"
  dirs <- return $ splitOn ":" path
  (liftIO (any id)) $ mapM (doesFileExist . (</> file)) dirs

-- Shows a qualified name by replacing all dots by underscores.
showQNameNoDots :: QName -> String
showQNameNoDots = map (\c -> if c=='.' then '_' else c) . showQName

--- Shows a text with line numbers preceded:
showWithLineNums :: String -> String
showWithLineNums txt =
  let txtlines  = lines txt
      maxlog    = ilog (length txtlines + 1)
      showNum n = (take (maxlog - ilog n) (repeat ' ')) ++ show n ++ ": "
  in unlines . map (uncurry (++)) . zip (map showNum [1..]) $ txtlines

---------------------------------------------------------------------------
