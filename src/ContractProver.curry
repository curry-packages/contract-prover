---------------------------------------------------------------------------
--- A tool to prove pre- or postconditions via an SMT solver (Z3)
--- and to remove the statically proven conditions from a program.
---
--- @author  Michael Hanus
--- @version July 2024
---------------------------------------------------------------------------
-- A few things to be done to improve contract checking:
--
-- * eta-expand pre- and postconditions (before contract checking)
--   in order to generate correct SMT formulas
---------------------------------------------------------------------------

module ContractProver where

import Control.Monad      ( unless, when )
import Data.IORef
import Data.List          ( elemIndex, find, init, maximum, minimum, nub
                          , partition, splitOn, union )
import Data.Maybe         ( catMaybes, isJust )
import System.Environment ( getArgs, getEnv )

-- Imports from dependencies:
import Contract.Names
import Contract.Usage                    ( checkContractUsage )
import Control.Monad.Trans.Class         ( lift )
import Control.Monad.Trans.State         ( StateT, get, put, evalStateT )
import System.FilePath                   ( (</>) )
import FlatCurry.Files
import FlatCurry.Types
import qualified FlatCurry.Goodies as FCG
import FlatCurry.Annotated.Goodies
import FlatCurry.Annotated.Types
import FlatCurry.TypeAnnotated.Files     ( readTypeAnnotatedFlatCurry
                                         , typeAnnotatedFlatCurryFileName 
                                         , writeTypeAnnotatedFlatCurryFile )
import FlatCurry.TypeAnnotated.TypeSubst ( substRule )
import FlatCurry.ShowIntMod              ( showCurryModule )
import System.CurryPath                  ( runModuleActionQuiet )
import System.Directory                  ( doesFileExist )
import System.IOExts                     ( evalCmd )
import System.Process                    ( exitWith, system )

-- Imports from package modules:
import ESMT
import Curry2SMT
import FlatCurry.Typed.Build
import FlatCurry.Typed.Read
import FlatCurry.Typed.Goodies
import FlatCurry.Typed.Names
import FlatCurry.Typed.Simplify ( simpProg, simpFuncDecl, simpExpr )
import FlatCurry.Typed.Types
import PackageConfig            ( packagePath )
import ToolOptions
import VerifierState

------------------------------------------------------------------------

banner :: String
banner = unlines [bannerLine, bannerText, bannerLine]
 where
  bannerText = "Contract Checking/Verification Tool (Version of 15/07/24)"
  bannerLine = take (length bannerText) (repeat '=')

-- Path name of the module with auxiliary operations for contract checking.
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
    when (optTAFCY opts) $
      writeTransformedTAFCY opts (typeAnnotatedFlatCurryFileName mname) prog3
  printWhenStatus opts (showStats vst2)
 where
  line = take 78 (repeat '-')

-- Writes the transformed FlatCurry program together with the contents
-- of the auxiliary `contractCheckerModule`.
writeTransformedFCY :: Options -> String -> Prog -> IO ()
writeTransformedFCY opts progfile prog = do
  ccprog <- runModuleActionQuiet readFlatCurry contractCheckerModule
  let rnmccprog = FCG.rnmProg (FCG.progName prog) ccprog
      ccimps    = FCG.progImports rnmccprog
      ccfuncs   = FCG.progFuncs rnmccprog
  writeFCY progfile
           (FCG.updProgFuncs (++ ccfuncs)
                             (FCG.updProgImports (`union` ccimps) prog))
  printWhenStatus opts $ "Transformed program written to: " ++ progfile

-- Writes the transformed type-annotated FlatCurry program
-- together with the contents of the auxiliary `contractCheckerModule`.
writeTransformedTAFCY :: Options -> String -> TAProg -> IO ()
writeTransformedTAFCY opts progfile prog = do
  ccprog <- runModuleActionQuiet readTypeAnnotatedFlatCurry
                                 contractCheckerModule
  let rnmccprog = rnmProg (progName prog) ccprog
      ccimps    = progImports rnmccprog
      ccfuncs   = progFuncs rnmccprog
  writeTypeAnnotatedFlatCurryFile progfile
     (updProgFuncs (++ ccfuncs)
                   (updProgImports (`union` ccimps) prog))
  printWhenStatus opts $ "Transformed program written to: " ++ progfile

---------------------------------------------------------------------------
-- The state of the transformation process contains
-- * the current assertion
-- * a fresh variable index
-- * a list of all introduced variables and their types:
data TransState = TransState
  { cAssertion :: Term
  , freshVar   :: Int
  , varTypes   :: [(Int,TypeExpr)]
  }

makeTransState :: Int -> [(Int,TypeExpr)] -> TransState
makeTransState = TransState tTrue

emptyTransState :: TransState
emptyTransState = makeTransState 0 []

-- The type of the state monad contains the transformation state.
--type TransStateM a = State TransState a
type TransStateM a = StateT TransState IO a

-- Gets the current fresh variable index of the state.
getFreshVarIndex :: TransStateM Int
getFreshVarIndex = get >>= return . freshVar

-- Sets the fresh variable index in the state.
setFreshVarIndex :: Int -> TransStateM ()
setFreshVarIndex fvi = do
  st <- get
  put $ st { freshVar = fvi }

-- Gets a fresh variable index and increment the index in the state.
getFreshVar :: TransStateM Int
getFreshVar = do
  st <- get
  put $ st { freshVar = freshVar st + 1 }
  return $ freshVar st

-- Gets the variables and their types stored in the state.
getVarTypes :: TransStateM [(Int,TypeExpr)]
getVarTypes = get >>= return . varTypes

-- Adds variables and their types to the state.
addVarTypes :: [(Int,TypeExpr)] -> TransStateM ()
addVarTypes vts = do
  st <- get
  put $ st { varTypes = vts ++ varTypes st }

-- Gets the current assertion stored in the state.
getAssertion :: TransStateM Term
getAssertion = get >>= return . cAssertion

-- Sets the current assertion in the state.
setAssertion :: Term -> TransStateM ()
setAssertion formula = do
  st <- get
  put $ st { cAssertion = formula }

-- Add a formula to the current assertion in the state by conjunction.
addToAssertion :: Term -> TransStateM ()
addToAssertion formula = do
  st <- get
  put $ st { cAssertion = tConj [cAssertion st, formula] }

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
    , string2TAFCY fn
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
    , string2TAFCY fn
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
      st = makeTransState (maximum (0 : map fst rargs ++ allVars rhs) + 1) rargs
  (flip evalStateT) st $ do
    -- compute precondition of operation:
    precondformula <- preCondExpOf ti qn targs
    setAssertion precondformula
    newrhs <- optPreCondInExp rhs
    return (ARule rty rargs newrhs)
 where
  optPreCondInExp exp = case exp of
    AComb ty ct (qf,tys) args ->
      if qf == ("Prelude","?") && length args == 2
        then optPreCondInExp (AOr ty (args!!0) (args!!1))
        else do
          precond <- getAssertion
          nargs <- mapM optPreCondInExp args
          if toPreCondQName qf `elem` map funcName (preConds ti)
            then do
              lift $ printWhenIntermediate opts $ "Checking call to " ++ snd qf
              (bs,_)   <- normalizeArgs nargs
              bindexps <- mapM (binding2SMT True ti) bs
              precondcall <- preCondExpOf ti qf
                               (zip (map fst bs) (map annExpr args))
              -- TODO: select from 'bindexps' only demanded argument positions
              let title = "SMT script to verify precondition of '" ++ snd qf ++
                          "' in function '" ++ fn ++ "'"
              vartypes <- getVarTypes
              pcproof <- lift $
                checkImplication opts vstref title vartypes
                                 precond (tConj bindexps) precondcall
              let pcvalid = isJust pcproof
              lift $ modifyIORef vstref
                       (addPreCondToStats (snd qf ++ "("++fn++")") pcvalid)
              if pcvalid
                then do
                  lift $ printWhenStatus opts $
                          fn ++ ": PRECONDITION OF '" ++ snd qf ++ "': VERIFIED"
                  return $ AComb ty ct (toNoCheckQName qf, tys) nargs
                else do
                  lift $ printWhenStatus opts $
                           fn ++ ": PRECOND CHECK ADDED TO '" ++ snd qf ++ "'"
                  return $ AComb ty ct (qf,tys) nargs
            else return $ AComb ty ct (qf,tys) nargs
    ACase ty ct e brs -> do
      ne <- optPreCondInExp e
      freshvar <- getFreshVar
      be <- binding2SMT True ti (freshvar,ne)
      addToAssertion be
      addVarTypes [ (freshvar, annExpr ne) ]
      nbrs <- mapM (optPreCondInBranch freshvar) brs
      return $ ACase ty ct ne nbrs
    AOr ty e1 e2 -> do
      ne1 <- optPreCondInExp e1
      ne2 <- optPreCondInExp e2
      return $ AOr ty ne1 ne2
    ALet ty bs e -> do
      nes <- mapM optPreCondInExp (map snd bs)
      ne  <- optPreCondInExp e
      return $ ALet ty (zip (map fst bs) nes) ne
    AFree ty fvs e -> do
      ne <- optPreCondInExp e
      return $ AFree ty fvs ne
    ATyped ty e et -> do
      ne <- optPreCondInExp e
      return $ ATyped ty ne et
    _ -> return exp

  optPreCondInBranch dvar branch = do
    ABranch p e <- renamePatternVars branch
    addToAssertion (tEquVar dvar (pat2SMT p))
    ne <- optPreCondInExp e
    return (ABranch p ne)

-- Rename argument variables of constructor pattern
renamePatternVars :: TABranchExpr -> TransStateM TABranchExpr
renamePatternVars (ABranch p e) =
  if isConsPattern p
    then do
      fv <- getFreshVarIndex
      let args = map fst (patArgs p)
          minarg = minimum (0 : args)
          maxarg = maximum (0 : args)
          rnm i = if i `elem` args then i - minarg + fv else i
          nargs = map (\ (v,t) -> (rnm v,t)) (patArgs p)
      setFreshVarIndex (fv + maxarg - minarg + 1)
      addVarTypes nargs
      return $ ABranch (updPatArgs (map (\ (v,t) -> (rnm v,t))) p)
                       (rnmAllVars rnm e)
    else return $ ABranch p e

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
  maybe (do putStrLn $ "Postcondition: " ++ pcname ++ "\n" ++
                       "Operation of this postcondition not found!"
            return allfuns)
        --(\checkfun -> provePC checkfun) --TODO: simplify definition
        (\checkfun -> evalStateT (provePC (simpFuncDecl checkfun))
                                 emptyTransState)
        (find (\fd -> toPostCondName (snd (funcName fd)) ==
                      decodeContractName pcname)
              allfuns)
 where
  pcname = snd (funcName postfun)

  provePC checkfun = do
    let (postmn,postfn) = funcName postfun
        mainfunc        = snd (funcName checkfun)
        orgqn           = (postmn, reverse (drop 5 (reverse postfn)))
    -- lift $ putStrLn $ "Check postcondition of operation " ++ mainfunc
    let farity = funcArity checkfun
        ftype  = funcType checkfun
        targsr = zip [1..] (argTypes ftype ++ [resultType ftype])
    bodyformula     <- extractPostConditionProofObligation ti
                         [1 .. farity] (farity+1) (funcRule checkfun)
    precondformula  <- preCondExpOf ti orgqn (init targsr)
    postcondformula <- applyFunc postfun targsr >>= pred2smt
    let title = "verify postcondition of '" ++ mainfunc ++ "'..."
    lift $ printWhenIntermediate opts $ "Trying to " ++ title
    vartypes <- getVarTypes
    pcproof <- lift $
      checkImplication opts vstref ("SMT script to " ++ title) vartypes
                       (tConj [precondformula, bodyformula])
                       tTrue postcondformula
    lift $ modifyIORef vstref (addPostCondToStats mainfunc (isJust pcproof))
    maybe
      (do lift $ (printWhenStatus opts $ mainfunc ++ ": POSTCOND CHECK ADDED")
          return (map (addPostConditionTo (funcName postfun)) allfuns) )
      (\proof -> do
         unless (optNoProof opts) $ lift $
           writeFile ("PROOF_" ++ showQNameNoDots orgqn ++ "_" ++
                      "SatisfiesPostCondition.smt") proof
         lift $ printWhenStatus opts $ mainfunc ++ ": POSTCONDITION VERIFIED"
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
                                    -> TransStateM Term
extractPostConditionProofObligation _ _ _ (AExternal _ s) =
  return $ tComb ("External: " ++ s) []
extractPostConditionProofObligation ti args resvar
                                    (ARule ty orgargs orgexp) = do
  let exp    = rnmAllVars renameRuleVar orgexp
      rtype  = resType (length orgargs) (stripForall ty)
  put $ makeTransState (maximum (resvar : allVars exp) + 1)
                       ((resvar, rtype) : zip args (map snd orgargs))
  binding2SMT True ti (resvar,exp)
 where
  maxArgResult = maximum (resvar : args)
  renameRuleVar r = maybe (r + maxArgResult + 1)
                          (args!!)
                          (elemIndex r (map fst orgargs))

  resType n te =
    if n==0
      then te
      else case te of
             FuncType _ rt -> resType (n-1) rt
             _             -> error $ "Internal errror: resType: " ++ show te

-- Returns the precondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding the `freshvar` index to them.
preCondExpOf :: VerifyInfo -> QName -> [(Int,TypeExpr)] -> TransStateM Term
preCondExpOf ti qf args =
  maybe (return tTrue)
        (\fd -> applyFunc fd args >>= pred2smt)
        (find (\fd -> decodeContractQName (funcName fd)
                        == toPreCondQName (fromNoCheckQName qf))
              (preConds ti))

-- Returns the postcondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding `freshvar` to them and
-- return the new freshvar value.
postCondExpOf :: VerifyInfo -> QName -> [(Int,TypeExpr)] -> TransStateM Term
postCondExpOf ti qf args =
  maybe (return tTrue)
        (\fd -> applyFunc fd args >>= pred2smt)
        (find (\fd -> decodeContractQName (funcName fd)
                        == toPostCondQName (fromNoCheckQName qf))
              (postConds ti))

-- Applies a function declaration on a list of arguments,
-- which are assumed to be variable indices, and returns
-- the renamed body of the function declaration.
-- All local variables are renamed by adding `freshvar` to them.
-- Also the new fresh variable index is returned.
applyFunc :: TAFuncDecl -> [(Int,TypeExpr)] -> TransStateM TAExpr
applyFunc fdecl targs = do
  fv <- getFreshVarIndex
  let tsub = maybe (error $ "applyFunc: types\n" ++
                            show (argTypes (funcType fdecl)) ++ "\n" ++
                            show (map snd targs) ++ "\ndo not match!")
                   id
                   (matchTypes (argTypes (funcType fdecl)) (map snd targs))
      (ARule _ orgargs orgexp) = substRule tsub (funcRule fdecl)
      exp = rnmAllVars (renameRuleVar fv orgargs) orgexp
  setFreshVarIndex (max fv (maximum (0 : args ++ allVars exp) + 1))
  return $ simpExpr $ applyArgs exp (drop (length orgargs) args)
 where
  args = map fst targs
  -- renaming function for variables in original rule:
  renameRuleVar fv orgargs r = maybe (r + fv)
                                     (args!!)
                                     (elemIndex r (map fst orgargs))

  applyArgs e [] = e
  applyArgs e (v:vs) =
    -- simple hack for eta-expansion since the type annotations are not used:
    let e_v =  AComb failed FuncCall
                     (pre "apply", failed) [e, AVar failed v]
    in applyArgs e_v vs

-- Translates a Boolean FlatCurry expression into an SMT formula.
pred2smt :: TAExpr -> TransStateM Term
pred2smt exp = case exp of
  AVar _ i              -> return (TSVar i)
  ALit _ l              -> return (lit2SMT l)
  AComb _ ct (qf,ftype) args ->
    if qf == pre "not" && length args == 1
      then do barg <- pred2smt (head args)
              return (tNot barg)
      else do bargs <- mapM pred2smt args
              return (TComb (cons2SMT (ct /= ConsCall || not (null bargs))
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
binding2SMT :: Bool -> VerifyInfo -> (Int,TAExpr) -> TransStateM Term
binding2SMT odemanded vi (oresvar,oexp) =
  exp2smt odemanded (oresvar, simpExpr oexp)
 where
  exp2smt demanded (resvar,exp) = case exp of
    AVar _ i -> return $ if resvar==i then tTrue
                                       else tEquVar resvar (TSVar i)
    ALit _ l -> return (tEquVar resvar (lit2SMT l))
    AComb ty ct (qf,_) args ->
      if qf == pre "?" && length args == 2
        then exp2smt demanded (resvar, AOr ty (args!!0) (args!!1))
        else do
          (bs,nargs) <- normalizeArgs args
          -- TODO: select from 'bindexps' only demanded argument positions
          bindexps <- mapM (exp2smt (isPrimOp qf || optStrict (toolOpts vi))) bs
          comb2smt qf ty ct nargs bs bindexps
    ALet _ bs e -> do
      addVarTypes (map fst bs)
      bindexps <- mapM (exp2smt False) (map (\ ((i,_),ae) -> (i,ae)) bs)
      bexp <- exp2smt demanded (resvar,e)
      return (tConj (bindexps ++ [bexp]))
    AOr _ e1 e2  -> do
      bexp1 <- exp2smt demanded (resvar,e1)
      bexp2 <- exp2smt demanded (resvar,e2)
      return (tDisj [bexp1, bexp2])
    ACase _ _ e brs   -> do
      freshvar <- getFreshVar
      addVarTypes [(freshvar, annExpr e)]
      argbexp <- exp2smt demanded (freshvar,e)
      bbrs    <- mapM branch2smt (map (\b -> (freshvar,b)) brs)
      return (tConj [argbexp, tDisj bbrs])
    ATyped _ e _ -> exp2smt demanded (resvar,e)
    AFree _ _ _ -> error "Free variables not yet supported!"
   where
    comb2smt qf rtype ct nargs bs bindexps
     | qf == pre "otherwise"
       -- specific handling for the moment since the front end inserts it
       -- as the last alternative of guarded rules...
     = return (tEquVar resvar tTrue)
     | ct == ConsCall -- translate data constructor
     = return (tConj (bindexps ++
                      [tEquVar resvar
                               (TComb (cons2SMT (null nargs) False qf rtype)
                                      (map arg2smt nargs))]))
     | qf == pre "apply"
     = -- cannot translate h.o. apply: ignore it
       return tTrue
     | isPrimOp qf
     = return (tConj (bindexps ++
                      [tEquVar resvar (TComb (cons2SMT True False qf rtype)
                                             (map arg2smt nargs))]))
     | otherwise -- non-primitive operation: add contract only if demanded
     = do let targs = zip (map fst bs) (map annExpr nargs)
          precond  <- preCondExpOf vi qf targs
          postcond <- postCondExpOf vi qf (targs ++ [(resvar,rtype)])
          return
            (tConj (bindexps ++ if demanded then [precond,postcond] else []))
    
    branch2smt (cvar, (ABranch p e)) = do
      branchbexp <- exp2smt demanded (resvar,e)
      addVarTypes patvars
      return (tConj [ tEquVar cvar (pat2SMT p), branchbexp])
     where
      patvars = if isConsPattern p
                  then patArgs p
                  else []
  
    arg2smt e = case e of AVar _ i -> TSVar i
                          ALit _ l -> lit2SMT l
                          _        -> error $ "Not normalized: " ++ show e

normalizeArgs :: [TAExpr] -> TransStateM ([(Int,TAExpr)],[TAExpr])
normalizeArgs [] = return ([],[])
normalizeArgs (e:es) = case e of
  AVar _ i -> do (bs,nes) <- normalizeArgs es
                 return ((i,e):bs, e:nes)
  _        -> do fvar <- getFreshVar
                 addVarTypes [(fvar,annExpr e)]
                 (bs,nes) <- normalizeArgs es
                 return ((fvar,e):bs, AVar (annExpr e) fvar : nes)


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
  (ecode,out,err) <- evalCmd "z3"
                             ["-smt2", "-in", "-T:" ++ show (optTimeout opts)]
                             smtinput
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
  path <- getEnv "PATH"
  dirs <- return $ splitOn ":" path
  (fmap (any id)) $ mapM (doesFileExist . (</> file)) dirs

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
--- The value of `ilog n` is the floor of the logarithm
--- in the base 10 of `n`.
--- Fails if `n &lt;= 0`.
--- For positive integers, the returned value is
--- 1 less the number of digits in the decimal representation of `n`.
---
--- @param n - The argument.
--- @return the floor of the logarithm in the base 10 of `n`.
ilog :: Int -> Int
ilog n | n>0 = if n<10 then 0 else 1 + ilog (n `div` 10)
