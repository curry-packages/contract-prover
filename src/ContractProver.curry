---------------------------------------------------------------------------
--- A tool to prove pre- or postconditions via an SMT solver (Z3)
--- and to remove the statically proven conditions from a program.
---
--- @author  Michael Hanus
--- @version September 2017
---------------------------------------------------------------------------

module ContractProver where

import Directory    ( doesFileExist )
import Distribution ( stripCurrySuffix )
import FilePath     ( (</>) )
import FlatCurry.Files
import FlatCurry.Types
import IOExts
import List         ( deleteBy, elemIndex, find, intersect, isSuffixOf
                    , maximum, minimum, splitOn )
import Maybe        ( catMaybes )
import Pretty       ( pPrint )
import State
import System       ( getArgs, getEnviron, system )
import Unsafe

-- Imports from dependencies:
import FlatCurry.Annotated.Goodies
import FlatCurry.Annotated.Pretty        ( ppProg )
import FlatCurry.Annotated.Types
import ShowFlatCurry                     ( showCurryModule )

-- Imports from package modules:
import BoolExp
import Curry2SMT
import PackageConfig ( packagePath )
import ProverOptions

-- Just for testing:
m :: IO ()
m = mf "Fac"

mf :: String -> IO ()
mf p = do
  system $ "rm -f .curry/" ++ p ++ ".fcy"
  eliminateContracts defaultOptions { optVerb = 2 } p

------------------------------------------------------------------------

banner :: String
banner = unlines [bannerLine,bannerText,bannerLine]
 where
   bannerText = "Contract Optimization Tool (Version of 20/07/17)"
   bannerLine = take (length bannerText) (repeat '=')

---------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  (opts,progs) <- processOptions banner args
  z3exists <- fileInPath "z3"
  if z3exists
    then do
      when (optVerb opts > 0) $ putStrLn banner
      mapIO_ (eliminateContracts opts) progs
    else do
      putStrLn "CONTRACT VERIFICATION SKIPPED:"
      putStrLn "The SMT solver Z3 is required for the contract prover to work"
      putStrLn "but the program 'z3' is not found on the PATH!"

-- Optimize a module by proving its contracts:
eliminateContracts :: Options -> String -> IO ()
eliminateContracts opts mainmodname = do
  prog <- readTypedFlatCurry mainmodname
  eliminateContractsInProg opts prog

eliminateContractsInProg :: Options -> TAProg ->  IO ()
eliminateContractsInProg opts prog = do
  printWhenAll opts $ unlines $
    ["ORIGINAL PROGRAM:", line, showCurryModule (unAnnProg prog), line]
  (postoptprog,stats1) <- eliminatePostConditions opts
                            (makeTransInfo (progFuncs prog)) prog initStats
  (newprog,stats2) <- eliminatePreConditions opts
                        (makeTransInfo (progFuncs postoptprog))
                        postoptprog stats1
  let unewprog = unAnnProg newprog
  printWhenAll opts $ unlines $
    ["TRANSFORMED PROGRAM:", line, showCurryModule unewprog, line]
  --printWhenAll opts $ pPrint $ ppProg newprog
  when (optReplace opts && isOptimized stats2) $ do
    let newprogname = flatCurryFileName (progName newprog)
    writeFCY newprogname unewprog
    printWhenStatus opts $ "Optimized programm written to: " ++ newprogname
  printWhenStatus opts (showStats stats2)
 where
  line = take 78 (repeat '-')

---------------------------------------------------------------------------

printWhenStatus :: Options -> String -> IO ()
printWhenStatus opts s =
  when (optVerb opts > 0) (printCP s)

printWhenIntermediate :: Options -> String -> IO ()
printWhenIntermediate opts s =
  when (optVerb opts > 1) (printCP s)

printWhenAll :: Options -> String -> IO ()
printWhenAll opts s =
 when (optVerb opts > 2) (printCP s)

printCP :: String -> IO ()
printCP s = putStrLn $ "CONTRACT PROVER: " ++ s

---------------------------------------------------------------------------
-- Suffix of operation without precondition check:
woPreCondSuffix :: String
woPreCondSuffix = "'WithoutPreCondCheck"

dropWoPreCondSuffix :: QName -> QName
dropWoPreCondSuffix (mn,fn) =
  (mn, reverse (drop (length woPreCondSuffix) (reverse fn)))

-- Suffix of operation without postcondition check:
woPostCondSuffix :: String
woPostCondSuffix = "'WithoutPostCondCheck"

dropWoPostCondSuffix :: QName -> QName
dropWoPostCondSuffix (mn,fn) =
  (mn, reverse (drop (length woPostCondSuffix) (reverse fn)))

--- Returns the original name (i.e., without possible xxxCondCheck suffix) of
--- a qualified function name.
orgNameOf :: QName -> QName
orgNameOf qn =
  if woPostCondSuffix `isSuffixOf` (snd qn)
    then orgNameOf (dropWoPostCondSuffix qn)
    else if woPreCondSuffix `isSuffixOf` (snd qn)
           then dropWoPreCondSuffix qn
           else qn

---------------------------------------------------------------------------
-- Some global information used by the transformation process:
data TransInfo = TransInfo
  { allFuns       :: [TAFuncDecl] -- all defined operations
  , preConds      :: [TAFuncDecl] -- all precondition operations
  , postConds     :: [TAFuncDecl] -- all postcondition operations
  , woPreCondFuns :: [TAFuncDecl] -- all operations without precond checking
  }

makeTransInfo :: [TAFuncDecl] -> TransInfo
makeTransInfo fdecls = TransInfo fdecls preconds postconds woprefuns
 where
  -- Precondition operations:
  preconds  = filter (\fd -> "'pre"  `isSuffixOf` snd (funcName fd)) fdecls
  -- Postcondition operations:
  postconds = filter (\fd -> "'post" `isSuffixOf` snd (funcName fd)) fdecls
  -- Operations without precondition checks:
  woprefuns = filter (\fd -> woPreCondSuffix `isSuffixOf` snd (funcName fd))
                     fdecls

---------------------------------------------------------------------------
-- The state of the transformation process contains
-- * the current assertion
-- * a fresh variable index
-- * a list of all introduced variables and their types:
data TransState = TransState
  { preCond    :: BoolExp
  , freshVar   :: Int
  , varTypes   :: [(Int,TypeExpr)]
  }

makeTransState :: Int -> [(Int,TypeExpr)] -> TransState
makeTransState = TransState bTrue

-- Increments fresh variable index.
incFreshVarIndex :: TransState -> TransState
incFreshVarIndex st = st { freshVar = freshVar st + 1 }

-- Adds variables to the state.
addVarTypes :: [(Int,TypeExpr)] -> TransState -> TransState
addVarTypes vts st = st { varTypes = vts ++ varTypes st }

---------------------------------------------------------------------------
-- Statistical information of the transformation process:
-- all preconds / removed preconds / all postconds / removed postconds
data Statistics = Statistics Int Int Int Int

initStats :: Statistics
initStats = Statistics 0 0 0 0

--- Shows the statistics in human-readable format.
showStats :: Statistics -> String
showStats (Statistics allpre rmpre allpost rmpost) =
  "\nRemoved preconditions : " ++ show rmpre ++ " of " ++ show allpre ++
  " / Removed postconditions: " ++ show rmpost ++ " of " ++ show allpost ++
  (if allpre==rmpre && allpost==rmpost then "\nALL CONTRACTS VERIFIED!" else "")

--- Was there some optimization of a contract?
isOptimized :: Statistics -> Bool
isOptimized (Statistics _ rmpre _ rmpost) = rmpre>0 || rmpost>0

--- Increments the number of preconditions. If the first argument is true,
--- a precondition has been removed.
incPreCond :: Bool -> Statistics -> Statistics
incPreCond removed (Statistics allpre rmpre allpost rmpost) =
  Statistics (allpre+1) (rmpre + if removed then 1 else 0) allpost rmpost

--- Increments the number of postconditions. If the first argument is true,
--- a postcondition has been removed.
incPostCond :: Bool -> Statistics -> Statistics
incPostCond removed (Statistics allpre rmpre allpost rmpost) =
  Statistics allpre rmpre (allpost+1) (rmpost + if removed then 1 else 0)

---------------------------------------------------------------------------
-- Eliminate possible preconditions checks:
-- If an operation `f` occurring in a right-hand side has
-- a precondition check, a proof for the validity of the precondition
-- is extracted and, if the proof is successful, the operation without
-- the precondtion check `f'WithoutPreCondCheck` is called instead.
eliminatePreConditions :: Options -> TransInfo -> TAProg -> Statistics
                       -> IO (TAProg,Statistics)
eliminatePreConditions opts ti prog stats = do
  statsref <- newIORef stats
  newfuns  <- mapIO (provePreCondition opts ti statsref) (progFuncs prog)
  nstats   <- readIORef statsref
  return (updProgFuncs (const newfuns) prog, nstats)

provePreCondition :: Options -> TransInfo -> IORef Statistics -> TAFuncDecl
                  -> IO TAFuncDecl
provePreCondition opts ti statsref fdecl = do
  printWhenIntermediate opts $
    "Operation to be optimized: " ++ snd (funcName fdecl)
  newrule <- optPreConditionInRule opts ti (funcName fdecl)
                                           (funcRule fdecl) statsref
  return (updFuncRule (const newrule) fdecl)

optPreConditionInRule :: Options -> TransInfo -> QName -> TARule
                      -> IORef Statistics -> IO TARule
optPreConditionInRule _ _ _ rl@(AExternal _ _) _ = return rl
optPreConditionInRule opts ti (mn,fn) (ARule rty rargs rhs) statsref = do
  let farity = length rargs
      orgqn = if woPreCondSuffix `isSuffixOf` fn
                then dropWoPreCondSuffix (mn,fn)
                else (mn,fn)
      -- compute precondition of operation:
      s0 = makeTransState (maximum (0 : map fst rargs ++ allVars rhs) + 1) rargs
      (precondformula,s1)  = preCondExpOf ti orgqn [1..farity] s0
      s2 = s1 { preCond = precondformula }
  newrhs <- optPreCondInExp s2 rhs
  return (ARule rty rargs newrhs)
 where
  optPreCondInExp pts exp = case exp of
    AComb ty ct (qf,tys) args ->
      if qf == ("Prelude","?") && length args == 2
        then optPreCondInExp pts (AOr ty (args!!0) (args!!1))
        else do
          nargs <- mapIO (optPreCondInExp pts) args
          if addSuffix qf "'pre" `elem` map funcName (preConds ti) &&
             addSuffix qf woPreCondSuffix `elem` map funcName (woPreCondFuns ti)
            then do
              printWhenIntermediate opts $ "Optimizing call to " ++ snd qf
              let ((bs,_)     ,pts1) = normalizeArgs nargs pts
                  (bindexps   ,pts2) = mapS (exp2bool ti) bs pts1
                  (precondcall,pts3) = preCondExpOf ti qf (map fst bs) pts2
              -- TODO: select from 'bindexps' the demanded argument positions
              pcvalid <- checkImplicationWithSMT opts (varTypes pts3)
                           (preCond pts) (Conj bindexps) precondcall
              modifyIORef statsref (incPreCond pcvalid)
              if pcvalid
                then do
                  printWhenStatus opts $
                    fn ++ ": PRECOND CHECK OF '" ++ snd qf ++ "': REMOVED"
                  return $ AComb ty ct (addSuffix qf woPreCondSuffix, tys) nargs
                else do
                  printWhenStatus opts $
                    fn ++ ": PRECOND CHECK OF '" ++ snd qf ++ "': unchanged"
                  return $ AComb ty ct (qf,tys) nargs
            else return $ AComb ty ct (qf,tys) nargs
    ACase ty ct e brs -> do
      ne <- optPreCondInExp pts e
      let freshvar = freshVar pts
          (be,pts1) = exp2bool ti (freshvar,ne) (incFreshVarIndex pts)
          pts2 = pts1 { preCond = Conj [preCond pts, be]
                      , varTypes = (freshvar,annExpr ne) : varTypes pts1 }
      nbrs <- mapIO (optPreCondInBranch pts2 freshvar) brs
      return $ ACase ty ct ne nbrs
    AOr ty e1 e2 -> do
      ne1 <- optPreCondInExp pts e1
      ne2 <- optPreCondInExp pts e2
      return $ AOr ty ne1 ne2
    ALet ty bs e -> do
      nes <- mapIO (optPreCondInExp pts) (map snd bs)
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
    let npts = pts1 { preCond = Conj [preCond pts1, bEquVar dvar (pat2bool p)] }
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
-- Eliminate possible postconditions checks:
-- If an operation `f` has a postcondition check (inserted by currypp),
-- a proof for the validity of the postcondition is extracted and,
-- if the proof is successful, the operation `f'WithoutPostCondCheck`
-- is deleted and the code of `f` is replaced by the code of the
-- operation `f'WithoutPostCondCheck`.
eliminatePostConditions :: Options -> TransInfo -> TAProg -> Statistics
                        -> IO (TAProg,Statistics)
eliminatePostConditions opts ti prog stats = do
  -- Operations with postcondition checks:
  let fdecls = progFuncs prog
      postfuns = filter (\fd -> woPostCondSuffix `isSuffixOf` snd (funcName fd))
                        fdecls
  (newfuns,nstats) <- provePostConds postfuns (fdecls,stats)
  return $ (updProgFuncs (const newfuns) prog, nstats)
 where
  provePostConds []         (fdecls,sts) = return (fdecls,sts)
  provePostConds (pof:pofs) (fdecls,sts) =
    provePostCondition opts ti pof fdecls sts >>= provePostConds pofs

provePostCondition :: Options -> TransInfo -> TAFuncDecl -> [TAFuncDecl]
                   -> Statistics -> IO ([TAFuncDecl],Statistics)
provePostCondition opts ti wopostfun allfuns stats = do
  maybe (putStrLn ("Operation: " ++ snd (funcName wopostfun) ++ "\n" ++
                   "Operation which invokes postcondition check not found!") >>
         return (allfuns,stats))
        (\ (postfun,postcheckfun) -> provePC postfun postcheckfun)
        (findPostConditionChecker ti wopostfun)
 where
  provePC postfun postcheckfun = do
    --putStrLn $ "Operation with postcondition check:\n" ++
    --           snd (funcName postcheckfun)
    let (postmn,postfn) = funcName postfun
        orgqn           = (postmn, reverse (drop 5 (reverse postfn)))
    --putStrLn $ "Operation defining postcondition :\n" ++ postfn
    let farity = funcArity wopostfun
    let (bodyformula,s0) = extractPostConditionProofObligation ti [1..farity]
                             (farity+1) (funcRule wopostfun)
        (precondformula,s1)  = preCondExpOf ti orgqn [1..farity] s0
        (postcondformula,s2) = (applyFunc postfun [1 .. farity+1] `bindS`
                                pred2bool) s1
    pcvalid <- checkImplicationWithSMT opts (varTypes s2)
                                       (Conj [precondformula, bodyformula])
                                       bTrue postcondformula
    let nstats = incPostCond pcvalid stats
    if pcvalid
      then do printWhenStatus opts $
                snd (funcName postcheckfun) ++ ": POSTCOND CHECK REMOVED"
              let newpostcheckfun = updFuncRule (const (funcRule wopostfun))
                                                postcheckfun
              return (deleteBy (\f g -> funcName f == funcName g) wopostfun
                               (updFuncDecl newpostcheckfun allfuns), nstats)
      else do printWhenStatus opts $
                snd (funcName postcheckfun) ++ ": POSTCOND CHECK unchanged"
              return (allfuns, nstats)

-- Find the postcondition operation and the operation which invokes
-- the postcondition for a given operation without postcondition check:
findPostConditionChecker :: TransInfo -> TAFuncDecl
                         -> Maybe (TAFuncDecl,TAFuncDecl)
findPostConditionChecker ti wopostcheckfunc =
  let postchkname = dropWoPostCondSuffix (funcName wopostcheckfunc)
  in maybe Nothing
           (\pcfun -> let (ARule _ _ pcexp) = funcRule pcfun
                      in maybe Nothing
                               (\postfun -> Just (postfun,pcfun))
                               (postFuncOfPCExp pcexp))
           (find (\fd -> funcName fd == postchkname) (allFuns ti))
 where
  postFuncOfPCExp e = case e of
    AComb _ _ _ args ->
      case args!!1 of
        AComb _ _ (postname,_) _ ->
                          find (\fd -> funcName fd == postname) (allFuns ti)
        _ -> Nothing
    _ -> Nothing


extractPostConditionProofObligation :: TransInfo -> [Int] -> Int -> TARule
                                    -> (BoolExp,TransState)
extractPostConditionProofObligation _ _ _ (AExternal _ s) =
  (BTerm ("External: "++s) [], makeTransState 0 [])
extractPostConditionProofObligation ti args resvar (ARule ty orgargs orgexp) =
  let exp    = rnmAllVars renameRuleVar orgexp
      rtype  = resType (length orgargs) ty
      state0 = makeTransState (maximum (resvar : allVars exp) + 1)
                              ((resvar, rtype) : zip args (map snd orgargs))
  in exp2bool ti (resvar,exp) state0
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
preCondExpOf :: TransInfo -> QName -> [Int] -> State TransState BoolExp
preCondExpOf ti qf args =
  maybe (returnS bTrue)
        (\fd -> applyFunc fd args `bindS` pred2bool)
        (find (\fd -> funcName fd == qnpre) (preConds ti))
 where
  qnpre = addSuffix (orgNameOf qf) "'pre"

-- Returns the postcondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding `freshvar` to them and
-- return the new freshvar value.
postCondExpOf :: TransInfo -> QName -> [Int] -> State TransState BoolExp
postCondExpOf ti qf args =
  maybe (returnS bTrue)
        (\fd -> applyFunc fd args `bindS` pred2bool)
        (find (\fd -> funcName fd == qnpost) (postConds ti))
 where
  qnpost = addSuffix (orgNameOf qf) "'post"

-- Applies a function declaration on a list of arguments,
-- which are assumed to be variable indices, and returns
-- the renamed body of the function declaration.
-- All local variables are renamed by adding `freshvar` to them.
-- Also the new fresh variable index is returned.
applyFunc :: TAFuncDecl -> [Int] -> State TransState TAExpr
applyFunc fdecl args s0 =
  let (ARule _ orgargs orgexp) = funcRule fdecl
      exp = rnmAllVars (renameRuleVar orgargs) orgexp
      s1  = s0 { freshVar = max (freshVar s0)
                                   (maximum (0 : args ++ allVars exp) + 1) }
  in (exp, s1)
 where
  renameRuleVar orgargs r = maybe (r + freshVar s0)
                                  (args!!)
                                  (elemIndex r (map fst orgargs))

-- Translates a Boolean FlatCurry expression into a Boolean formula.
-- Calls to user-defined functions are replaced by the first argument
-- (which might be true or false).
pred2bool :: TAExpr -> State TransState BoolExp
pred2bool exp = case exp of
  AVar _ i              -> returnS (BVar i)
  ALit _ l              -> returnS (lit2bool l)
  AComb _ _ (qf,_) args ->
    if qf == ("Prelude","not") && length args == 1
      then pred2bool (head args) `bindS` \barg -> returnS (Not barg)
      else mapS pred2bool args `bindS` \bargs ->
           returnS (BTerm (transOpName qf) bargs)
  _     -> returnS (BTerm (show exp) [])


-- Translates an expression to a Boolean formula representing
-- the postcondition assertion by generating an equality
-- between the first argument variable and the translated expression.
-- The translated expression is normalized when necessary.
-- For this purpose, a "fresh variable index" is passed as a state.
-- Moreover, the returned state contains also the types of all fresh variables.
exp2bool :: TransInfo -> (Int,TAExpr) -> State TransState BoolExp
exp2bool ti (resvar,exp) = case exp of
  AVar _ i          -> returnS $ if resvar==i
                                   then bTrue
                                   else bEquVar resvar (BVar i)
  ALit _ l          -> returnS (bEquVar resvar (lit2bool l))
  AComb ty _ (qf,_) args ->
    if qf == ("Prelude","?") && length args == 2
      then exp2bool ti (resvar, AOr ty (args!!0) (args!!1))
      else normalizeArgs args `bindS` \ (bs,nargs) ->
           mapS (exp2bool ti) bs `bindS` \bindexps ->
           comb2bool qf nargs bs bindexps
  ALet _ bs e ->
    mapS (exp2bool ti) (map (\ ((i,_),ae) -> (i,ae)) bs) `bindS` \bindexps ->
    exp2bool ti (resvar,e) `bindS` \bexp ->
    returnS (Conj (bindexps ++ [bexp]))
  AOr _ e1 e2  ->
    exp2bool ti (resvar,e1) `bindS` \bexp1 ->
    exp2bool ti (resvar,e2) `bindS` \bexp2 ->
    returnS (Disj [bexp1, bexp2])
  ACase _ _ e brs   ->
    getS `bindS` \ts ->
    let freshvar = freshVar ts
    in putS (addVarTypes [(freshvar, annExpr e)] (incFreshVarIndex ts)) `bindS_`
       exp2bool ti (freshvar,e) `bindS` \argbexp ->
       mapS branch2bool (map (\b->(freshvar,b)) brs) `bindS` \bbrs ->
       returnS (Conj [argbexp, Disj bbrs])
  ATyped _ e _ -> exp2bool ti (resvar,e)
  AFree _ _ _ -> error "Free variables not yet supported!"
 where
   comb2bool qf nargs bs bindexps
    | isPrimOp qf
    = returnS (Conj (bindexps ++
                     [bEquVar resvar (BTerm (transOpName qf)
                                            (map arg2bool nargs))]))
    | qf == ("Prelude","otherwise")
      -- specific handling for the moment since the front end inserts it
      -- as the last alternative of guarded rules...
    = returnS (bEquVar resvar bTrue)
    | qf == ("Prelude","[]")
    = returnS (bEquVar resvar (BTerm "nil" []))
    | qf == ("Prelude",":") --&& length nargs == 2
    = returnS (Conj (bindexps ++
                     [bEquVar resvar (BTerm "insert" (map arg2bool nargs))]))
    | otherwise -- non-primitive operation: add only the contract
    = preCondExpOf ti qf (map fst bs) `bindS` \precond ->
      postCondExpOf ti qf (map fst bs ++ [resvar]) `bindS` \postcond ->
      returnS (Conj (bindexps ++ [precond,postcond]))
   
   branch2bool (cvar, (ABranch p e)) =
     exp2bool ti (resvar,e) `bindS` \branchbexp ->
     getS `bindS` \ts ->
     putS ts { varTypes = patvars ++ varTypes ts} `bindS_`
     returnS (Conj [ bEquVar cvar (pat2bool p), branchbexp])
    where
     patvars = if isConsPattern p
                 then patArgs p
                 else []


   arg2bool e = case e of AVar _ i -> BVar i
                          ALit _ l -> lit2bool l
                          _ -> error $ "Not normalized: " ++ show e

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
-- Updates a function definition in a list of function declarations.
updFuncDecl :: TAFuncDecl -> [TAFuncDecl] -> [TAFuncDecl]
updFuncDecl _    []     = []
updFuncDecl newf (f:fs) =
  if funcName f == funcName newf
    then newf : fs
    else f : updFuncDecl newf fs

-- Removes a function definition in a list of function declarations.
rmFuncDecl :: TAFuncDecl -> [TAFuncDecl] -> [TAFuncDecl]
rmFuncDecl _    []     = []
rmFuncDecl oldf (f:fs) =
  if funcName f == funcName oldf
    then fs
    else f : rmFuncDecl oldf fs

-- Adds a suffix to some qualified name:
addSuffix :: QName -> String -> QName
addSuffix (mn,fn) s = (mn, fn ++ s)

---------------------------------------------------------------------------
-- Calls the SMT solver to check whether an assertion implies some
-- (pre/post) condition.
checkImplicationWithSMT :: Options -> [(Int,TypeExpr)] -> BoolExp -> BoolExp
                        -> BoolExp -> IO Bool
checkImplicationWithSMT opts vartypes assertion impbindings imp = do
  let smt = unlines
              [ "; Free variables:"
              , typedVars2SMT vartypes
              , "; Boolean formula of assertion (known properties):"
              , showBoolExp (assertSMT assertion)
              , ""
              , "; Bindings of implication:"
              , showBoolExp (assertSMT impbindings)
              , ""
              , "; Assert negated implication:"
              , showBoolExp (assertSMT (Not imp))
              , ""
              , "; check satisfiability:"
              , "(check-sat)"
              , "; if unsat, we can omit the postcondition check"
              ]
  let allsymbols = allSymbolsOfBE (Conj [assertion, impbindings, imp])
      allqsymbols = catMaybes (map untransOpName allsymbols)
  unless (null allqsymbols) $ printWhenIntermediate opts $
    "Translating operations into SMT:\n" ++
    unwords (map showQName allqsymbols)
  smtfuncs   <- funcs2SMT allqsymbols
  smtprelude <- readFile (packagePath </> "include" </> "Prelude.smt")
  let smtinput = smtprelude ++ smtfuncs ++ smt
  printWhenIntermediate opts $ "SMT SCRIPT:\n" ++ smtinput
  printWhenIntermediate opts $ "CALLING Z3..."
  (ecode,out,err) <- evalCmd "z3" ["-smt2", "-in", "-T:5"] smtinput
  when (ecode>0) $ printWhenIntermediate opts $ "EXIT CODE: " ++ show ecode
  printWhenIntermediate opts $ "RESULT:\n" ++ out
  unless (null err) $ printWhenIntermediate opts $ "ERROR:\n" ++ err
  let pcvalid = let ls = lines out in not (null ls) && head ls == "unsat"
  return pcvalid

-- Operations axiomatized by specific smt scripts (no longer necessary
-- since these scripts are now automatically generated by Curry2SMT.funcs2SMT).
-- However, for future work, it might be reasonable to cache these scripts
-- for faster contract checking.
axiomatizedOps :: [String]
axiomatizedOps = ["Prelude_null","Prelude_take","Prelude_length"]

---------------------------------------------------------------------------
-- Translates a FlatCurry type to an SMT type string:
type2SMT :: TypeExpr -> String
type2SMT (TVar _) = "TVar"
type2SMT (FuncType dom ran) = type2SMT dom ++ " -> " ++ type2SMT ran
type2SMT (TCons (mn,tc) targs)
  | mn=="Prelude" && length targs == 0 = tc
  | mn=="Prelude" && tc == "[]" && length targs == 1
  = "(List " ++ type2SMT (head targs) ++ ")"
  | otherwise = mn ++ "." ++ tc -- TODO: complete

-- Translates a list of type variables to SMT declarations:
typedVars2SMT :: [(Int,TypeExpr)] -> String
typedVars2SMT tvars = unlines (map tvar2SMT tvars)
 where
  tvar2SMT (i,te) =
    withBracket (unwords ["declare-const", smtBE (BVar i), type2SMT te])

---------------------------------------------------------------------------
-- Auxiliaries:

--- Checks whether a file exists in one of the directories on the PATH.
fileInPath :: String -> IO Bool
fileInPath file = do
  path <- getEnviron "PATH"
  dirs <- return $ splitOn ":" path
  (liftIO (any id)) $ mapIO (doesFileExist . (</> file)) dirs

---------------------------------------------------------------------------