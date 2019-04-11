module VerifierState where

import IOExts
import List ( find )

import FlatCurry.Annotated.Types
import FlatCurry.Annotated.Goodies

import Contract.Names ( isPreCondName, isPostCondName )
import ProverOptions

---------------------------------------------------------------------------
-- Some global information used by the transformation process:
data TransInfo = TransInfo
  { tiOptions     :: Options      -- options passed to all defined operations
  , allFuns       :: [AFuncDecl TypeExpr] -- all defined operations
  , preConds      :: [AFuncDecl TypeExpr] -- all precondition operations
  , postConds     :: [AFuncDecl TypeExpr] -- all postcondition operations
  }

makeTransInfo :: Options -> [AFuncDecl TypeExpr] -> TransInfo
makeTransInfo opts fdecls = TransInfo opts fdecls preconds postconds
 where
  -- Precondition operations:
  preconds  = filter (isPreCondName . snd . funcName) fdecls
  -- Postcondition operations:
  postconds = filter (isPostCondName . snd . funcName) fdecls

---------------------------------------------------------------------------
-- The global state of the verification process keeps some
-- statistical information and the programs that are already read
-- (to avoid multiple readings).
data VState = VState
  { trInfo      :: TransInfo -- information used by the transformation process
  , uPreCond    :: [String]  -- unverified preconditions
  , vPreCond    :: [String]  -- verified preconditions
  , uPostCond   :: [String]  -- unverified postconditions
  , vPostCond   :: [String]  -- verified postconditions
  , currTAProgs :: [AProg TypeExpr]  -- already read typed FlatCurry programs
  }

initVState :: TransInfo -> VState
initVState ti = VState ti [] [] [] [] []

--- Reads TransInfo from VState IORef.
readTransInfoRef :: IORef VState -> IO TransInfo
readTransInfoRef vstref = readIORef vstref >>= return . trInfo

--- Shows the statistics in human-readable format.
showStats :: VState -> String
showStats vst =
  showStat "PRECONDITIONS : VERIFIED  " (vPreCond  vst) ++
  showStat "PRECONDITIONS : UNVERIFIED" (uPreCond  vst) ++
  showStat "POSTCONDITIONS: VERIFIED  " (vPostCond vst) ++
  showStat "POSTCONDITIONS: UNVERIFIED" (uPostCond vst) ++
  (if areContractsAdded vst then "" else "\nALL CONTRACTS VERIFIED!")
 where
  showStat t fs = if null fs then "" else "\n" ++ t ++ ": " ++ unwords fs

--- Is the program transformed so that some contracts are added?
areContractsAdded :: VState -> Bool
areContractsAdded vst = not (null (uPreCond vst) && null (uPostCond vst))

--- Increments the number of preconditions. If the first argument is true,
--- a precondition has been verified.
addPreCondToStats :: String -> Bool -> VState -> VState
addPreCondToStats pc verified vst =
  if verified then vst { vPreCond = pc : vPreCond vst }
              else vst { uPreCond = pc : uPreCond vst }

--- Adds an operation to the already processed operations with postconditions.
--- If the second argument is true, the postcondition of this operation
--- has been verified.
addPostCondToStats :: String -> Bool -> VState -> VState
addPostCondToStats pc verified vst =
  if verified then vst { vPostCond = pc : vPostCond vst }
              else vst { uPostCond = pc : uPostCond vst }

--- Adds a new typed FlatCurry program to the state.
addProgToState :: AProg TypeExpr -> VState -> VState
addProgToState prog vstate = vstate { currTAProgs = prog : currTAProgs vstate }

---------------------------------------------------------------------------
