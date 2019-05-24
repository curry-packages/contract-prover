module VerifierState where

import IOExts
import List ( find )

import Contract.Names ( isPreCondName, isPostCondName )
import FlatCurry.Annotated.Goodies ( funcName, typeName, progName, progTypes )

import FlatCurry.Typed.Types
import ToolOptions

---------------------------------------------------------------------------
-- Some global information used by the transformation process:
data VerifyInfo = VerifyInfo
  { toolOpts      :: Options      -- options passed to the tool
  , allFuns       :: [TAFuncDecl] -- all defined operations
  , preConds      :: [TAFuncDecl] -- all precondition operations
  , postConds     :: [TAFuncDecl] -- all postcondition operations
  }

makeVerifyInfo :: Options -> [AFuncDecl TypeExpr] -> VerifyInfo
makeVerifyInfo opts fdecls = VerifyInfo opts fdecls preconds postconds
 where
  -- Precondition operations:
  preconds  = filter (isPreCondName  . snd . funcName) fdecls
  -- Postcondition operations:
  postconds = filter (isPostCondName . snd . funcName) fdecls

---------------------------------------------------------------------------
-- The global state of the verification process keeps some
-- statistical information and the programs that are already read
-- (to avoid multiple readings).
data VState = VState
  { trInfo      :: VerifyInfo -- information used by the transformation process
  , uPreCond    :: [String]   -- unverified preconditions
  , vPreCond    :: [String]   -- verified preconditions
  , uPostCond   :: [String]   -- unverified postconditions
  , vPostCond   :: [String]   -- verified postconditions
  , currTAProgs :: [TAProg]   -- already read typed FlatCurry programs
  }

initVState :: VerifyInfo -> VState
initVState ti = VState ti [] [] [] [] []

--- Reads VerifyInfo from VState IORef.
readVerifyInfoRef :: IORef VState -> IO VerifyInfo
readVerifyInfoRef vstref = readIORef vstref >>= return . trInfo

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
--- Selects the type declaration of a type constructor from the state.
tdeclOf :: VState -> QName -> Maybe TypeDecl
tdeclOf vst tcons@(mn,_) =
  maybe Nothing
        (\p -> find (\td -> typeName td == tcons) (progTypes p))
        (find (\p -> progName p == mn) (currTAProgs vst))

---------------------------------------------------------------------------
