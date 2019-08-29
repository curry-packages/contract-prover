-------------------------------------------------------------------------
--- The options of the contract verification tool together with some
--- related operations.
---
--- @author Michael Hanus
--- @version July 2019
-------------------------------------------------------------------------

module ToolOptions
  ( Options(..), defaultOptions, processOptions
  , printWhenStatus, printWhenIntermediate, printWhenAll
  )
 where

import Char              ( toUpper )
import GetOpt
import ReadNumeric       ( readNat )
import System            ( exitWith )

import System.CurryPath  ( stripCurrySuffix )

data Options = Options
  { optVerb    :: Int    -- verbosity (0: quiet, 1: status, 2: interm, 3: all)
  , optHelp    :: Bool   -- if help info should be printed
  , optName    :: String -- show only the name of a nonfail condition
  , optVerify  :: Bool   -- verify contracts (or just add them)?
  , optFCY     :: Bool   -- replace FlatCurry program?
  , optTFCY    :: Bool   -- replace typed FlatCurry program?
  , optStrict  :: Bool   -- verify precondition w.r.t. strict evaluation?
                         -- in this case, we assume that all operations are
                         -- strictly evaluated which might give better results
                         -- but not not be correct if some argument is not
                         -- demanded (TODO: add demand analysis to make it
                         -- safe and powerful)
  , optNoProof :: Bool   -- do not write scripts of successful proofs
  }

defaultOptions :: Options
defaultOptions = Options 1 False "" True True False False False

--- Process the actual command line argument and return the options
--- and the name of the main program.
processOptions :: String -> [String] -> IO (Options,[String])
processOptions banner argv = do
  let (funopts, args, opterrors) = getOpt Permute options argv
      opts = foldl (flip id) defaultOptions funopts
  unless (null opterrors)
         (putStr (unlines opterrors) >> printUsage >> exitWith 1)
  when (optHelp opts) (printUsage >> exitWith 0)
  return (opts, map stripCurrySuffix args)
 where
  printUsage = putStrLn (banner ++ "\n" ++ usageText)

-- Help text
usageText :: String
usageText = usageInfo ("Usage: curry-contracts [options] <module names>\n") options
  
-- Definition of actual command line options.
options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"]  (NoArg (\opts -> opts { optHelp = True }))
           "print help and exit"
  , Option "q" ["quiet"] (NoArg (\opts -> opts { optVerb = 0 }))
           "run quietly (no output, only exit code)"
  , Option "v" ["verbosity"]
            (OptArg (maybe (checkVerb 2) (safeReadNat checkVerb)) "<n>")
            "verbosity level:\n0: quiet (same as `-q')\n1: show status messages (default)\n2: show intermediate results (same as `-v')\n3: show all intermediate results and more details"
  , Option "a" ["add"] (NoArg (\opts -> opts { optVerify = False }))
           "do not verify contracts, just add contract checks"
  , Option "s" ["strict"] (NoArg (\opts -> opts { optStrict = True }))
           "check contracts w.r.t. strict evaluation strategy"
  , Option "t" ["target"]
            (ReqArg checkTarget "<T>")
           ("target of the transformed program:\n" ++
            "NONE: do not store transformed FlatCurry program\n" ++
            "FCY : write FlatCurry program (default)\n" ++
            "TFCY: write typed FlatCurry program")
  , Option "" ["noproof"] (NoArg (\opts -> opts { optNoProof = True }))
           "do not write scripts of successful proofs"
  , Option "" ["name"]
            (ReqArg (\s opts -> opts { optName = s }) "<f>")
            "only show the names of pre- and postconditions\nfor function <f>"
  ]
 where
  safeReadNat opttrans s opts =
   let numError = error "Illegal number argument (try `-h' for help)"
   in maybe numError
            (\ (n,rs) -> if null rs then opttrans n opts else numError)
            (readNat s)

  checkVerb n opts = if n>=0 && n<4
                       then opts { optVerb = n }
                       else error "Illegal verbosity level (try `-h' for help)"

  checkTarget t opts = case map toUpper t of
    "NONE" -> opts { optFCY = False, optTFCY = False }
    "FCY"  -> opts { optFCY = True,  optTFCY = False }
    "TFCY" -> opts { optFCY = False, optTFCY = True  }
    _      -> error $ "Illegal target `" ++ t ++ "' (try `-h' for help)"

-------------------------------------------------------------------------

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
printCP s = putStrLn $ "INFO: " ++ s

---------------------------------------------------------------------------
