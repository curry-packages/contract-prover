-------------------------------------------------------------------------
--- The options of the contract verification tool.
---
--- @author Michael Hanus
--- @version September 2017
-------------------------------------------------------------------------

module ProverOptions( Options(..), defaultOptions, processOptions )
 where

import Distribution          ( stripCurrySuffix )
import Numeric               ( readNat )
import System.Process        ( exitWith )
import System.Console.GetOpt

data Options = Options
  { optVerb    :: Int    -- verbosity (0: quiet, 1: status, 2: interm, 3: all)
  , optHelp    :: Bool   -- if help info should be printed
  , optReplace :: Bool   -- replace FlatCurry program with optimized version?
  , optStrict  :: Bool   -- verify precondition w.r.t. strict evaluation?
                         -- in this case, we assume that all operations are
                         -- strictly evaluated which might give better results
                         -- but might not be correct if some argument is not
                         -- demanded (TODO: add demand analysis to make it
                         -- safe and powerful)
  }

defaultOptions :: Options
defaultOptions = Options 1 False True False

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
usageText = usageInfo ("Usage: curry-ctopt [options] <module names>\n") options

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
  , Option "n" ["nostore"] (NoArg (\opts -> opts { optReplace = False }))
           "do not write optimized program"
  , Option "s" ["strict"] (NoArg (\opts -> opts { optStrict = True }))
           "check contracts w.r.t. strict evaluation strategy"
  ]
 where
  safeReadNat opttrans s opts =
    case readNat s of
      [(n,"")] -> opttrans n opts
      _        -> error "Illegal number argument (try `-h' for help)"

  checkVerb n opts = if n>=0 && n<4
                     then opts { optVerb = n }
                     else error "Illegal verbosity level (try `-h' for help)"

-------------------------------------------------------------------------
