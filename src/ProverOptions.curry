-------------------------------------------------------------------------
--- The options of the contract verification tool.
---
--- @author Michael Hanus
--- @version June 2017
-------------------------------------------------------------------------

module ProverOptions( Options(..), defaultOptions, processOptions )
 where

import Distribution      ( stripCurrySuffix )
import GetOpt
import ReadNumeric       ( readNat )
import System            ( exitWith )

data Options = Options
  { optVerb    :: Int    -- verbosity (0: quiet, 1: status, 2: interm, 3: all)
  , optHelp    :: Bool   -- if help info should be printed
  , optReplace :: Bool   -- replace FlatCurry program with optimized version?
  }

defaultOptions :: Options
defaultOptions = Options 1 False True

--- Process the actual command line argument and return the options
--- and the name of the main program.
processOptions :: [String] -> IO (Options,String)
processOptions argv = do
  let (funopts, args, opterrors) = getOpt Permute options argv
      opts = foldl (flip id) defaultOptions funopts
  unless (null opterrors)
         (putStr (unlines opterrors) >> putStrLn usageText >> exitWith 1)
  when (optHelp opts) (putStrLn usageText >> exitWith 0)
  when (length args /= 1 || optHelp opts) (putStrLn usageText >> exitWith 1)
  return (opts, stripCurrySuffix (head args))

-- Help text
usageText :: String
usageText = usageInfo ("Usage: curry-opt [options] <module name>\n") options
  
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
  , Option "n" ["nostore"] (NoArg (\opts -> opts { optReplace = True }))
           "do not write optimized program"
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

-------------------------------------------------------------------------
