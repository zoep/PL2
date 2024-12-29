module Main where

import System.Environment (getArgs)

import MiniML

data Mode = Print | TypeInf

getArg :: [String] -> (Mode, String)
getArg ("--pretty-print":f:_) = (Print,f)
getArg ("--type-inf":f:_) = (TypeInf, f)
getArg _ = error "Invalid argument format."

proceed :: String       -- the input file for better error reporting
        -> Error a      -- the computation to run
        -> (a -> IO ()) -- its continuation
        -> IO ()
proceed contents res f = case res of
    Left err -> prettyErrs contents err
    Right a -> f a

main :: IO ()
main = do
  args <- getArgs
  let (mode, f) = getArg args
  contents <- readFile f
  case mode of
    Print -> proceed contents (parse $ lexer contents) printExp
    TypeInf -> proceed contents (parse $ lexer contents) (\e ->
                 proceed contents (inferTypeTop e) printTypeScheme)