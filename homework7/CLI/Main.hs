module Main where

import System.Environment (getArgs)

import MiniML

data Mode = Print | Type | Eval

getArg :: [String] -> (Mode, String)
getArg ("--pretty-print":f:_) = (Print,f)
getArg ("--type-check":f:_) = (Type, f)
getArg ("--eval":f:_) = (Eval, f)
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
    Type -> proceed contents (parse $ lexer contents) (\e ->
              proceed contents (typeCheckTop e) printType)
    Eval ->
      -- parse
      proceed contents (parse $ lexer contents) (\e -> do
        -- typecheck
        proceed contents (typeCheckTop e) (\_ ->
          -- add return types to lambdas. Ths is needed to correctly propagate
          -- types to values so that values can be typechecked.
          proceed contents (annotateTop e) (\e' ->
            -- evaluate
            proceed contents (evalTop e') (\(v,s) ->
              -- print the resulting value
              printConf s v))))