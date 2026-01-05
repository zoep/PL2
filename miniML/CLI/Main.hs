module Main where

import System.Environment (getArgs)

import MiniML

data Mode = Print | PrintCC | TypeCheck | Infer | Eval | EvalCC

getArg :: [String] -> (Mode, String)
getArg ("--pretty-print":f:_) = (Print,f)
getArg ("--type-check":f:_) = (TypeCheck, f)
getArg ("--infer":f:_) = (Infer, f)
getArg ("--eval":f:_) = (Eval, f)
getArg ("--eval-cc":f:_) = (EvalCC, f)
getArg ("--pretty-print-cc":f:_) = (PrintCC,f)
getArg args = error $ "Invalid argument format: " <> show args

proceed :: String       -- the input file for better error reporting
        -> Error a      -- the computation to run
        -> (a -> IO ()) -- its continuation
        -> IO ()
proceed src res f = case res of
    Left err -> prettyErrs src err
    Right a -> f a

main :: IO ()
main = do
  args <- getArgs
  let (mode, fin) = getArg args
  src <- readFile fin
  case mode of
    Print -> proceed src (parse $ lexer src) printExp
    PrintCC -> proceed src (parse (lexer src)) (\e ->                 
                 proceed src (typeCheckTop e) (\_ -> printExp (closureConv $ implementLazy e)))
    TypeCheck -> proceed src (parse (lexer src)) (\e ->
                   proceed src (typeCheckTop e) printType)
    Infer -> proceed src (parse (lexer src)) (\e ->
                 proceed src (inferTypeTop e) printTypeScheme)
    Eval -> proceed src (parse $ lexer src) (\e ->
              -- proceed src (typeCheckTop e) (\_ -> 
                proceed src (evalTop $ implementLazy e) $ printValue . fst)
    EvalCC -> proceed src (parse $ lexer src) (\e ->
                -- proceed src (typeCheckTop e) (\_ ->
                  proceed src (evalccTop (closureConv $ implementLazy e)) $ printValue . fst)