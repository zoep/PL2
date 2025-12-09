{-# LANGUAGE OverloadedStrings #-}

module MiniML.Error where

import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import qualified Data.Text as T
import MiniML.Syntax (Posn, nowhere)
import MiniML.Lex (AlexPosn(..), lastPos)


-- A computation that may return an error. It is used by the typechecking and
-- evaluation functions.

-- `Error` is defined as a type alias for `Either`, where the left value
-- represents an error (with a position and an error message), and the right
-- value represents a successful result.

-- The `Either` type has a `Monad` instance (it's provided by the Haskell base
-- library) and it is similar to the `Maybe` monad. Therefore, Error is also a
-- Monad and computations can be sequenced using monadic operations.

-- You can find more about the Either data type here
-- https://hackage.haskell.org/package/base-4.20.0.1/docs/Data-Either.html

type Error res = Either (Posn,String) res

throw :: (Posn,String) -> Error a
throw = Left

-- Pretty Errs Str
prettyErrsStr :: String -> (Posn, String) -> String
prettyErrsStr contents = prettyErrStr
  where
    prettyErrStr (pn, msg) 
      | pn == nowhere = 
          "Internal error:\n" <> msg
      | pn == lastPos = 
          let culprit = last $ lines contents
              line' = length (lines contents) - 1
              col  = length culprit
              marker = T.unpack (T.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
          in unlines [show line' <> " | " <> culprit, marker, msg]
      | otherwise = 
          case pn of
            AlexPn _ line' col -> 
              let cxt = safeDrop (line' - 1) (lines contents)
                  marker = T.unpack (T.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
              in unlines [msg <> ":", show line' <> " | " <> hd cxt, marker]
    
    hd :: [a] -> a
    hd (x:_) = x
    hd _ = error "Internal error: expecting nonempty list"

    safeDrop :: Int -> [a] -> [a]
    safeDrop 0 a = a
    safeDrop _ [] = []
    safeDrop _ [a] = [a]
    safeDrop n (_:xs) = safeDrop (n-1) xs

-- Pretty print errors with source code position.
-- Almost verbatim from Act (https://github.com/ethereum/act/blob/main/src/Act/CLI.hs#L295)
prettyErrs :: String -> (Posn, String) -> IO ()
prettyErrs contents errs = prettyErr errs >> exitFailure
  where
  prettyErr (pn, msg) | pn == nowhere = do
    hPutStrLn stderr "Internal error:"
    hPutStrLn stderr msg
  prettyErr (pn, msg) | pn == lastPos = do
    let culprit = last $ lines contents
        line' = length (lines contents) - 1
        col  = length culprit
    hPutStrLn stderr $ show line' <> " | " <> culprit
    hPutStrLn stderr $ T.unpack (T.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
    hPutStrLn stderr msg
  prettyErr (AlexPn _ line' col, msg) = do
    let cxt = safeDrop (line' - 1) (lines contents)
    hPutStrLn stderr $ msg <> ":"
    hPutStrLn stderr $ show line' <> " | " <> hd cxt
    hPutStrLn stderr $ T.unpack (T.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
    where
      hd :: [a] -> a
      hd (x:_) = x
      hd _ = error "Internal error: expecting nonempty list"

      safeDrop :: Int -> [a] -> [a]
      safeDrop 0 a = a
      safeDrop _ [] = []
      safeDrop _ [a] = [a]
      safeDrop n (_:xs) = safeDrop (n-1) xs
