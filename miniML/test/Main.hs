module Main (main) where

import Test.Tasty
import Test.Tasty.QuickCheck
import Control.Monad.State

import Data.Map as M
import MiniML
import Gen
import Debug.Trace (trace)

-- The main testing function. Runs a series of tests. Add as many additional
-- tests as you want.

main :: IO ()
main = defaultMain $ testGroup "act"
  [ testProperty "Parser round trip" parserRoundTrip ]

-- A property that for a randomly MiniML as pretty-printing it and parsing it
-- produces the original program (i.e., `parse . lex . showExp == id`)
parserRoundTrip :: Property
parserRoundTrip =
  forAll genExp (\e ->
    let txt = showExp e in
    case parse $ lexer txt of
      Left err -> 
        trace ("Parsing failed on input: " ++ txt ++ "\nError: " ++ show err) $
        whenFail (prettyErrs txt err) (counterexample "Parsing failed!" False)
      Right e' -> e === e')

