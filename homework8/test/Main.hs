module Main (main) where

import Test.Tasty
import Test.Tasty.QuickCheck

import MiniML
import Gen

-- The main testing function. Runs a series of tests. Add as many additional
-- tests as you want.

main :: IO ()
main = defaultMain $ testGroup "act"
  [ testProperty "Parser round trip" parserRoundTrip
  , testProperty "Type inference" testTypeInf
  , testProperty "Placeholder" someProperty ]

-- A property that for a randomly MiniML as pretty-printing it and parsing it
-- produces the original program (i.e., `parse . lex . showExp == id`)
parserRoundTrip :: Property
parserRoundTrip =
  forAll genExp (\e ->
    let txt = showExp e in
    case parse $ lexer txt of
      Left err -> whenFail (prettyErrs txt err) (counterexample "Parsing failed!" False)
      Right e' -> e === e')


testTypeInf :: Property
testTypeInf = counterexample "FILL IN HERE!" False


someProperty :: Property
someProperty =
  forAll (choose (5,10 :: Int)) (<= 10)
