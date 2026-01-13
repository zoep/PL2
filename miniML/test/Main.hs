module Main where

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Data.Map as M

import MiniML
import Gen

-- | The main testing function. Runs a series of tests. Add as many additional
-- tests as you want.
main :: IO ()
main = defaultMain $ testGroup "act"
  [ testProperty "Parser round trip" parserRoundTrip 
  , testProperty "Type checking" typeCheckProp
  , testProperty "Type inference" typeInferenceProp
  , testProperty "Closure Conversion" closureConversionProp
  ]

-- | A property that for a randomly generated MiniML program, pretty-printing it
-- and parsing it produces the original program (i.e., `parse . lex . showExp == id`)
parserRoundTrip :: Property
parserRoundTrip =
  forAll genExp (\e ->
    let txt = showExp e in
    case parse $ lexer txt of
      Left err -> 
        whenFail (prettyErrs txt err) (counterexample "Parsing failed!" False)
      Right e' -> e === e')


-- | A property that for a randomly generated MiniML program with type `t`,
-- type checking should succeed and yield the same type `t`.
-- (5 points)
typeCheckProp :: Property
typeCheckProp = error "TODO: implement typeCheckProp"

-- | A property that for a randomly generated MiniML program with type `t`,
-- type inference should succeed and yield the same or a more general type than `t`.
-- (20 points)
typeInferenceProp :: Property
typeInferenceProp = error "TODO: implement typeInferenceProp"


-- | A property that for a randomly generated MiniML program,
-- performing closure conversion should yield a semantically equivalent program.
-- (30 points)
closureConversionProp :: Property
closureConversionProp = error "TODO: implement closureConversionProp"


-- Question 1 (5 points): Why is it important to test the closure conversion transformation 
-- on well-typed programs? What meta-theoretical property do we take advantage of here?


{--  Your answer: 




--}


-- Question 2 (10 points): Did you find any bug in the given code while implementing the tests above?
-- If yes, describe the bug and how you found it.


{--  Your answer: 



--}
