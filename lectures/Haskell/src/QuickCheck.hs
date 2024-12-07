module QuickCheck where

import Prelude hiding (map)
import Test.QuickCheck
import Control.Monad
import Control.Monad.State hiding (when)
import Data.List hiding (insert,map)
import qualified Data.Map as M
import System.Random (Random)
import Data.Maybe (isJust)
import Debug.Trace

{- Property Based Testing
   ======================

Property-based testing is a powerful automatic testing methodology where the
programmer writes program specifications, expressed as boolean predicates. These
specifications are then tested against a large set of randomly generated inputs
to identify potential property violations.

This approach combines benefits from both formal verification and testing:

Formal Specifications: The programmer formally specifies their code, which
enhances understanding and documentation.

Automated Falsification: The specifications are tested automatically, allowing
for quick bug discovery.

While property-based testing alone cannot prove the absolute correctness of a
specification, it is highly effective at exposing flaws, enhancing software
quality, and accelerating the development process.

Property-based random testing was introduced and popularized by QuickCheck [1],
a Haskell library and testing framework that provides combinator for writing
properties and random input generators. Since then, QuickCheck has been ported
to many other languages.

Note: You can find more QuickCheck course material in [2] and [3].

-}


{- Properties
   ---------
Let's start by defining some basic properties for QC to test.


-}


revLength :: [Integer] -> Bool
revLength l = length l == length (reverse l)

revInvolutive :: [Integer] -> Bool
revInvolutive xs = reverse (reverse xs) == xs

revSingleton :: Integer -> Bool
revSingleton a = reverse [a] == [a]

revAppend :: [Integer] -> [Integer] -> Bool
revAppend xs ys = reverse (xs ++ ys) == reverse ys ++ reverse xs

revAppendWrong :: [Integer] -> [Integer] -> Bool
revAppendWrong xs ys = reverse (xs ++ ys) == reverse xs ++ reverse ys


{- We can then open the REPL and try the following

ghci> quickCheck revSingleton
+++ OK, passed 100 tests.

ghci> quickCheck revAppend
+++ OK, passed 100 tests.

ghci> quickCheck revAppendWrong
*** Failed! Falsified (after 2 tests):
[]
[0]

ghci> quickCheck revInvolutive
+++ OK, passed 100 tests.

-}

{-- Testable
    --------

All four of the above calls type check, which makes us wonder what is the type
of the quickCheck function.

quickCheck :: Testable prop => prop -> IO ()

quickCheck takes as input an instance of the Testable class. This is the class
of properties that QC knows how to test.

It has one function:

property :: prop -> Property

Which test something testable and turns it into the Testable type. Testable is
the type of testable properties in QC.

Let's look at some instances:

-- Of course A Property is testable
Testable Property

-- Bool is trivially testable
Testable Bool

-- If a property is Testable, then a -> prop is testable, provided that the
   input satisfies -- some type class constraints, in particular Show and
   Arbitrary. Show will let QuickCheck print -- counterexamples, if any, and
   Arbitrary is QC's type class for types for which there are random generators.

--  (Arbitrary a, Show a, Testable prop) => Testable (a -> prop)

Internally what this instance does is to generate random inputs for the argument a,
and pass them to the property so that it can be tested.

QC derived properties for all of the function above using the second and third instance.

This can be done with the forAll combinator, as we will see later.

-}


{- More Properties
   ---------------

Let's now try to write more convoluted properties that test an insertion sort implementation.
-}

insert :: Integer -> [Integer] -> [Integer]
insert v []= [v]
insert v (x:xs) | x < v = x : insert v xs
insert v (x:xs) = v : x : xs

insertionSort :: [Integer] -> [Integer]
insertionSort [] = []
insertionSort (x:xs) = insert x (insertionSort xs)

-- >>> insertionSort [7,5,4,3,4]
-- [3,4,4,5,7]

-- We will define and test the properties that our implementation needs to
-- satisfy. One obvious one is the the output of insertionSort must be sorted.

-- We define an isSorted predicate that we use to test the implementation if insertionSort

isSorted :: [Integer] -> Bool
isSorted [] = True
isSorted (x:xs)= aux x xs
 where
    aux _ [] = True
    aux y (z:zs) = y <= z && aux z zs


sortedProp :: ([Integer] -> [Integer]) -> [Integer] -> Bool
sortedProp f = isSorted . f

{- We run:

ghci> quickCheck $ sortedProp insertionSort
+++ OK, passed 100 tests.

That's good. But also, a trivial wrong implementation that always the empty list satisfies this spec.

ghci> quickCheck $ sortedProp (\_ -> [])
-- ... complains about some types ...
+++ OK, passed 100 tests.

Let's try to further refine the output.
-}

lengthProp :: ([Integer] -> [Integer]) -> [Integer] -> Bool
lengthProp f xs = length xs == length (f xs)


{-
ghci> quickCheck $ lengthProp insertionSort
+++ OK, passed 100 tests.

That's better but we can still find a wrong implementation that passes all of this tests.


ghci> quickCheck $ sortedProp (\xs -> repeat 1 (length xs))

-}

bogusSort :: [Integer] -> [Integer]
bogusSort xs = replicate (length xs) 1

-- If you're aiming for more "Haskell-like" brevity (and don’t mind alienating
-- the reader!), you can write the same function using point-free style:

-- bogusSort = flip replicate 1 . length

{- bogusSort passes all the tests, despite being bogus.

ghci> quickCheck $ sortedProp bogusSort
+++ OK, passed 100 tests.

ghci> quickCheck $ lengthProp bogusSort
+++ OK, passed 100 tests.

-}

{-

We need an even more precise property here. We need to test that the output
list, in addition to being sorted,  must contain exactly the same elements as
the input list, including their frequencies

Exercise: Write a property that states that the output of insertionSort is a
permutation of the input. Think about how you can do this efficiently.

-}

{- Conditional Properties
   -----------------------

It is a good idea to also check correctness properties for the insert function.
After all, if we find a bug in insertionSort it may very well be that it is a
bug in the implementation of insert.

We will test that insert preserves the "sortedness" of a list:
if the input list is sorted then the output list after the insertion should also
be sorted.

To do this we must write a conditional property. To do this we uses QC's ==>
combinator.

(==>) :: Testable prop => Bool -> prop -> Property

Note: as above, this does not uniquely determine the output of insert and to test full
functional correctness we must also write more properties.
-}

insertPreservesSorted :: Integer -> [Integer] -> Property
insertPreservesSorted x xs = isSorted xs ==> isSorted (insert x xs)

{-

Let's see what happens.

ghci> quickCheck $ insertPreservesSorted
*** Gave up! Passed only 63 tests; 1000 discarded tests.

QuickCheck reports that 63 tests passed but the rest was discarded. We can try
to increase the number of tests that QC runs, using the combinator withMaxSuccess.

-- Configures how many times a property will be tested.
withMaxSuccess ::  forall prop. Testable prop => Int -> prop -> Property


-}

quickCheckN :: (Testable prop) => Int -> prop -> IO ()
quickCheckN n = quickCheck . withMaxSuccess n

{-

We configure ghci to also output timing and memory info after the evaluation of every expression.

ghci> :set +s

Then we test the property.

ghci> quickCheckN 100000 $ insertPreservesSorted
*** Gave up! Passed only 55173 tests; 1000000 discarded tests.
(13.83 secs, 17,899,048,256 bytes)

This is somewhat better than above, but still very inefficient. It takes almost
14 seconds and tests only the ~5% of the generated tests.

This makes sense, as sorted is a scarce property. Only a small fraction of
randomly generated inputs will naturally have this characteristic. To make
things worse, most of the 55173 tests that are sorted will be very small, as the
probability of generating a sorted list decreases significantly as the list size
increases.

QuickChick lets us peek at the distribution of various properties of test cases
by providing a combinator called collect.

-- Collect will gather all values that are being passed to itm and will print out a histogram of the distribution of the values.
collect :: (Show a, Testable prop) => a -> prop -> Property collect

By using collect, we can group test cases based on a specific property (e.g.,
whether the list is sorted, its size, etc.) and observe their frequency during
testing. This helps identify potential biases in the test input distribution and
ensures that critical edge cases are adequately represented.

-}

insertPreservesSorted':: Integer -> [Integer] -> Property
insertPreservesSorted' x xs = isSorted xs ==> collect (length xs) $ isSorted (insert x xs)

{-

ghci> quickCheckN 100000 $ insertPreservesSorted'
ghci> quickCheckN 100000 $ insertPreservesSorted'
*** Gave up! Passed only 55399 tests; 1000000 discarded tests:
37.434% 0
36.295% 1
18.246% 2
 6.161% 3
 1.473% 4
 0.325% 5
 0.056% 6
 0.009% 7
 0.002% 8


Indeed, the vast majority of test cases (73.7%) have length 0 or 1. Less than 2% of the
test cases have a length more than 4.

So to test this property effectively we must write a fine-tuned generator for lists that only
generates sorted lists.

-}

{- Generators
   ----------

QuickCheck provides a library of generator combinators that lets us write our
own fine tuned generators.

Generators of a type a in QuickCheck have type Gen a. Gen is an instance of the
Monad type class which allows us to combine generators to build more complex ones.

-- Returns a constant generator
return :: a -> Gen a

- Generates an a and passes it to the second generator to generate a b
(>>=)  :: Gen a -> (a -> Gen b) -> Gen b

-}

{-

The Arbitrary Type Class
-----------------------

QuickCheck provides a class called Arbitrary for types that can be randomly generated.

It has two methods:

-- A generator for values of the given type.
arbitrary :: Gen a

-- Produces a (possibly) empty list of all the possible immediate shrinks of the given value.
shrink :: a -> [a]

What does the second method do?

Once a counterexample is found, QC can try to shrink the counterexample in order return a simpler
and more readable counterexample to the reader. It does so using the shrink function.

The default implementation returns the empty list, so will not try to shrink the value.

The Arbitrary type class is useful to write general functions over all type that have random generators.

For example we can write a naive generator for lists of type a.

-}

genList :: Gen [Integer]
genList = listOf arbitrary

{- We used the combinator

listOf :: Gen a -> Gen [a]

Its documentation says:

Generates a list of random length. The maximum length depends on the size
parameter.

What is this size parameter?

Internally, a QC generator receives two arguments: a random seed and a size
parameter. The size parameter can be used by a generator as an upper bound for
the size of the generated elements.

When running tests, QC will use increasingly larger size parameters.

In practice, it is vert common to write a generator that generates
elements of or up to a given size parameter and then use the combinator [sized]
internalize the size parameter.

-- Used to construct generators that depend on the size parameter.
sized :: (Int -> Gen a) -> Gen a

Using sized, we can write a primitive generator for list of a given type a.

-}

genList' :: Arbitrary a => Gen [a]
genList' = sized genListSize
  where
    -- generate a list of a certain length
    genListSize 0 = return []
    genListSize n = do
      x <- arbitrary
      xs <- genListSize (n-1)
      return $ x:xs

-- Note: List has already an arbitrary instance defined in QuickCheck. This is
-- just for demonstration purposes.

{-

Now we have all the necessary knowledge to define a generator for sorted lists.

We will use a couple more useful combinators.

Here's their type and documentation.

-- Generates a random element in the given inclusive range. For integral and enumerated types,
-- the specialized variants of choose below run much quicker.
choose :: (Random a, Ord a) => (a, a) -> Gen a

-- Generates a random element over the natural range of a.
chooseAny :: Random a => Gen a

-- A fast implementation of choose for Integer.
chooseInteger :: (Integer, Integer) -> Gen Integer

You can find many more useful combinators here https://hackage.haskell.org/package/QuickCheck-2.15.0.1/docs/Test-QuickCheck-Gen.html.


-}

-- Our sorted list generator is below.

genSorted :: Gen [Integer]
genSorted = do
    -- pick a lower bound
    lower <- arbitrary
    -- run aux with the lower bound and an arbitrary size
    sized $ aux lower
  where
    -- generates a random sorted list of length len whose first element is
    -- greater or equal to lower
    aux :: Integer -> Int -> Gen [Integer]
    aux _ 0 = return []
    aux lower len = do
      -- get a random positive range
      range <- (arbitrary :: Gen (Positive Integer))
      -- the upper bound is range + lower
      let upper = getPositive range + lower
      -- generate an element in the range [lower,range+lower]
      x <- chooseInteger (lower,upper)
      -- generate a sorted with length (len-1) whose first element is greater or equal to x
      xs <- aux x (len-1)
      -- return the list
      return $ x:xs

{-

We can try our generator out by using sample, a useful combinator that will run
the generator some times.

sample :: Show a => Gen a -> IO ()

ghci> sample genSorted

[]
[0,1]
[0,2,2,3]
[-5,1,1,1,6,7]
[10,17,19,23,28,33,33,40]
[9,9,13,17,17,22,22,24,26,27]
[4,10,17,18,26,26,28,37,42,44,49,58]
[-5,2,15,21,25,30,41,42,43,43,44,48,49,52]
[5,8,9,9,19,22,28,30,33,40,46,53,53,60,62,68]
[12,15,18,18,20,32,37,43,44,59,62,74,79,79,80,92,109,114]
[-13,-1,2,5,13,20,38,45,47,51,52,54,61,62,70,82,91,102,102,104]

-}

{-

Let's use it to test insert. We write a new property that uses the property
combinator forAll.

-- uses an explicitly given test case generator to test a property of type a -> prop
forAll :: (Show a, Testable prop) => Gen a -> (a -> prop) -> Property

You can find more useful property combinators here: https://hackage.haskell.org/package/QuickCheck-2.15.0.1/docs/Test-QuickCheck.html

We will also collect information about the "sortedness" and the length of test data.

-}

testGen :: Property
testGen =
  forAll genSorted isSorted

insertPreservesSorted'' :: Integer -> Property
insertPreservesSorted'' x =
    forAll genSorted (\l -> collect (length l) $ isSorted (insert x l))

{-

ghci> quickCheck insertPreservesSorted''
+++ OK, passed 100 tests:
 1% 0
 1% 1
 1% 10
 1% 11
 1% 12
 1% 13
 ....
 1% 96
 1% 97
 1% 98
 1% 99

Now, not only our test cases are all sorted lists, but each one has a different length. We have achieved way better
test coverage than the previous property.

-}

{- Case study: Red-black Trees
   ---------------------------

Inspired from: https://inria.hal.science/hal-01162898/document

TODO add more comments

Red-black invariant

- No path has two red nodes in a raw.
- Every path from the root to a leaf has the same number of black nodes. This is
  called the black height of the tree.

This invariant guarantees that every leaf is at least at most twice as deep as
any other leaf, which means that the heigh of any tree of N nodes is at most
2logN.

By convention the root of the tree is black.

-}

data Color = Red | Black
  deriving (Show, Eq)

data Tree a = Leaf
            | Node Color a (Tree a) (Tree a)
  deriving (Show, Eq)

-- Balance
balance :: Color -> a -> Tree a -> Tree a -> Tree a
balance Red k t1 t2 = Node Red k t1 t2
balance Black k (Node Red y (Node Red x a b) c) t2 =
    Node Red y (Node Black x a b) (Node Black k c t2)
balance Black k (Node Red x a (Node Red y b c)) t2 =
    Node Red y (Node Black x a b) (Node Black k c t2)
balance Black k t1 (Node Red z (Node Red y b c) d) =
    Node Red y (Node Black k t1 b) (Node Black z c d)
balance Black k t1 (Node Red y b (Node Red z c d)) =
    Node Red y (Node Black k t1 b) (Node Black z c d)
balance Black k t1 t2 = Node Black k t1 t2


-- Auxiliary insert
insert' :: Ord a => a -> Tree a -> Tree a
insert' x Leaf = Node Red x Leaf Leaf
insert' x (Node c y t1 t2) | x < y = balance c y (insert' x t1) t2
insert' x (Node c y t1 t2) | y > x = balance c y t1 (insert' x t2)
insert' _ t = t

-- Insert function
insertRB :: Ord a => a -> Tree a -> Tree a
insertRB x t = makeBlack $ insert' x t
  where
    makeBlack Leaf = Leaf
    makeBlack (Node _ y a b) = Node Black y a b


-- Testing functions

-- Returns a black height, is the tree is back balanced
blackHeight :: Tree a -> Maybe Integer
blackHeight Leaf = return 0
blackHeight (Node c _ t1 t2) = do
    h1 <- blackHeight t1
    h2 <- blackHeight t2
    if h1 == h2 then
      case c of
      Black -> return $ 1 + h1
      Red -> return h1
    else Nothing

height :: Tree a -> Integer
height Leaf = 0
height (Node _ _ t1 t2) = 1 + max (height t1) (height t2)


isBlackBalanced :: Tree a -> Bool
isBlackBalanced = isJust . blackHeight

hasNoRedRed :: Color -> Tree a -> Bool
hasNoRedRed _     Leaf                 = True
hasNoRedRed _     (Node Black _ t1 t2) = hasNoRedRed Black t1 && hasNoRedRed Black t2
hasNoRedRed Red   (Node Red _ _ _)     = False
hasNoRedRed Black (Node Red _ t1 t2)   = hasNoRedRed Red t1 && hasNoRedRed Red t2

-- Red-black invariant predicate
isRedBlack :: Tree a -> Bool
isRedBlack t = isBlackBalanced t && hasNoRedRed Red t

--
genRBTreeHeight :: Arbitrary a => Color -> Int -> Gen (Tree a)
genRBTreeHeight Red   0 = return Leaf
genRBTreeHeight Black 0 = oneof [ return Leaf,
                                  do
                                    n <- arbitrary
                                    return (Node Red n Leaf Leaf)
                                ]
genRBTreeHeight Red    h = liftM3 (Node Black) arbitrary (genRBTreeHeight Black (h-1)) (genRBTreeHeight Black (h-1))
genRBTreeHeight Black  h = do
  c <- elements [Red,Black]
  case c of
    Black -> liftM3 (Node Black) arbitrary (genRBTreeHeight Black (h-1)) (genRBTreeHeight Black (h-1))
    Red -> liftM3 (Node Red) arbitrary (genRBTreeHeight Red h) (genRBTreeHeight Red h)

genRBTree :: Arbitrary a => Gen (Tree a)
-- do not generate trees with black height greater than 10 (i.e, at most 1048576 nodes)
genRBTree = scale (min 10) $ sized (genRBTreeHeight Red)

genMakesSense :: Property
genMakesSense =
  forAll (genRBTree :: Gen (Tree Int)) isRedBlack

insertPreservesRedBlack :: Integer -> Property
insertPreservesRedBlack n =
  forAll genRBTree (\t -> collect (isRedBlack t) $ isRedBlack (insertRB n t))


{-

ghci> quickCheck insertPreservesRedBlack
+++ OK, passed 100 tests (100% True).

-}

{- Case study: Well-typed STLC
   ---------------------------


The code indludes: 

- Definitions of abstract syntax for simply-typed lambda calculus with numbers and addition
- Typechecker for STLC
- Random generator for types
- Random generator for well-typed terms of a given type
- Random generator for well-typed terms of a random type
- Property checker for fuzzing the typechecker

-}

-- STLC with Integers and Addition

data Typ = TInt | TArrow Typ Typ
  deriving (Eq,Show,Ord)

data Exp = Var String
         | App Exp Exp
         | Abs String Typ Exp
         | Num Integer
         | Add Exp Exp
   deriving (Eq, Show)

-- Simple typechecker that returns the type of a type-annotated term
getType :: M.Map String Typ -> Exp -> Maybe Typ
getType env (Var x) = M.lookup x env
getType env (App e1 e2) =  do
  t1 <- getType env e1
  case t1 of
    TArrow t1' t2' -> do
      t2 <- getType env e2
      if t2 == t1' then return t2' else Nothing
    _ -> Nothing
getType env (Abs x t e) = do
  t' <- getType (M.insert x t env) e
  return $ TArrow t t'
getType _ (Num _) = return TInt
getType env (Add e1 e2) = do
  t1 <- getType env e1
  t2 <- getType env e2
  if t1 == TInt && t2 == TInt then return TInt else Nothing


-- Type generator. Generates types up to a given size, where size is the number of arrows.
genTypeSize :: Int -> Gen Typ
genTypeSize n | n <= 0 = return TInt
genTypeSize n =
  frequency [ (1, return TInt)
            , (3, genArrow) ]
  where
    genArrow = do
      t1 <- genTypeSize (n-1)
      t2 <- genTypeSize (n-1)
      return $ TArrow t1 t2


genType :: Gen Typ
genType = arbitrary >>= genTypeSize

-- Generates random terms of a given type and up to a given size. The
-- environment has the available bound variables with their types. We define the
-- size of a term to be the maximum number of binary nodes (addition and
-- applications) on a path from the root to a leaf.
genTermSize :: M.Map Typ [String]  -- a map from types to variables with the corresponding types
            -> Int                 -- counter for generating fresh names (*)
            -> Typ                 -- the type of the generated terms
            -> Int                 -- The size of the term. We define it to be the size of the application nodes.
            -> Gen Exp
genTermSize map next t sz =
  case t of
    -- generate a tern of type TInt
    TInt ->
      frequency $ [ (3, genNat) ]
                  ++ if sz == 0 then [] else [ (2, genAdd) , (1, genApp) ]
                  ++ zip [1..] genVar
    -- generate a tern of type TArrow
    TArrow t1 t2 ->
      frequency $ [ (2, genAbs t1 t2) ]
                  ++ if sz == 0 then [] else [(1, genApp)]
                  ++ zip [1..] genVar

  where
    -- generate an integer
    genNat = liftM Num arbitrary
    -- generate an addition
    genAdd = liftM2 Add (genTermSize map next TInt sz) (genTermSize map next TInt sz)
    -- Generate an already bound variable of the given type
    genVar = case M.lookup t map of
      Just xs -> [elements (fmap Var xs)]
      Nothing -> []
    -- A term of type t can alway be an application of a term of type (t -> t2) to a term of type t
    genApp = do
      -- generate a random type for the input up to the given size
      t1 <- genTypeSize sz
      -- generate a term with type t1 -> t
      e1 <- genTermSize map next (TArrow t1 t) (sz - 1)
      -- generate a term with type t1
      e2 <- genTermSize map next t1 (sz - 1)
      return $ App e1 e2
    -- Generate a lambda abstraction of type t1 -> t2
    genAbs t1 t2 = do
      let name = "x_" ++ show next
      let map' = addVar name t1 map
      e <- genTermSize map' (next+1) t2 sz
      return $ Abs name t1 e
    -- add a variable x with type t to the map
    addVar x typ env = M.insertWith (++) typ [x] env

-- Generate a well-type term
genTerm :: Gen Exp
genTerm = do
  size <- arbitrary
  t <- genType
  genTermSize M.empty 1 t size

-- Generate a well-type term of a certain type
genTermOfType :: Typ -> Gen Exp
genTermOfType t = genTermSize M.empty 1 t 3

-- Generate a well-type term with its type
genTermType :: Gen (Exp,Typ)
genTermType = do
  -- size <- arbitrary
  t <- scale (min 5) $ sized genTypeSize
  e <- scale (min 5) $ sized $ genTermSize M.empty 1 t
  return (e,t)


{-

Let's play around with generating terms. You can type the following in the REPL
and see what comes out.

ghci> sample $ genTypeSize 3

ghci> sample $ genType

ghci> sample $ genTermOfType TInt

ghci> sample $ genTermOfType (TArrow TInt TInt)

ghci> sample $ genTermOfType (TArrow TInt (TArrow TInt TInt))

ghci> genTermType

-}


-- We can now fuzz the typechecker with the well-typed term generator (or, put
-- it differently, test that the generator returns a well typed term according
-- to the typechecker).


typechecksProp :: Property
typechecksProp = forAll genTermType (\(e,t) -> getType M.empty e == Just t)

{-

ghci> quickCheck $ forAll genTermType (\(e,t) -> getType M.empty e == Just t)
+++ OK, passed 100 tests.

-}

{- References
   ----------

[1]: Koen Claessen and John Hughes. 2000. QuickCheck: a lightweight tool for
     random testing of Haskell programs.  ICFP '00. ttps://dl.acm.org/doi/10.1145/351240.351266

[2]: https://github.com/upenn-cis5520/05-quickcheck/blob/main/QuickCheck.hs

[3]: https://cseweb.ucsd.edu//classes/wi11/cse230/lectures/quickcheck.lhs
 -}

