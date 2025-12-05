{-# LANGUAGE BangPatterns #-}
module Intro where

import Prelude hiding (elem)
-- we can explicitly choose which functions to import from a module
import Data.List (foldl', tails) 

import Debug.Trace -- Useful for debugging

{- 

Introduction to Haskell
=======================
Haskell is a purely functional programming language with a strong, static type
system. Its key features include purity, laziness, and an expressive type system
that supports polymorphism and powerful abstractions such as type classes and
higher-kinded polymorphism.


Purity
------
Haskell is a pure functional language, which means that expressions in Haskell
are side-effect free. This characteristic allows for better reasoning about
code: expressions are referentially transparent, meaning that "equals can be
substituted with equals" without changing the program's behavior.

For example in the expression let x = f z in x + x, x can be substituted with
its definition to obtain (f z) + (f z) without changing the program's behavior.


Laziness
--------
Haskell employs lazy evaluation, which means expressions are evaluated only when
their results are needed. Arguments to functions are not evaluated when the
function is called but when their value is required. This is also known as
non-strict evaluation. Once evaluated, the values of expressions are memoized so
as to avoid duplicate computation.

The benefit of lazy evaluation is that computations are only performed when
absolutely necessary, avoiding redundant work. Also, lazy evaluation enables
working with infinite data structures (like streams), by computing only the
required portion of the structure on demand.

However, reasoning about performance become much harder as computation is
nonlocal. Also, suspended computations (known as thunks) may accumulate in
memory if not carefully managed, leading to unexpected memory consumption.


Type system
-----------
Haskell has a strong, static type system. Its basis is the Hindley-Milner type
system, with a few extensions.  

Type classes: A way to define an interface (set of functions/constraints) that
work for multiple types. Type classes provide a principled way to define
overloaded operators.

Higher-rank polymorphism: Haskell allows polymorphism over type operators which
is a feature that allows expressive and reusable abstractions.

Higher-rank polymorphism: By default, Haskell's type system only allows prenex
polymorphism (a.k.a. let-polymorphism). This means that type quantification in
polymorphic types can only happen at the outermost of the type. 

Higher-rank polymorphism allows function arguments to be polymorphic as well. A
rank-N type is type in which a universal quantifier can be at most N level deep
inside a function argument. For example, the following type is a rank-2 type:

(forall b, b -> (b, b)) -> Int -> Bool -> ((Int, Int), (Bool, Bool))

GHC has extensions for both rank-2 polymorphism (Rank2Types) and arbitrary rank
polymorphism (RankNTypes). 

With rank-2 polymorphic types, type inference remains decidable, but rank-N type
reconstruction becomes undecidable, and some explicit type annotations are
required in their presence.

Reference: https://wiki.haskell.org/Rank-N_types

Haskell Glossary 
----------------

ghc   : The Glasgow Haskell Compiler, the primary compiler for Haskell.

ghci  : GHC’s interactive environment (REPL)

cabal : Haskell's package manager and build system for managing project
dependencies.

Core  : GHC "desugars" Haskell into Core, a typed intermediate representation
which is a superset of System F
https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/compiler/hsc-main

Lazy evaluation : Expressions in Haskell are evaluated when needed and at most
once! (very rough description)

Monad : Just a monoid in the category of endofunctors (just kidding, see next
lecture).

Thunk : A suspended computation (a value which is not yet evaluated)  

Side Effects : None! Haskell ensures side effects are managed explicitly through
constructs like the IO monad.

-}

{-

Basic Types
------------

-}

-- A Haskell module is a list of definitions like the following ones. Even
-- though the type annotations are optional, they are strongly encouraged.

-- The type Integer is the type of arbitrarily large integer numbers
n1 :: Integer
n1 = 42

-- >>> n1
-- 42

-- The type Int is the type of word-sized integers, which is machine dependent. 
n1' :: Int
n1' = 42

-- >>> n1'
-- 42

-- Definitions don't have to be in order 
n3 :: Int
n3 = n2 + 21

n2 :: Int
n2 = 21

-- >>> n3
-- 42

-- Double precision floating point
f1 :: Double 
f1 = 123.4567

--- >>> f1
-- 123.4567

-- Booleans
b1 :: Bool
b1 = True && (False :: Bool) || (n2 == 42)

-- >>> b1
-- False

-- Strings
hello :: String 
hello = "Hello " ++ "world!"

-- >>> hello
-- "Hello world!"

hello' :: [Char]
hello' = hello

-- >>> hello'
-- "Hello world!"

-- Unit type
unit :: ()
unit = ()

-- >>> unit
-- ()

{-

Functions
---------

-}

-- In Haskell, functions is just a regular definition
add :: Integer -> Integer -> Integer
add = \x y -> x + y  -- This is an anonymous function

-- The above is equivalent to the following definition
add' :: Num a => a -> a -> a
add' x y = x + y

-- We may also define this function as follows (This is a very Haskellish thing to do)
add'' :: Integer -> Integer -> Integer
add'' = (+)

-- >>> add'' 41 1
-- 42

{- Infix and Prefix notations
   
In Haskell we can define infix operators, like +, -, etc. We defined them as
ordinary functions but their symbol is put in parentheses.

Generally, if we put an infix operator in parentheses, it becomes prefix. If we
put an prefix operator inside backticks then it becomes infix.
-}

-- Example: Lexicographic comparison of pairs
(<=|) :: (Int, Int) -> (Int, Int) -> Bool
(<=|) (x1, y1) (x2, y2) = x1 <= x2 || x1 == x2 && y1 <= y2

-- >>> (1,3) <=| (1, 5)
-- True

-- >>> (2,3) <=| (1, 4)
-- False

-- Every infix operator can be used as prefix and vise versa.

-- >>> (<=|) (1,3) (1, 4)
-- True

-- >>> 3 `add` 4
-- 7

{- Function composition 
  
   Haskell introduces an infix notation for composing functions: the '.' operator.
   Its type is (.) :: forall b c a. (b -> c) -> (a -> b) -> a -> c
   For example we can write the following 

-}

myodd :: Integer -> Bool
myodd = not . even

--- >>> myodd 42
-- False

-- f :: A -> A

-- (\x -> f x) :: A -> A

-- Point-free notation 

-- Writing functions without explicitly mentioning arguments is considered
-- idiomatic Haskell. This style typically involves composing partially applied
-- or unapplied functions. Additionally, combinators like const and flip are
-- often used to achieve concise and expressive definitions.


-- Examples:

addOneAndDouble :: Integer -> Integer
addOneAndDouble x = (x + 1) * 2

addOneAndDouble' :: Integer -> Integer
addOneAndDouble' = (* 2) . (+ 1)


-- >>> addOneAndDouble' 11
-- 24

-- This style can lead to obfuscation and code that is hard to understand, so it
-- must be used with caution

compf :: (b -> c1) -> (c1 -> c2) -> (a -> b) -> a -> c2
compf f g r = g . f . r

compf' :: (b -> c1) -> (c1 -> c2) -> (a -> b) -> a -> c2
compf' f = (. (f .)) . (.) -- what?



-- More fun examples here: https://wiki.haskell.org/Pointfree

{- Pattern matching -}
 
fib :: Integer -> Integer
fib 0 = 0 
fib 1 = 1
fib x = fib (x-1) + fib (x-2)

-- >>> fib 7
-- 13

-- We can also define this function using case analysis ...
fib' :: Integer -> Integer
fib' x = case x of
  0 -> 0
  1 -> 1
  _ -> fib' (x-1) + fib' (x-2)

-- >>> fib' 6
-- 8

-- ... or using "guards"
fib'' :: Integer -> Integer
fib'' x 
  | x == 0 = 0
  | x == 1 = 1
  | otherwise = fib'' (x-1) + fib'' (x-2)


-- Haskell is an indentation-sensitive language. For example, the following two
-- functions have a different meaning 

test1 :: Integer -> Integer -> Bool
test1 x y = 
  case x of 
    0 -> True 
    1 -> case y of 
      0 -> True
    _ -> False

-- >>> test1 3 1
-- False

test2 :: Integer -> Integer -> Bool
test2 x y = 
  case x of 
    0 -> True 
    1 -> case y of 
      0 -> True
      _ -> False

-- >>> test2 3 1
-- /Users/zoo/Repos/PL2/lectures/Haskell/src/Intro.hs:(239,3)-(243,16): Non-exhaustive patterns in case

-- Note, that both of these functions are partial, i.e., they are not defined for
-- all the values of their domain.

-- As a general guideline, all grouped expressions must be exactly aligned. This
-- includes cases and other constructs like let, where, and do blocks that we
-- will see later. 



{- 
Laziness
--------

Haskell is a lazy language. It has call-by-need semantics and arguments to
functions are evaluated at most once, and only when its needed. 

In Haskell, it is easy to define Short-circuit operators, wh. 
-}

and' :: Bool -> Bool -> Bool
and' False _ = False
and' True y = y


-- To check that `and'` uses indeed short-circuit evaluation we can use two 
-- special Haskell combinators: undefined and error, that always fail when 
-- they are evaluated. 

-- >>> :t error 
-- error :: HasCallStack => [Char] -> a

-- >>> :t undefined 
-- undefined :: HasCallStack => a

-- >>> and' False (error "unreachable")
-- False

-- >>> and' (error "boom") False
-- boom

-- >>> and' True undefined
-- Prelude.undefined

-- A non terminating function. 

-- We can define such a function and pass it around without observing any 
-- non termination, as long as its value is not explicitly needed
loop :: () -> a
loop _ = loop ()

--- >>> (\_ -> 42) (loop ())
-- 42

fst' :: (a, b) -> a
fst' (x, _) = x

-- >>> fst' ((\x -> x) ((42, 11), (undefined, error "unreachable")))
-- (42,11)

-- In Haskell, an expression whose value has not been explicitly needed yet
-- is represented by a thunk. A thunk is a heap-allocated data structure that
-- represents a suspended computation. Once evaluated, the thunk's value is
-- memoized, so subsequent uses don’t recompute it. 

-- The evaluation of a thunk is _forced_ when the value of the expression is
-- needed. This commonly happens when the expression is pattern-matched against
-- a constructor and the outmost constructor of the expression needs to be
-- known. Then the thunk is evaluated to what is called _weak-head normal form_:
-- an expression whose outermost is not a redex. 

-- A value in weak-head normal form (WHNF) is either:
-- - A fully evaluated value of a primitive type (Int, Char, etc.)
-- - A constructed value of an algebraic data type that consists of a
--   constructor applied to potentially unevaluated arguments.Applicative

-- For example (1+2, 3+4) is in WHNF, but (fst ((1,2),3)) is
-- not.

-- The point of WHNF is that the arguments of constructed values will not be
-- evaluated unless their value is also forced. When only the outermost
-- constructor is needed for computation then the arguments of the constructor
-- will remain thunks.

-- In order to express sharing of thunks, and avoid duplicate compulation,
-- expressions are internally represented using graphs instead of trees.  

-- Laziness has the benefit that avoids unnecessary computations by only
-- evaluating exactly what is needed. It also enables working with infinite data
-- structures like streams. However, it can lead to inefficiencies as thunk can
-- accumulate memory and create memory leaks (we explain this later with an
-- example). 

-- Sometimes, it is useful to control evaluation with one of the following operations.

-- seq: The seq operator forces evaluation of its first argument before returning the second

-- Bang patterns: A function argument annotated with ! is strict 

-- $!: Strict Application

-- >>> (error "boom") `seq` 42
-- boom

-- Once the evaluation of the outermost constructor of the thunk is forced,
-- which usually happens through pattern matching, the outermost constructor of
-- the thunk will be evaluated.  (unless they have been evaluated by some earlier use). We say the
-- expression is evaluated in _weak head normal form_.


{-

Structured Data
===============

Tuples
------
-}

-- We've already seen tuples. They can have an arbitrary number of components.

tup2 :: (Integer, Bool, Integer -> Bool)
tup2 = (42, True, even)


{-
Option Types
------------

The datatype Maybe in Haskell is used to model optional values. It has two constructors:

Just :: a -> Maybe a
Nothing :: Maybe a 

-}

-- Safe head function (fast-forward to lists)
hd :: [a] -> Maybe a
hd [] = Nothing
hd (x:_) = Just x

-- >>> hd [1,2,undefined]
-- Just 1

-- >>> hd []
-- Nothing

{-
Lists
-----

The list datatype in Haskell is denoted [a], where a is the type of the elements. 
It has two constructors

[]  :: [a]
(:) :: a -> [a] -> [a] 

-}

-- List ranges 

-- A convenient way of constructing lists is with list ranges. 
upto :: Integer -> [Integer]
upto n = [1..n]

-- >>> upto 10
-- [1,2,3,4,5,6,7,8,9,10]

-- One can also construct infinite ranges. If only finite prefixes need to be
-- evaluated then the computation can terminate.  

-- >>> take 5 [1..]
-- [1,2,3,4,5]

-- >>> take 5 $ drop 10 [1..]
-- [11,12,13,14,15]

range :: Int -> [Int]
range x = x : range (x + 1)

-- >>> take 5 (range 42)
-- [42,43,44,45,46]


-- Note: The $ operator is another common Haskell idiom and denotes infix
-- application. It is a convenient way to avoid parentheses around the last
-- argument of an application.

-- Manipulating list in Haskell with higher-order functions is a very common
-- programming pattern. Doing so with point-free notation is a quite common
-- idiom that can result in concise and elegant code (but sometimes difficult to
-- understand)

mapExample :: [Integer] -> [Bool]
mapExample = map (even . (+1))


-- >>> mapExample [1..4]
-- [True,False,True,False]


sum1 :: [Integer] -> Integer
sum1 = foldr (+) 0

sum2 :: [Integer] -> Integer
sum2 = foldl (+) 0

sum3 :: [Integer] -> Integer
sum3 = foldl' (+) 0

-- foldl' is a version of foldl that applies the operator in a strict way. This
-- forces the reduction of operands to WHNF and avoids creating intermediate
-- thunks. We will see how this can be useful.

-- >>> sum1 [1..10]
-- 55

-- >>> sum2 [1..10]
-- 55

-- >>> sum3 [1..10]
-- 55

-- The three functions return the same result, but have different behavior
-- regarding space consumption. In an ideal situation, we would like to do this
-- computation in constant space, after all we shouldn't use linear space for
-- this summation. 

-- In Haskell it is possible to do this with a list because lists are
-- constructed lazily. The list [1..n] will be generated as needed. Any list
-- elements that are no longer needed, are garbage collected. Therefore, it is
-- possible to have only a constant portion of the list expanded in the heap of
-- the program at each point. 

-- However, not all three functions achieve this. Let's analyze their behaviour. 

{-

  foldr (+) 0 [1..10]
= 1 + (foldr (+) 0 [2..10]) 
= 1 + (2 + foldr (+) 0 [3..10])
= 1 + (2 + (3 + foldr (+) 0 [4..10]))
....
= 1 + (2 + (3 + (4 + (5 + (6 + (7 + (8 + (9 + 10))))))))
= 55

-}

-- Because + is strict on both of its arguments, none of its applications can be
-- reduced at any point until the last element has been reached. Therefore the
-- thunks in this computation will take up linear space.

{-

  foldl (+) 0 [1..10]
= foldl (+) (0 + 1) [2..10]
= foldl (+) (0 + 1 + 2) [3..10]
= foldl (+) (0 + 1 + 2 + 3) [4..10]
= foldl (+) (0 + 1 + 2 + 3 + 4) [5..10]
... 
= foldl (+) (0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10) []
= 55

-} 

-- This computation is still expanded and takes linear space. However, in this
-- case there is no reason for the computation to be expanded! We could simply 
-- fully evaluate the accumulator at each step and reduce space usage. 

-- We can achieve this with foldl' that has a strict application of the operator.


{-

  foldl' (+) 0 [1..10]
= foldl' (+) 1 [2..10]
= foldl' (+) 3 [3..10]
= foldl' (+) 6 [4..10]
= foldl' (+) 10 [5..10]
... 
= foldl' (+) 55 []
= 55

-} 

-- Now the sum uses constant space!

-- There are however cases where the other versions of fold would have been more
-- efficient. 

-- In particular when the operator of the fold is lazy on its second argument, 
-- foldr can have significant performance gains.


trues :: [Bool]
trues = True:trues

-- >>> foldr (&&) True (False:trues)
-- False

elem :: (Eq a, Foldable t) => a -> t a -> Bool 
elem x = foldr (\y b -> x == y || b) False    

-- >>> elem 1 [1..]
-- True


-- One the other hand, foldl will have to reach the end of the list to compute
-- the result. This will cause the computation to diverge.

-- >>> foldl (&&) True (False:trues)


-- This fibonacci function uses constant space. Notice that next is strict on its arguments
fibl :: Integer -> Integer
fibl x = fst $ foldl' (\ c _ -> next c) (0,1) [1..x]
  where
    next (!p1,!p2) = (p1 + p2,p1)

-- This fib does not use constant space (for the same reasons as above)
fibl' :: Integer -> Integer
fibl' x = fst $ foldr (const next) (0,1) [1..x]
  where
    next (p1,p2) = (p1 + p2,p1)


-- Notice the where clause. It is similar to a let-binding but it comes after
-- the declaration of the function. It is a common syntactic idiom of Haskell.


-- List Comprehensions

-- We can write operations on list using a notation familiar from math:
-- comprehensions.

--- More examples 

filter' :: (a -> Bool) -> [a] -> [a]
filter' p xs = [ x | x <- xs, p x ]

-- >>> filter' (> 42) [1..50]
-- [43,44,45,46,47,48,49,50]

-- finds all Pythagorian triples up to n
pythag :: Integer -> [(Integer,Integer,Integer)]
pythag n =
  [(x,y,z) | x <- [1..n], y <- [x..n],
             z <- [y..n], x^2 + y^2 == z^2 ]

-- >>> pythag 17
-- [(3,4,5),(5,12,13),(6,8,10),(8,15,17),(9,12,15)]


qsort :: Ord a => [a] -> [a] -- What is Ord?
qsort [] = []
qsort (p:xs) =
  qsort [x | x <- xs, x < p] ++
  [p] ++ qsort [x | x <- xs, x >= p]

-- >>> qsort [1,9,5,4,2,8,10,11,5,42,100,21]
-- [1,2,4,5,5,8,9,10,11,21,42,100]


uniquePairs :: [a] -> [(a,a)]
uniquePairs xs = [(x,y) | (x:ys) <- tails xs, y <- ys]

-- >>> uniquePairs [1,9,5,4,2,8,10,11,5,42,100,21]
-- [(1,9),(1,5),(1,4),(1,2),(1,8),(1,10),(1,11),(1,5),(1,42),(1,100),(1,21),(9,5),(9,4),(9,2),(9,8),(9,10),(9,11),(9,5),(9,42),(9,100),(9,21),(5,4),(5,2),(5,8),(5,10),(5,11),(5,5),(5,42),(5,100),(5,21),(4,2),(4,8),(4,10),(4,11),(4,5),(4,42),(4,100),(4,21),(2,8),(2,10),(2,11),(2,5),(2,42),(2,100),(2,21),(8,10),(8,11),(8,5),(8,42),(8,100),(8,21),(10,11),(10,5),(10,42),(10,100),(10,21),(11,5),(11,42),(11,100),(11,21),(5,42),(5,100),(5,21),(42,100),(42,21),(100,21)]

-- Primes sieve 
primes :: [Integer]
primes = sieve [2..]
  where 
    sieve (p:ns) = p : sieve [n | n <- ns, n `mod` p /= 0]


-- >>> take 5 primes
-- [2,3,5,7,11]

-- [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

-- Fib, again 

fibi :: [Integer]
fibi  = 0 : fibi1 

fibi1 :: [Integer]
fibi1 = 1 : fibi2

fibi2 :: [Integer]
fibi2 = addf fibi fibi1
  where addf (x:xs) (y:ys) = (x+y) : addf xs ys
        addf _ _           = error "unreachable"

-- >>> take 10 fibi
-- [0,1,1,2,3,5,8,13,21,34]

consumer :: (Eq t, Num t, Show a) => [a] -> t -> [Char]
consumer stream n =
  if n == 1 then show x
  else show x ++ ", " ++ consumer xs (n-1)
    where 
      x:xs = stream

-- >>> consumer fibi 10
-- "0, 1, 1, 2, 3, 5, 8, 13, 21, 34"


{-
User Defined Data Types
-----------------------
-}

data Tree a = Leaf | Node a (Tree a) (Tree a)

{-

Interacting with the World with IO
----------------------------------

The IO monad is a mechanism for handling side effects in Haskell while
preserving its purity.  Any computation that interacts with the "outside world"
by performing input and output operations must be inside of an IO type. That is,
the IO type separates impure actions (e.g., reading a file) from pure code.

Examples of IO types:

- IO String : An IO computation that, when executed, produces a String.
- IO (): An IO computations that produces unit

IO computations can be sequenced inside a so-called "do block". Examples of its
syntax are below. 

Note: The IO type and its syntax are instances of a more general pattern called
monads. We will learn more about monads in the next lecture.

Some common IO actions:

-- Prints a string with a newline. 
putStrLn :: String -> IO () 

-- Reads a line of input 
getLine :: IO String 

-- Reads the contents of a file 
readFile :: FilePath -> IO String 

-- Writes a string to a file 
writeFile :: FilePath -> String -> IO ()
-}


-- some examples from https://github.com/upenn-cis5520/01-basics/blob/main/Basics.hs

helloAgain :: IO ()
helloAgain = putStr "Hello World!\n"

many :: IO ()
many = do
  putStr "Hello" -- each line in the sequence
  putStr " World!" -- must be an IO action
  putStr "\n"

-- Note that actions is a do block must be correctly indented.

query :: IO ()
query = do
  putStr "What is your name? "
  n <- getLine -- this syntax binds the result of the getLine computation to n
  putStrLn ("Welcome to PL2 " ++ n)

query2 :: IO String
query2 = do
  putStr "What is your name? "
  n <- getLine
  return n

readSomeLines :: String -> IO ()
readSomeLines f = do
  c <- readFile f
  let c' = unlines . take 5 . lines $ c -- a pure computation inside an IO block
  putStrLn c'


-- Haskell offers an escape mechanism from the IO monad. This is not a safe
-- feature, as it brakes encapsulation of side effects.

-- unsafePerformIO :: IO a -> a 

{-

Debugging
---------

Because of purity and lazy evaluation, debugging Haskell programs can be hard.
Haskell provides a library called Debug.Trace that offers a few functions that
can be helpful with debugging. Some useful functions are below.

-- The function trace outputs the trace message given as its first argument, 
-- before returning the second argument as its result 
trace     :: String -> a -> a

-- Note that trace is not a pure functional program: it has a side-effect (and 
-- it is not even defined inside IO!) However it is very useful for debugging.


-- Like trace, but uses show on the argument to convert it to a String.
traceShow :: Show a => a -> b -> b

The monadic counterparts of the above functions.

traceM     :: Monad m => String -> m ()
traceShowM :: (Monad m, Show a) => a -> m ()

-}

-- Examples 

query2Dbg :: IO String
query2Dbg = do
  putStr "What is your name? "
  n <- getLine
  traceM "Read the line:"
  traceM n
  return n

qsortDbg :: (Ord a, Show a) => [a] -> [a] -- What is Ord?
qsortDbg [] = []
qsortDbg (p:xs) = lt ++ [p] ++ ge
  where 
    lt = qsortDbg [x | x <- xs, x < p]
    ge = qsortDbg [x | x <- xs, x >= p]
