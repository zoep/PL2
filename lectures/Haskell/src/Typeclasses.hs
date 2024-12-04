{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}

module Typeclasses where

import Prelude hiding (fail, elem)
import qualified Data.Map as M
import Data.Foldable hiding (elem)

{- 

Typeclasses
-----------

-}
-- If we let Haskell infer the type of the following function, it will not be
-- the one we wrote for it in the previous section, but something more general.
  
add :: Num a => a -> a -> a
add = (+)

-- The above type tells us that add works for any type, as long as this type
-- implements the [Num] type class. 

-- What is a type class??

-- A type class is a set of operations, you can think of it as a record, that
-- can be implemented by various types. It defines an interface that can be
-- implemented by various types in an ad-hoc way. 

-- Then when writing polymorphic functions, one can put constraints on
-- polymorhic types that they should implement a particular type class.

-- Haskell implements overloading, which is the ability to define an operation
-- for more than one types, using type classes. 

-- The Num typeclass defines operations line _, -, * for numeric types. Every
-- type that implements the typeclass, i.e., provides an instance of the type
-- class, should define this operations.

-- Another useful class is Eq, that defined equality and inequality.

{- Its definition is the following:


class Eq a where
    (==)        :: a -> a -> Bool
    (/=)        :: a -> a -> Bool

    x /= y      = not (x == y) -- default implementation
-}

-- Most build-in datatype in Haskell provide instances for Eq But when we are
-- defining our own types, we may want them to provide instances of such
-- classes.

data Tree a = Leaf | Node a (Tree a) (Tree a)


-- Type class instance for Tree a
-- Eq a is a type class contraint that the abstract type a must implement Eq
instance Eq a => Eq (Tree a) where
    (==) :: Eq a => Tree a -> Tree a -> Bool
    Leaf          == Leaf             = True
    Node a1 t1 t2 == Node a1' t1' t2' = a1 == a1' && t1 == t1' && t2 == t2'
    _ == _ = False 
    
tree1 :: Tree Int
tree1 = Node 42 (Node 17 Leaf Leaf) Leaf

tree2 :: Tree Int 
tree2 = Node 17 (Node 11 Leaf Leaf) Leaf

--- >>> tree1 == tree2
-- False

--- >>> tree1 == tree1
-- True

-- Haskell lets us use the keyword deriving to automatically derive some
-- instances. In Haskell 98, the only derivable classes are Eq, Ord, Enum, Ix,
-- Bounded, Read, and Show. Various language extensions extend this list.

-- For example:

data Tree' a = Leaf' | Node' a (Tree' a) (Tree' a)
  deriving (Eq, Show)

tree1' :: Tree' Int
tree1' = Node' 42 (Node' 17 Leaf' Leaf') Leaf'

tree2' :: Tree' Int 
tree2' = Node' 17 (Node' 11 Leaf' Leaf') Leaf'

--- >>> tree1' == tree2'
-- False

--- >>> tree1' == tree1'
-- True

-- The Show typeclass provides one function show :: a -> String that converts
-- its input to a string. 

-- >>> show tree1'
-- "Node' 42 (Node' 17 Leaf' Leaf') Leaf'"

-- However, these derived instances might not always be the desired ones.

-- For example, consider the following simple AST that contains information
-- about the position of the node in the source code. When we compare
-- expressions, we would like to ignore this

-- The source code position
type Posn = (Int,Int) -- a type synonym

data Exp = Var Posn String 
         | App Posn Exp Exp
         | Abs Posn String Exp
         | Num Posn Int
         | Add Posn Exp Exp 
   deriving Show

instance Eq Exp where
    (==) :: Exp -> Exp -> Bool
    Var _ x     == Var _ x'      = x == x'
    App _ e1 e2 == App _ e1' e2' = e1 == e1' && e2 == e2'
    Abs _ x e   == Abs _ x' e'   = x == x' && e == e'
    Num _ n     == Num _ n'      = n == n'
    Add _ e1 e2 == Add _ e1' e2' = e1 == e1' && e2 == e2'
    _ == _ = False

-- >>> (Add (0,2) (Num (0,0) 3) (Num (0,4) 4)) == (Add (1,2) (Num (1,0) 3) (Num (1,4) 4))
-- True

-- Another common typeclass is the Ord typeclass that provides comparison
-- functions.

-- Using Ord we can write a generic quicksort function

qsort :: Ord a => [a] -> [a] -- What is Ord?
qsort [] = []
qsort (p:xs) =
  qsort [x | x <- xs, x < p] ++
  [p] ++ qsort [x | x <- xs, x >= p]


{- To summarize we've see four very standard type classes in Haskell

- Ord used for totally ordered data types
- Show allow data types to be printed as strings
- Eq used for data types supporting equality
- Num functionality common to all kinds of numbers

Next, we will move to another very common Haskell typeclass: Monads.
-}

{- 

Monads
------

Monads can be seen as a generic interface to various types of computations.

Monads can be used to model stateful computation and ensure that all
"side-effects" remain inside the monad (like the IO monad.). 


The interface that must be implemented by a monad is 

class Monad (m :: Type -> Type) where    
  return :: a -> m a
  -- monadic bind
  (>>=)  :: m a -> (a -> m b) -> m b

Note, that the monad is not parametric on a type, but a type operator. As we
will see, this can be a List, a Maybe, or a "side-effect" type like IO.

In addition to the interface, monads should satisfy the _monad laws_:

return a >>= k = k a
m >>= return = m 
m >>= (\x -> k x >>= h)  =  (m >>= k) >>= h

-}

-- The Maybe Monad

{- The implementation of the Maybe monad, provided by the Haskell standard library 
   is the following:

instance Monad Maybe where
   return      :: a -> Maybe a
   return         =  Just

   (>>=)       :: Maybe a -> (a -> Maybe b) -> Maybe b
   Nothing  >>= _ =  Nothing
   (Just x) >>= f =  f x

-}

-- We also provide some "actions" that are specific to this monad
fail :: Maybe a
fail = Nothing

-- We can use the Maybe monad to avoid boilerplate code when writing recursive
-- functions that return optional types. 

-- For example we can write an interpreter for lambda calculus, which is a
-- partial function, without having to match at the result type all the time.

subst :: String -> Exp -> Exp -> Exp 
subst x t' t@(Var _ y)    = if x == y then t' else t
subst x t' t@(Abs p y t1) = if x == y then t else Abs p y (subst x t' t1)
subst x t' (App p t1 t2)  = App p (subst x t' t1) (subst x t' t2)
subst _ _ t@(Num _ _)     = t
subst x t' (Add p t1 t2)  = Add p (subst x t' t1) (subst x t' t2)

psn :: Posn
psn = (0,0)

exp1 :: Exp
exp1 = subst "x" (Abs psn "z" (Var psn "z")) (App psn (Var psn "x") (Add psn (Num psn 1) (Num psn 2)))

-- >>> exp1
-- App (0,0) (Abs (0,0) "z" (Var (0,0) "z")) (Add (0,0) (Num (0,0) 1) (Num (0,0) 2))

eval :: Exp -> Maybe Exp
eval (Var _ _) = fail
eval (Abs p x t) = return (Abs p x t)  
eval (App _ t1 t2) = 
  eval t1 >>= (\v -> 
    case v of
      Abs _ x t -> 
        eval t2 >>= (\v2 ->
        eval (subst x v2 t))
      _ -> fail)
eval (Num p n) = return (Num p n)
eval (Add p t1 t2) = 
  eval t1 >>= (\v1 ->
  eval t2 >>= (\v2 ->
  case (v1, v2) of 
    (Num _ n1, Num _ n2) -> return $ Num p (n1 + n2)
    _ -> Nothing))

-- >>> eval exp1
-- Just (Num (0,0) 3)

-- This already feels all lot like sequencing computation. Haskell provides the
-- do notation to makes this sequencing feel even more natural. 

-- Do notation

{- 

A monadic bind operation 

m >>= \x -> m' 

in do notation becomes 

x <- m;
m'

This notation, which resembles an imperative program, must be written inside a
do block. The following examples domonstrates this.  

-}


-- 

eval' :: Exp -> Maybe Exp
eval' (Var _ _) = fail
eval' (Abs p x t) = return (Abs p x t)  
eval' (App _ t1 t2) = do
  v <- eval' t1;
  case v of
    Abs _ x t -> do
      v2 <- eval' t2;
      eval (subst x v2 t)
    _ -> fail
eval' (Num p n) = return (Num p n)
eval' (Add p t1 t2) = do 
  v1 <- eval' t1;
  v2 <- eval' t2;
  case (v1, v2) of 
    (Num _ n1, Num _ n2) -> return $ Num p (n1 + n2)
    _ -> fail


-- >>> eval' exp1
-- Just (Num (0,0) 3)

-- The Reader Monad

-- data Val = Clo Env String Exp
--          | VNum Int

-- type Env = M.Map String Val

-- data Reader env a = Rd (env -> a)

-- instance Monad (Reader env) where 

--    return      :: a -> Reader env a
--    return  a = Rd (\_ -> a)

--    (>>=)       :: Reader env a -> (a -> Reader env b) -> Reader env b
--    (Rd m) >>= f   =  Rd (\env -> let x = m env in 
--                                  let Rd r = f x in r env)




elem :: (Eq a, Foldable t) => a -> t a -> Bool 
elem x = foldr (\y b -> x == y || b) False    

-- >>> elem 1 [42]
-- False


-- test1 :: Functor f => (a -> b) -> f a -> f b
-- test1 = fmap 

-- class Eq a where
--   (==) :: a -> a -> Bool

-- eval' :: Exp -> Reader Env Exp
-- eval' (Var _ _) = fail
-- eval' (Abs p x t) = return (Abs p x t)  
-- eval' (App _ t1 t2) = do
--   env <- read ;; 
--   v <- eval' t1;
--   case v of
--     Abs _ x t -> do
--       v2 <- eval' t2;
--       eval (subst x v2 t)
--     _ -> fail
-- eval' (Num p n) = return (Num p n)
-- eval' (Add p t1 t2) = do 
--   v1 <- eval' t1;
--   v2 <- eval' t2;
--   case (v1, v2) of 
--     (Num _ n1, Num _ n2) -> return $ Num p (n1 + n2)
--     _ -> fail


-- Generic Monad Functions 

-- mapM :: (a -> m b) -> t a -> m (t b)
-- sequence :: (Traversable t, Monad m) => t (m a) -> m (t a)
-- liftM :: Monad m => (a1 -> r) -> m a1 -> m r
-- liftM2 :: Monad m => (a1 -> a2 -> r) -> m a1 -> m a2 -> m r
  

newtype Reader env a = Reader { runReader :: env -> a }

instance Functor (Reader env) where
  fmap f r = Reader (f . runReader r)

instance Applicative (Reader env) where
  pure x                   = Reader (\_ -> x)
  Reader fe <*> Reader ae  = Reader (\e -> fe e (ae e))

instance Monad (Reader env) where
  (>>=) :: Reader env a -> (a -> Reader env b) -> Reader env b
  x >>= f  = Reader $ \e -> let x' = runReader x e in runReader (f x') e

ask :: Reader env env
ask = Reader (\e -> e)

-- >>> elem 1 [42,2]
-- False

newtype State state a = State { runState :: state -> (state, a) }

instance Functor (State state) where
  fmap f st = State (\s -> let (s', a) = runState st s in (s', f a))

instance Applicative (State state) where
  pure x                 = State (\s -> (s,x))
  State fs <*> State as  = State (\s -> 
      let (s', f) = fs s in
      let (s'', a) = as s' in (s'', f a))

instance Monad (State state) where
  (>>=) :: State state a -> (a -> State state b) -> State state b
  x >>= f = State $ \s -> let (s', x') = runState x s in runState (f x') s'

get :: State state state
get = State (\s -> (s,s))

put :: state -> State state ()
put s = State (\_ -> (s,()))