{-# LANGUAGE InstanceSigs #-}

module Typeclasses where

import Prelude hiding (fail, elem)
import qualified Data.Map as M
import Control.Monad hiding (fail)
import Control.Monad.Trans
import Debug.Trace
import Test.QuickCheck.Monadic (run)

{-

Type Classes
-------------

If we let Haskell infer the type of the following function, it will not be
the one we wrote for it in the previous section, but something more general.

-}

add :: Num a => a -> a -> a
add = (+)

{-

The above type tells us that add works for any type `a`, as long as this type
implements the [Num] type class.

What is a type class?

A type class is a set of operations (functions and constants), that must be
implemented by any type that is an _instance_ of the type class. A type class
defines a common interface

Then when writing polymorphic functions, one can put constraints on
polymorphic types that they should implement a particular type class. This is
called a type class constraint. Then the function can access all the
operations of the type class.

Haskell implements overloading, which is the ability to define an operation
for more than one types, using type classes.

The Num type class defines operations like +, -, * for numeric types. Every
type that implements the type class (i.e. provides an instance of the type
class) should define these operations.

Another useful class is Eq, that defines equality and inequality.
Its definition in Haskell library is the following:


class Eq a where
    (==)        :: a -> a -> Bool
    (/=)        :: a -> a -> Bool

    x /= y      = not (x == y) -- default implementation


The definition of inequality has a default implementation that
will be used if the instance does not redefine the operation.

Most built-in datatypes in Haskell provide instances for Eq but when we are
defining our own types, we may want to provide instances of such
classes.

-}

data Tree a = Leaf | Node a (Tree a) (Tree a)

-- The type class instance for Tree a, has a type class constraint that the
-- type a must implement Eq

instance Eq a => Eq (Tree a) where
    (==) :: Tree a -> Tree a -> Bool
    Leaf          == Leaf             = True
    Node a1 t1 t2 == Node a1' t1' t2' = a1 == a1' && t1 == t1' && t2 == t2'
    _             == _                = False

tree1 :: Tree Int
tree1 = Node 42 (Node 17 Leaf Leaf) Leaf

tree2 :: Tree Int
tree2 = Node 17 (Node 11 Leaf Leaf) Leaf


-- >>> (42 ==) <$> tree1
-- Node True (Node False Leaf Leaf) Leaf

--- >>> tree1 == tree2
-- False

--- >>> tree1 == tree1
-- True

-- Haskell lets us use the keyword `deriving` to automatically derive some
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

-- The Show type class provides one function show :: a -> String that converts
-- its input to a string.

-- >>> show tree1'
-- "Node' 42 (Node' 17 Leaf' Leaf') Leaf'"

-- -- These derived instances might not always be the desired ones.

-- For example, consider the following simple AST that contains information
-- about the source code position of each node in the source AST. When we
-- compare expressions, we would like to ignore this.


-- The source code position
type Posn = (Int,Int) -- [type] declares a type synonym

data Exp = Num Posn Int
         | Add Posn Exp Exp
         | Sub Posn Exp Exp
         | Mul Posn Exp Exp
         | Div Posn Exp Exp
   deriving Show

-- If we derive the Eq instance, it will compare the positions as well.
-- Instead, we can provide our own instance that ignores the positions.

instance Eq Exp where
    (==) :: Exp -> Exp -> Bool
    Num _ n     == Num _ n'      = n == n'
    Add _ e1 e2 == Add _ e1' e2' = e1 == e1' && e2 == e2'
    Sub _ e1 e2 == Sub _ e1' e2' = e1 == e1' && e2 == e2'
    Mul _ e1 e2 == Mul _ e1' e2' = e1 == e1' && e2 == e2'
    Div _ e1 e2 == Div _ e1' e2' = e1 == e1' && e2 == e2
    _ == _ = False

-- >>> (Add (0,2) (Num (0,0) 3) (Num (0,4) 4)) == (Add (1,2) (Num (1,0) 3) (Num (1,4) 4))
-- False

-- Another common typeclass is the Ord typeclass that provides comparison
-- operations.

-- Using Ord we can write a generic quicksort functionz

qsort :: Ord a => [a] -> [a] -- What is Ord?
qsort [] = []
qsort (p:xs) =
  qsort [x | x <- xs, x < p] ++
  [p] ++ qsort [x | x <- xs, x >= p]


{-

To summarize, we've seen four very standard type classes in Haskell:

- Ord  : provides total orderings on data types
- Show : allows data types to be printed as strings
- Eq   : provides (in)equality operations
- Num  : provides functionality common to all kinds of numbers

Next, we will move to another very common Haskell type class: Monads.
-}


{- Functors -}

{- A Functor is a type class that represents types that can be mapped over.
   The functor type class is defined as follows:

class Functor f where
    fmap :: (a -> b) -> f a -> f b

   The type constructor f must take one type argument. The fmap function
   takes a function from a to b, and a value of type f a, and returns a value
   of type f b, by applying the function inside the structure f.

   For example, the List type constructor is an instance of Functor:

instance Functor [] where
    fmap :: (a -> b) -> [a] -> [b]
    fmap _ []     = []
    fmap f (x:xs) = f x : fmap f xs


Functors must satisfy the following laws:

fmap id = id

fmap (g . h) = fmap g . fmap h

These ensure that fmap preserves the structure of the functor and the only thing that
fmap does is to apply the function to the elements inside the structure.

-}

-- We can write a Functor instance for our Tree type:
instance Functor Tree' where
  fmap :: (a -> b) -> Tree' a -> Tree' b
  fmap _ Leaf'         = Leaf'
  fmap f (Node' a l r) = Node' (f a) (fmap f l) (fmap f r)


-- >>> fmap (*2) tree1'
-- Node' 84 (Node' 34 Leaf' Leaf') Leaf'

{-

Monads
------

Monads are a very important type class in Haskell and functional programming in
general. They provide a way to sequence computation that take place inside the
context of a type constructor m.

A monad is more powerful than a functor, as it provides not only a way to map
functions over values inside the context, but also a way to sequence
computations that produce values inside the context.

Monads can be seen as programmable semicolons, that let us define how to
sequence computations. Thus, monads


The interface of a monad can be used to simulate an imperative programming style
in purely functional languages by hiding a lot of boilerplate code under the
hood (i.e., the monadic interface).

Thus, it is easier to write code that manipulates state, throws errors, models
nondeterminism, etc.

Monads can also be used to encapsulate truly impure code and keep it separate
from the pure language fragment (like the IO monad).

The interface defined by a monad is the following.

class Monad (m :: Type -> Type) where
  -- encapsulate a pure computation in a monadic one
  return :: a -> m a
  -- sequence two monadic computations
  (>>=)  :: m a -> (a -> m b) -> m b


In addition to the interface, monads should satisfy the _monad laws_:

-- left identity
return a >>= k = k

-- right identity
m >>= return = m

-- associativity
m >>= (\x -> k x >>= h)  =  (m >>= k) >>= h

The monad laws ensure that the sequencing of computations behaves in a canonical way:

- Left identity ensures that if we encapsulate a pure value and then
  sequence it with a computation, it is the same as just running the computation
  on the value, i.e., no extra effects are introduced by return or bind.

- Right identity ensures that sequencing a computation with return does not
  change the computation, ensuring again that return does not introduce any extra
  effects.

- Associativity ensures that the order of sequencing does not matter, i.e., we
  can group computations in any way we like without changing the result.


Note: As of 2017, Haskell require every Monad to also be an Applicative
instance, and every Applicative to also have a Functor instance. So in the code
below, we also provide these instances.

-}

-- The Maybe Monad

{- The implementation of the Maybe monad, provided by the Haskell standard library
   is the following:

instance Monad Maybe where
   return      :: a -> Maybe a
   return      =  Just

   (>>=)       :: Maybe a -> (a -> Maybe b) -> Maybe b
   Nothing  >>= _ =  Nothing
   (Just x) >>= f =  f x

-}

-- There is also a "monadic action" specific to this monad
fail :: Maybe a
fail = Nothing

-- We can use the Maybe monad to avoid boilerplate code when writing recursive
-- functions that return optional types.

-- For example we can write an interpreter for a simple arithmetic language with
-- runtime errors (e.g., division by zero) without having to check for errors at
-- each step. The monadic bind operator will take care of propagating errors for us.


eval :: Exp -> Maybe Int
eval (Num p n) = return n
eval (Add p t1 t2) =
  eval t1 >>= (\v1 ->
  eval t2 >>= (\v2 ->
  return $ v1 + v2))
eval (Sub p t1 t2) =
  eval t1 >>= (\v1 ->
  eval t2 >>= (\v2 ->
  return $ v1 - v2))
eval (Mul p t1 t2) =
  eval t1 >>= (\v1 ->
  eval t2 >>= (\v2 ->
  return $ v1 * v2))
eval (Div p t1 t2) =
  eval t1 >>= (\v1 ->
  eval t2 >>= (\v2 ->
    if v2 == 0 then fail
    else return $ v1 `div` v2))


exp1 :: Exp
exp1 = Mul (0,0) (Num (0,0) 6) (Add (0,0) (Num (0,0) 4) (Num (0,0) 3))


-- >>> eval exp1
-- Just 42


{--

Do notation
-----------

This already feels all lot like sequencing imperative code. Haskell provides a
"do notation" to makes this sequencing feel even more natural.

A monadic bind operation

m >>= \x -> m'

can be written with do notation as:

do
  x <- m;
  m'

This notation, which resembles an imperative program, must be written inside a
do block. The following example demonstrates this.

-}


-- eval with do notation

eval' :: Exp -> Maybe Int
eval' (Num _ n) = return n
eval' (Add _ t1 t2) = do
  v1 <- eval' t1
  v2 <- eval' t2
  return $ v1 + v2
eval' (Sub _ t1 t2) = do
  v1 <- eval' t1
  v2 <- eval' t2
  return $ v1 - v2
eval' (Mul _ t1 t2) = do
  v1 <- eval' t1
  v2 <- eval' t2
  return $ v1 * v2
eval' (Div _ t1 t2) = do
  v1 <- eval' t1
  v2 <- eval' t2
  if v2 == 0 then fail
  else return $ v1 `div` v2

-- >>> eval' exp1
-- Just 42

-- >>> eval' (Div (0,0) (Num (0,0) 1) (Num (0,0) 0))
-- Nothing


{-

Generic Monad Functions
------------------------

There are several monadic combinators that let us manipulate and sequence monadic computation.
Some examples are:

-- Map each element of a structure to a monadic action, evaluate these actions from left to
-- right, and collect the results.
mapM :: (Traversable t, Monad m) => (a -> m b) -> t a -> m (t b)

-- Evaluate each monadic action in the structure from left to right, and collect the results.
sequence :: (Traversable t, Monad m) => t (m a) -> m (t a)

-- Lift a pure function to a monadic one
liftM :: Monad m => (a1 -> r) -> m a1 -> m r

-- Lift a pure function with two arguments to a monadic one
liftM2 :: Monad m => (a1 -> a2 -> r) -> m a1 -> m a2 -> m r

You can find more monadic combinators here: https://hackage.haskell.org/package/base/docs/Control-Monad.html
-}


-- As an excercise, you can try to implement some of these combinators yourself.

-- Here is the implementation of sequence (without using Traversable, just list):

sequence' :: Monad m => [m a] -> m [a]
sequence' [] = return []
sequence' (m:ms) = do
    as <- sequence' ms
    a <- m
    return $ a:as


{-

The Reader Monad
----------------

The Reader monad (also called the Environment monad) encapsulates a computation
that reads values from a shared environment. Essentially a Reader monad, is a
function from the type of environment to the result type. The computation can
ask for the value of the environment and execute subcomputations in a modified
environment.
-}

newtype Reader env a = Reader { runReader :: env -> a }

instance Functor (Reader env) where
  fmap f r = Reader (f . runReader r)

instance Applicative (Reader env) where
  pure x                   = Reader (\_ -> x)
  Reader fe <*> Reader ae  = Reader (\e -> fe e (ae e))

instance Monad (Reader env) where
  -- by default, return is defined as the pure method of the Applicative type class

  (>>=) :: Reader env a -> (a -> Reader env b) -> Reader env b
  x >>= f  = Reader $ \e -> let x' = runReader x e in runReader (f x') e

-- Return the value of the environment
ask :: Reader env env
ask = Reader (\e -> e)

-- Execute the computation provided as a second argument in a modified
-- environment
local :: (env -> env) -> Reader env a -> Reader env a
local f (Reader m) = Reader (m . f)


-- For example, we can write an interepreter for a simple lambda calculus
-- with variables and function application using the Reader monad to model
-- the environment.

type Env = M.Map String Value

data Value = VNum Integer
           | VClo Env String Term
  deriving (Show, Eq)

data Term = TVar Posn String
          | TAbs Posn String Term
          | TApp Posn Term Term
          | TInt Posn Integer
          | TAdd Posn Term Term
  deriving (Show, Eq)


evalTerm :: Term -> Reader Env Value
evalTerm (TVar _ x) = do
  env <- ask
  case M.lookup x env of
    Just v  -> return v
    Nothing -> error $ "Unbound variable: " ++ x
evalTerm (TAbs _ x t) = do
  env <- ask
  return (VClo env x t)
evalTerm (TApp _ t1 t2) = do
  v <- evalTerm t1
  case v of
    VClo cenv x t -> do
      v2 <- local (\_ -> cenv) (evalTerm t2)
      local (M.insert x v2) (evalTerm t)
    _ -> error "Trying to apply a non-function"
evalTerm (TInt _ n) = return $ VNum n
evalTerm (TAdd _ t1 t2) = do
  v1 <- evalTerm t1
  v2 <- evalTerm t2
  case (v1, v2) of
    (VNum n1, VNum n2) -> return $ VNum (n1 + n2)
    _ -> error "Trying to add non-numbers"


term :: Term
term = TApp (0,0)
         (TAbs (0,0) "x"
           (TAdd (0,0)
             (TVar (0,0) "x")
             (TInt (0,0) 1)))
         (TInt (0,0) 41)


-- >>> runReader (evalTerm term) M.empty
-- VNum 42

{-

The State Monad
----------------

The State monad encapsulates computations that read and write from a shared
state. Essentially a state monad is a computation that is written in state
passing style, i.e., state -> (state, a) for some result type a, and hides th
explicit state threading under the monadic operations.

-}


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

-- Monadic actions specific to the State monad

get :: State state state
get = State (\s -> (s,s))

put :: state -> State state ()
put s = State (\_ -> (s,()))


-- Example: Fibonacci as a stateful function, various versions

type FibState = State (Integer, Integer) ()


fibSt :: Integer -> FibState
fibSt n =
  forM_ [1..n] (\_ -> do
    (prev, curr) <- get
    put (curr, prev+curr))

fibN :: Integer -> Integer
fibN n = case fibSt n of
  State fibst ->
    let ((prev, curr), _) = fibst (0,1) in
    prev

-- >>> fibN 8
-- 21


mapM' :: Monad m => (a -> m b) -> [a] -> m [b]
mapM' _ [] = return []
mapM' f (x:xs) = do
    y <- f x
    ys <- mapM' f xs
    return $ y:ys


fibState :: Integer -> FibState
fibState 0 = return ()
fibState n = do
  fibState (n-1)
  (cur, prev) <- get
  put (cur + prev, cur)

computeFib :: Integer -> Integer
computeFib n = fst . fst $ runState (fibState n) (0,1)

-- Or, in point-free style:
-- computeFib' = fst . fst . flip runState (0,1) . fibState

-- We can also write this as a "for loop"

fibFor :: Integer -> State (Integer, Integer) ()
fibFor n =
  forM_ [1..n] (\_ -> do
    (cur, prev) <- get
    put (cur+prev, cur))


computeFib' :: Integer -> Integer
computeFib' n = fst . fst $ runState (fibFor n) (0,1)

-- Or, in point-free style:
-- computeFib' = fst . fst . flip runState (0,1) . fibFor

-- >>> computeFib 9
-- 34

-- >>> computeFib' 9
-- 34

fibNFor :: Integer -> Integer
fibNFor n = snd . flip runState (0,1) $ do

  forM_ [0..(n-1)] $ \_ -> do
    (curr,prev) <- get
    put (curr+prev,curr)

  (curr,_) <- get
  return curr


-- Stack based evaluator for arithmetic expressions written in a state monad

type StackSt =  State [Int] ()

evalStackBop :: (Int -> Int -> Int) -> StackSt
evalStackBop op = do
    stack <- get
    case stack of
      (x:y:rest) -> put (x `op` y:rest)
      _          -> error "Stack underflow"


evalStack :: Exp -> StackSt
evalStack (Num _ n) = do
    stack <- get
    put (n:stack)
evalStack (Add _ t1 t2) = do
    evalStack t1
    evalStack t2
    evalStackBop (+)
evalStack (Sub _ t1 t2) = do
    evalStack t1
    evalStack t2
    evalStackBop (+)
evalStack (Mul _ t1 t2) = do
    evalStack t1
    evalStack t2
    evalStackBop (*)
evalStack (Div _ t1 t2) = do
    evalStack t1
    evalStack t2
    evalStackBop div

evalStackTop :: Exp -> Int
evalStackTop exp =
  let (stack, _) = runState (evalStack exp) [] in
  case stack of
    (v:_) -> v
    _     -> error "Empty stack after evaluation"


-- >>> evalStackTop exp1
-- 42


-- >>> fibNFor 9
-- 34


{- Monad Transformers -}

-- Often, it is useful to combine two monads together. For example, in the
-- environment based interpreter we might want to use a Maybe monad inside the
-- state in order to do error handling.

-- One option is to build a new type, encapsulating a computation with type
-- `state -> (state, Maybe a)` and make it and instance of Monad.

-- One other option, is to make monad definitions parametric an another
-- underlying monad, and make them add functionality on top of it. These
-- constructions are called monad transformers.

-- The simple non-transformer versions can be then be obtain by using the Id
-- (identity) monad as the base monad.


-- State transformers

newtype StateT s m a = StateT { runStateT :: s -> m (s, a) }

instance Monad m => Monad (StateT state m) where
  return :: a -> StateT state m a
  return x = StateT (\s -> return (s,x))

  (>>=) :: StateT state m a -> (a -> StateT state m b) -> StateT state m b
  x >>= f = StateT $ \s -> do
    (s', x') <- runStateT x s
    runStateT (f x') s'


instance (Monad m) => Applicative (StateT s m) where
  pure = return
  (<*>) :: Monad m => StateT s m (a -> b) -> StateT s m a -> StateT s m b
  (<*>) = ap

instance (Monad m) => Functor (StateT s m) where
  fmap = liftM

instance MonadTrans (StateT s) where
  lift :: (Monad m) => m a -> StateT s m a
  lift ma = StateT $ \s -> do
    r <- ma
    return (s, r)

getT :: Monad m => StateT state m state
getT = StateT (\s -> return (s,s))

putT ::  Monad m => state -> StateT state m ()
putT s = StateT (\_ -> return (s,()))


-- Example: Stack evaluator combining State and Maybe monads
type StackStM =  StateT [Int] Maybe ()

evalStackBopT :: (Int -> Int -> Int) -> StackStM
evalStackBopT op = do
    stack <- getT
    case stack of
      (x:y:rest) -> putT (x `op` y:rest)
      _          -> lift Nothing


peekStackT :: StateT [Int] Maybe Int -- ([Int] -> Maybe ([Int] , Int)
peekStackT = do
    stack <- getT
    case stack of
      s:_ -> return s
      _ -> lift Nothing


evalStackT :: Exp -> StackStM
evalStackT (Num _ n) = do
    stack <- getT
    putT (n:stack)
evalStackT (Add _ t1 t2) = do
    evalStackT t1
    evalStackT t2
    evalStackBopT (+)
evalStackT (Sub _ t1 t2) = do
    evalStackT t1
    evalStackT t2
    evalStackBopT (+)
evalStackT (Mul _ t1 t2) = do
    evalStackT t1
    evalStackT t2
    evalStackBopT (*)
evalStackT (Div _ t1 t2) = do
    evalStackT t1
    evalStackT t2
    n <- peekStackT
    if n == 0 then lift Nothing
    else evalStackBopT div



evalStackTopT :: Exp -> Int
evalStackTopT exp =
  let res = runStateT (evalStackT exp) [] in
  case res of
    Just (top:_, _) -> top
    _ -> error "Error when running the computation"


-- >>> evalStackTopT exp1
-- 42


-- Reader transformers

newtype ReaderT env m a = ReaderT { runReaderT :: env -> m a }

instance Monad m => Monad (ReaderT env m) where
  return :: a -> ReaderT env m a
  return x = ReaderT $ \_ -> return x
  (>>=) :: ReaderT env m a -> (a -> ReaderT env m b) -> ReaderT env m b
  (ReaderT r) >>= f = ReaderT $ \env -> do
    x <- r env
    runReaderT (f x) env

instance Functor m => Functor (ReaderT env m) where
  fmap :: Functor m => (a -> b) -> ReaderT env m a -> ReaderT env m b
  fmap f (ReaderT r) = ReaderT $ \env -> fmap f (r env)

instance Applicative m => Applicative (ReaderT env m) where
  pure :: Applicative m => a -> ReaderT env m a
  pure x = ReaderT $ \_ -> pure x
  (<*>) :: Applicative m => ReaderT env m (a -> b) -> ReaderT env m a -> ReaderT env m b
  (ReaderT rf) <*> (ReaderT rx) = ReaderT $ \env -> rf env <*> rx env


instance MonadTrans (ReaderT env) where
  lift :: Monad m => m a -> ReaderT env m a
  lift ma = ReaderT $ \_ -> ma


askT :: Monad m => ReaderT env m env
askT = ReaderT return

localT :: (env -> env) -> ReaderT env m a -> ReaderT env m a
localT f (ReaderT g) = ReaderT $ \env -> g (f env)

-- Maybe transformers

newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

instance Functor m => Functor (MaybeT m) where
    fmap f (MaybeT mma) = MaybeT (fmap (fmap f) mma)

instance Monad m => Applicative (MaybeT m) where
    pure x = MaybeT (pure (Just x))
    (MaybeT mmf) <*> (MaybeT mmx) = MaybeT $ do
        mf <- mmf
        mx <- mmx
        return (mf <*> mx)

instance Monad m => Monad (MaybeT m) where
    return :: a -> MaybeT m a
    return = MaybeT . return . Just

    (>>=) :: MaybeT m a -> (a -> MaybeT m b) -> MaybeT m b
    (MaybeT mmx) >>= f = MaybeT $ do
        mx <- mmx
        case mx of
            Nothing -> return Nothing
            Just x  -> runMaybeT (f x)

instance MonadTrans MaybeT where
    lift :: Monad m => m a -> MaybeT m a
    lift ma = MaybeT (Just <$> ma)



-- Example: environment-based evaluator written with monad transformers

type Eval = ReaderT Env Maybe

evalTerm' :: Term -> Eval Value
evalTerm' (TVar _ x) = do
  env <- askT
  case M.lookup x env of
    Just v -> return v
    _ -> lift fail
evalTerm' (TAbs _ x t) = do
  env <- askT
  return (VClo env x t)
evalTerm' (TApp _ t1 t2) = do
  v <- evalTerm' t1;
  case v of
    VClo cenv x t -> do
      v2 <- evalTerm' t2;
       -- evaluate t in the closure environment update with the argument value
      localT (\_ -> M.insert x v2 cenv) (evalTerm' t)
    _ -> lift fail
evalTerm' (TInt _ n) = return $ VNum n
evalTerm' (TAdd _ t1 t2) = do
  v1 <- evalTerm' t1;
  v2 <- evalTerm' t2;
  case (v1, v2) of
    (VNum n1, VNum n2) -> return $ VNum (n1 + n2)
    _ -> lift fail
