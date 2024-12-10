module MiniML.Eval where

import qualified Data.Map as M
import Control.Monad.State

import MiniML.Syntax
import MiniML.Error
import MiniML.Values


-- MiniML evaluation

-- Make sure to look at Values.hs for the associated data types.

-- The evaluation state.
type EvalState = ( Env     -- An environment mapping variables to their values.
                 , Store   -- A store mapping memory locations to values.
                 , Loc     -- The next available memory location. Needed when allocation new references.
                 )

-- The type of the evaluation computation.
type Eval = StateT EvalState (Either (Posn,String))

-- `StateT` is the monad transformer for the State monad. It allows you to put
-- an arbitrary monad inside the State. Here, we put an Error monad inside the
-- result of the state, composing the State monad with the Error monad.

-- The resulting monad, `Eval`, manages both mutable state and error propagation
-- within a single monad.

-- Essentially, the type `Eval a` represents a computation of type `EvalState -> (EvalState, Error a)`

-- Note 1: In the definition of `Eval`, we use `Either (Posn, String)` directly
-- instead of the type synonym `Error` (defined in Error.hs) because Haskell
-- does not allow partially applied type synonyms.

-- Note 2: Technically, we could have used a reader monad for Env, but it makes
-- our definitions simpler to put it in the state and avoid composing too many
-- monads.

-- Useful functions for handling the state.

-- Get the environment
getEnv :: Eval Env
getEnv = do
  (env, _, _) <- get
  return env

-- Update the environment
putEnv :: Env -> Eval ()
putEnv env = do
  (_, store, l) <- get
  put (env, store, l)

-- Get the store
getStore :: Eval Store
getStore = do
  (_, store, _) <- get
  return store

-- Update the store
putStore :: Store -> Eval ()
putStore store = do
  (env, _, l) <- get
  put (env, store, l)

-- Run a computation in the provided environment
localEnv :: Env -> Eval a -> Eval a
localEnv env m = do
  env' <- getEnv
  putEnv env
  x <- m
  putEnv env'
  return x

-- Update the store using the given function and run a computation
withStore :: (Store -> Store) -> Eval a -> Eval a
withStore f m = do
  store <- getStore
  putStore (f store)
  m

-- Return a fresh location and increase the location counter
freshLoc :: Eval Loc
freshLoc = do
  (store, env, l) <- get
  let l' = l + 1
  put (store, env, l')
  return l'

-- Throw an error.
throwErr :: Posn -> String -> Eval a
throwErr p str = lift (throw (p,str))

-- Main evaluation function.

-- TODO 2: Fill in the definition for the evaluation function.

-- Make sure to correctly propagate the types to closure values. This should be
-- available as type annotations in the input program (Do not use the
-- typechecking function in te evaluation function!). You can assume that the
-- input programs will never have the form `Abs p x t Nothing e` (i.e., return
-- type annotations will be filled).

eval :: Exp -> Eval Value
eval _ = error "FILL IN HERE"

-- Top-level evaluation function. Runs the main evaluation function on an empty
-- state and extracts the value and the store. Note that the store is needed as
-- the value may contain memory locations.
evalTop :: Exp -> Error (Value,Store)
evalTop e = do
  let initState = (M.empty, M.empty, 0)
  (val, (_, store, _)) <- runStateT (eval e) initState
  return (val, store)