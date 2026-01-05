module MiniML.Eval where

import Control.Monad.State
import qualified Data.Map as M

import MiniML.Syntax
import MiniML.Error
import MiniML.Print

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
-- within a single monad./Users/zoo/Repos/PL2-first/2024b/miniML/src/MiniML/Typecheck.hs

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
-- Var
eval (Var p x) = do
  env <- getEnv
  case M.lookup x env of
    Just v -> return v
    Nothing -> throwErr p ("Unbound variable " <> x)
-- App
eval (App _ e1 e2) = do
    v1 <- eval e1
    case v1 of
      VClo env' _ x e -> do
        v2 <- eval e2
        localEnv (M.insert x v2 env') (eval e)
      _ -> throwErr (getPosn e1) ("Application of non-functional value " <> showExp e1)
-- Abs
eval (Abs _ x _ e) = do
  env <- getEnv
  return $ VClo env "__dummy" x e
-- Unit
eval (Unit _) = return VUnit
-- Numbers
eval (NumLit _ n) = return $ VNum n
-- Booleans
eval (BoolLit _ b) = return $ VBool b
-- ITE
eval (ITE _ e1 e2 e3) = do
  t1 <- eval e1
  case t1 of
    VBool b -> if b then eval e2 else eval e3
    _ -> throwErr (getPosn e1) "Expression is expected to have a boolean value"
-- Binary operators, arithmetic
eval (Bop _ bop e1 e2) | bop == Plus || bop == Minus || bop == Mult || bop == Div = do
  let f = case bop of
            Plus -> (+)
            Minus -> (-)
            Mult -> (*)
            Div -> div
            _ -> error "unreachable"
  v1 <- eval e1
  v2 <- eval e2
  case (v1, v2) of
    (VNum n1, VNum n2) -> return $ VNum (f n1 n2)
    _ -> throwErr (getPosn e1) $ "Expressions are expected to have type int " <> show v1 <> " and " <> show v2 
-- Binary operators, comparison
eval (Bop _ bop e1 e2) | bop == Le || bop == Lt || bop == Ge || bop == Gt || bop == Eq = do
  let f = case bop of
            Le -> (<=)
            Lt -> (<)
            Ge -> (>=)
            Gt -> (>)
            Eq -> (==)
            _ -> error "unreachable"
  v1 <- eval e1
  v2 <- eval e2
  case (v1, v2) of
    (VNum n1, VNum n2) -> return $ VBool $ f n1 n2
    _ -> throwErr (getPosn e1) "Expressions are expected to have type int"
-- Binary operators, boolean
eval (Bop _ bop e1 e2) | bop == Or || bop == And = do
  let f = case bop of
            Or -> (||)
            And -> (&&)
            _ -> error "unreachable"
  v1 <- eval e1
  v2 <- eval e2
  case (v1, v2) of
    (VBool b1, VBool b2) -> return $ VBool $ f b1 b2
    _ -> throwErr (getPosn e1) "Expressions are expected to have type bool"
-- Unary operator
eval (Uop _ Not e1) = do
  v1 <- eval e1
  case v1 of
    VBool b -> return $ VBool $ not b
    _ -> throwErr (getPosn e1) "Expression is expected to have type bool"
-- Pairs
eval (Tuple _ args) = do
  vs <- mapM eval args
  return $ VTuple vs
eval (Proj _ i e1) = do
  v1 <- eval e1
  case v1 of
    VTuple vs -> if i < length vs then return (vs !! i) else throwErr (getPosn e1) "Tuple index out of bounds"
    _ -> throwErr (getPosn e1) "Expression is expected to have a product type"
-- Sums
eval (Inl _ _ e1) = do
  v1 <- eval e1
  return $ VInl v1
eval (Inr _ _ e2) = do
  v2 <- eval e2
  return $ VInr v2
eval (Case _ e1 x e2 y e3) = do
  v <- eval e1
  env <- getEnv
  case v of
    VInl v1 -> localEnv (M.insert x v1 env) (eval e2)
    VInr v2 -> localEnv (M.insert y v2 env) (eval e3)
    _ -> throwErr (getPosn e1) "Expression is expected to have a sum type"
-- Let
eval (Let _ x _ e1 e2) = do
  v1 <- eval e1
  env <- getEnv
  localEnv (M.insert x v1 env) (eval e2)
-- Let rec
eval (LetRec _ f x _ _ e1 e2) = do
  env <- getEnv
  let f_clo = VClo (M.insert f f_clo env) f x e1
  localEnv (M.insert f f_clo env) (eval e2)
-- References
eval (Asgn _ e1 e2) = do
  v1 <- eval e1
  case v1 of
    Memloc l -> do
      v2 <- eval e2
      withStore (M.insert l v2) (return VUnit)
    _ -> throwErr (getPosn e1) "Expression is expected to have a reference type"
eval (Deref p e1) = do
  v1 <- eval e1
  store <- getStore
  case v1 of
    Memloc l -> case M.lookup l store of
      Just v -> return v
      _ -> throwErr p ("Dangling location " <> show l)
    _ -> throwErr (getPosn e1) "Expression is expected to have a reference type"
eval (Ref _ e1) = do
  v1 <- eval e1
  l <- freshLoc
  withStore (M.insert l v1) (return $ Memloc l)
eval (Nil _ _) = pure $ VList []
eval (Cons _ e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  case v2 of
    VList l2 -> return $ VList (v1:l2)
    _ -> throwErr (getPosn e2) "Expression is expected to have a list type"
eval (CaseL _ e1 e2 z y e3) = do
  v <- eval e1
  env <- getEnv
  case v of
    VList [] -> localEnv env (eval e2)
    VList (v1:l1) -> localEnv (M.insert z v1 (M.insert y (VList l1) env)) (eval e3)
    _ -> throwErr (getPosn e1) "Expression is expected to have a list type"
eval e = throwErr (getPosn e) ("Evaluation of illegal expression " <> show e)

-- Top-level evaluation function. Runs the main evaluation function on an empty
-- state and extracts the value and the store. Note that the store is needed as
-- the value may contain memory locations.
evalTop :: Exp -> Error (Value,Store)
evalTop e = do
  let initState = (M.empty, M.empty, 0)
  (val, (_, store, _)) <- runStateT (eval e) initState
  return (val, store)

-- evaluation without closures
evalcc :: Exp -> Eval Value
-- Var
evalcc (Var p x) = do
  env <- getEnv
  case M.lookup x env of
    Just v -> return v
    Nothing -> throwErr p ("Unbound variable " <> x)
-- App
evalcc (App _ e1 e2) = do
    v1 <- evalcc e1
    case v1 of
      VClo _ f x e -> do
        v2 <- evalcc e2
        localEnv (M.insert x v2 $ M.insert f v1 mempty) (evalcc e)
      _ -> throwErr (getPosn e1) ("Application of non-functional value " <> showExp e1)
-- Abs
evalcc (Abs _ x _ e) = do
  return $ VClo mempty "__dummy" x e
-- Unit
evalcc (Unit _) = return VUnit
-- Numbers
evalcc (NumLit _ n) = return $ VNum n
-- Booleans
evalcc (BoolLit _ b) = return $ VBool b
-- ITE
evalcc (ITE _ e1 e2 e3) = do
  t1 <- evalcc e1
  case t1 of
    VBool b -> if b then evalcc e2 else evalcc e3
    _ -> throwErr (getPosn e1) "Expression is expected to have a boolean value"
-- Binary operators, arithmetic
evalcc  (Bop _ bop e1 e2) | bop == Plus || bop == Minus || bop == Mult || bop == Div = do
  let f = case bop of
            Plus -> (+)
            Minus -> (-)
            Mult -> (*)
            Div -> div
            _ -> error "unreachable"
  v1 <- evalcc e1
  v2 <- evalcc e2
  case (v1, v2) of
    (VNum n1, VNum n2) -> return $ VNum (f n1 n2)
    _ -> throwErr (getPosn e1) $ "Expressions are expected to have type int " <> show v1 <> " and " <> show v2 
-- Binary operators, comparison
evalcc (Bop _ bop e1 e2) | bop == Le || bop == Lt || bop == Ge || bop == Gt || bop == Eq = do
  let f = case bop of
            Le -> (<=)
            Lt -> (<)
            Ge -> (>=)
            Gt -> (>)
            Eq -> (==)
            _ -> error "unreachable"
  v1 <- evalcc e1
  v2 <- evalcc e2
  case (v1, v2) of
    (VNum n1, VNum n2) -> return $ VBool $ f n1 n2
    _ -> throwErr (getPosn e1) "Expressions are expected to have type int"
-- Binary operators, boolean
evalcc (Bop _ bop e1 e2) | bop == Or || bop == And = do
  let f = case bop of
            Or -> (||)
            And -> (&&)
            _ -> error "unreachable"
  v1 <- evalcc e1
  v2 <- evalcc e2
  case (v1, v2) of
    (VBool b1, VBool b2) -> return $ VBool $ f b1 b2
    _ -> throwErr (getPosn e1) "Expressions are expected to have type bool"
-- Unary operator
evalcc (Uop _ Not e1) = do
  v1 <- evalcc e1
  case v1 of
    VBool b -> return $ VBool $ not b
    _ -> throwErr (getPosn e1) "Expression is expected to have type bool"
-- Pairs
evalcc (Tuple _ args) = do
  vs <- mapM evalcc args
  return $ VTuple vs
evalcc (Proj _ i e1) = do
  v1 <- evalcc e1
  case v1 of
    VTuple vs -> if i < length vs then return (vs !! i) else throwErr (getPosn e1) "Tuple index out of bounds"
    _ -> throwErr (getPosn e1) "Expression is expected to have a product type"
-- Sums
evalcc (Inl _ _ e1) = do
  v1 <- evalcc e1
  return $ VInl v1
evalcc (Inr _ _ e2) = do
  v2 <- evalcc e2
  return $ VInr v2
evalcc (Case _ e1 x e2 y e3) = do
  v <- evalcc e1
  env <- getEnv
  case v of
    VInl v1 -> localEnv (M.insert x v1 env) (evalcc e2)
    VInr v2 -> localEnv (M.insert y v2 env) (evalcc e3)
    _ -> throwErr (getPosn e1) "Expression is expected to have a sum type"
-- Let
evalcc (Let _ x _ e1 e2) = do
  v1 <- evalcc e1
  env <- getEnv
  localEnv (M.insert x v1 env) (evalcc e2)
-- Let rec
evalcc (LetRec _ f x _ _ e1 e2) = do
  env <- getEnv
  let f_clo = VClo mempty f x e1
  localEnv (M.insert f f_clo env) (evalcc e2)
-- References
evalcc (Asgn _ e1 e2) = do
  v1 <- evalcc e1
  case v1 of
    Memloc l -> do
      v2 <- evalcc e2
      withStore (M.insert l v2) (return VUnit)
    _ -> throwErr (getPosn e1) "Expression is expected to have a reference type"
evalcc (Deref p e1) = do
  v1 <- evalcc e1
  store <- getStore
  case v1 of
    Memloc l -> case M.lookup l store of
      Just v -> return v
      _ -> throwErr p ("Dangling location " <> show l)
    _ -> throwErr (getPosn e1) "Expression is expected to have a reference type"
evalcc (Ref _ e1) = do
  v1 <- evalcc e1
  l <- freshLoc
  withStore (M.insert l v1) (return $ Memloc l)
evalcc (Nil _ _) = pure $ VList []
evalcc (Cons _ e1 e2) = do
  v1 <- evalcc e1
  v2 <- evalcc e2
  case v2 of
    VList l2 -> return $ VList (v1:l2)
    _ -> throwErr (getPosn e2) "Expression is expected to have a list type"
evalcc (CaseL _ e1 e2 z y e3) = do
  v <- evalcc e1
  env <- getEnv
  case v of
    VList [] -> localEnv env (evalcc e2)
    VList (v1:l1) -> localEnv (M.insert z v1 (M.insert y (VList l1) env)) (evalcc e3)
    _ -> throwErr (getPosn e1) "Expression is expected to have a list type"
evalcc e = throwErr (getPosn e) ("Evaluation of illegal expression " <> show e)

-- Top-level evaluation function. Runs the main evaluation function on an empty
-- state and extracts the value and the store. Note that the store is needed as
-- the value may contain memory locations.
evalccTop :: Exp -> Error (Value,Store)
evalccTop e = do
  let initState = (M.empty, M.empty, 0)
  (val, (_, store, _)) <- runStateT (evalcc e) initState
  return (val, store)