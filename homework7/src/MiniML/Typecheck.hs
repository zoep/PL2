module MiniML.Typecheck where

import qualified Data.Map as M
import qualified Data.Map.Ordered as OM
import qualified Data.Set as S

import Control.Monad

import MiniML.Syntax
import MiniML.Error
import MiniML.Print
import MiniML.Values

-- A typing context. Maps variables to their type. You may want to look at the
-- `Map` library for operations on maps:
-- https://hackage.haskell.org/package/containers-0.4.0.0/docs/Data-Map.html
type Ctx = M.Map String Type

-- TODO 1: Extend the type checker to handle the following cases:
-- 1. Recursive functions (`let rec f (x : t1) : t2 = e1 in e2`)
-- 2. References (`ref e`)
-- 3. Dereferencing (`!e`)
-- 4. Assignment (`e1 := e2`):

-- Throw a typechecking error
typeError :: Posn -> String -> Error Type
typeError p msg = Left (p, msg)

-- Main typechecking functions
typeCheck :: Ctx -> Exp -> Error Type
-- Var
typeCheck env (Var p x) = case M.lookup x env of
    Just typ -> return typ
    Nothing -> typeError p ("Unbound variable " <> x)
-- App
typeCheck env (App _ e1 e2) = do
    t1 <- typeCheck env e1
    case t1 of
      TArrow tin tout -> do
        t2 <- typeCheck env e2
        if t2 == tin then return tout
        else typeError (getPosn e2) ("Argument is expected to have type " <> showType tin <> " but has type "  <> showType tout)
      _ -> typeError (getPosn e1) ("Application of non functional type " <> showType t1 <> "\n" <> showExp e1)
-- Abs
typeCheck env (Abs _ x t1 _ e) = do
  t2 <- typeCheck (M.insert x t1 env) e
  return $ TArrow t1 t2
-- Unit
typeCheck _ (Unit _) = return TUnit
-- Numbers
typeCheck _ (NumLit _ _) = return TInt
-- Booleans
typeCheck _ (BoolLit _ _) = return TBool
-- ITE
typeCheck env (ITE _ e1 e2 e3) = do
  t1 <- typeCheck env e1
  case t1 of
    TBool -> do
      t2 <- typeCheck env e2
      t3 <- typeCheck env e3
      if t2 == t3 then return t2
      else typeError (getPosn e3) ("Expression is expected to have type " <> showType t2 <> " but has type " <> showType t3)
    _ -> typeError (getPosn e1) ("Expression is expected to have type bool but has type  " <> showType t1)
-- Binary operators, arithmetic
typeCheck env (Bop _ bop e1 e2) | bop == Plus || bop == Minus || bop == Mult || bop == Div = do
  t1 <- typeCheck env e1
  t2 <- typeCheck env e2
  case t1 of
    TInt -> case t2 of
      TInt -> return TInt
      _ -> typeError (getPosn e2) ("Expression is expected to have type int but has type  " <> showType t2)
    _ -> typeError (getPosn e1) ("Expression is expected to have type int but has type  " <> showType t1)
-- Binary operators, comparison
typeCheck env (Bop _ bop e1 e2) | bop == Le || bop == Lt || bop == Ge || bop == Gt || bop == Eq = do
  t1 <- typeCheck env e1
  t2 <- typeCheck env e2
  case t1 of
    TInt -> case t2 of
      TInt -> return TBool
      _ -> typeError (getPosn e2) ("Expression is expected to have type int but has type  " <> showType t2)
    _ -> typeError (getPosn e1) ("Expression is expected to have type int but has type  " <> showType t1)
-- Binary operators, boolean
typeCheck env (Bop _ bop e1 e2) | bop == Or || bop == And = do
  t1 <- typeCheck env e1
  t2 <- typeCheck env e2
  case t1 of
    TBool -> case t2 of
      TBool -> return TBool
      _ -> typeError (getPosn e2) ("Expression is expected to have type bool but has type  " <> showType t2)
    _ -> typeError (getPosn e1) ("Expression is expected to have type bool but has type  " <> showType t1)
-- Unary operator
typeCheck _ (Bop _ _ _ _) = throw (nowhere, "Unreachable")
typeCheck env (Uop _ Not e1) = do
  t1 <- typeCheck env e1
  case t1 of
    TBool -> return TBool
    _ -> typeError (getPosn e1) ("Expression is expected to have type bool but has type  " <> showType t1)
-- Pairs
typeCheck env (Pair _ e1 e2) = do
  t1 <- typeCheck env e1
  t2 <- typeCheck env e2
  return $ TProd t1 t2
typeCheck env (Fst _ e1) = do
  t1 <- typeCheck env e1
  case t1 of
    TProd t1' _ -> return t1'
    _ -> typeError (getPosn e1) ("Expression is expected to have a product type but has type  " <> showType t1)
typeCheck env (Snd _ e1) = do
  t1 <- typeCheck env e1
  case t1 of
    TProd _ t2' -> return t2'
    _ -> typeError (getPosn e1) ("Expression is expected to have a product type but has type  " <> showType t1)
-- Sums
typeCheck env (Inl _ t2 e1) = do
  t1 <- typeCheck env e1
  return $ TSum t1 t2
typeCheck env (Inr _ t1 e2) = do
  t2 <- typeCheck env e2
  return $ TSum t1 t2
typeCheck env (Case _ e1 x e2 y e3) = do
  t1 <- typeCheck env e1
  case t1 of
    TSum t1' t2' -> do
      tl <- typeCheck (M.insert x t1' env) e2
      tr <- typeCheck (M.insert y t2' env) e3
      if tl == tr then return tl
      else typeError (getPosn e3) ("Expression is expected to have type " <> showType tl <> " but has type " <> showType tr)
    _ -> typeError (getPosn e1) ("Expression is expected to have a sum type but has type  " <> showType t1)
-- Let
typeCheck env (Let _ x t e1 e2) = do
    t1 <- typeCheck env e1
    if t1 == t then typeCheck (M.insert x t env) e2
    else typeError (getPosn e1) ("Expression is expected to have type " <> showType t <> " but has type " <> showType t1)
-- Let rec
typeCheck _ (LetRec _ _ _ _ _ _ _) = error "FILL IN HERE"
-- References
typeCheck _ (Asgn _ _ _) = error "FILL IN HERE"
typeCheck _ (Deref _ _) = error "FILL IN HERE"
typeCheck _  (Ref _ _) = error "FILL IN HERE"

-- Top-level typechecking function with an empty context
typeCheckTop :: Exp -> Error Type
typeCheckTop = typeCheck M.empty

-- You may ignore the implementation details of the following but make sure you
-- understand the type signature and high-level functionality.


-- Annotate a program with result types for lambda abstractions.
annotate :: Ctx -> Exp -> Error Exp
annotate _ (Unit p) = return $ Unit p
annotate _ (NumLit p n) = return $ NumLit p n
annotate _ (BoolLit p b) = return $ BoolLit p b
annotate _ (Var p y) = return $ Var p y
annotate env (Pair p e1 e2) = liftM2 (Pair p) (annotate env e1) (annotate env e2)
annotate env (Ref p e) = liftM (Ref p) (annotate env e)
annotate env (Deref p e) = liftM (Deref p) (annotate env e)
annotate env (App p e1 e2) = liftM2 (App p) (annotate env e1) (annotate env e2)
annotate env (Uop p op e) = liftM (Uop p op) (annotate env e)
annotate env (Fst p e) = liftM (Fst p) (annotate env e)
annotate env (Snd p e) = liftM (Snd p) (annotate env e)
annotate env (Inl p t e) = liftM (Inl p t) (annotate env e)
annotate env (Inr p t e) = liftM (Inr p t) (annotate env e)
annotate env (Bop p bop e1 e2) = liftM2 (Bop p bop) (annotate env e1) (annotate env e2)
annotate env (Asgn p e1 e2) = liftM2 (Asgn p) (annotate env e1) (annotate env e2)
annotate env (Let p y t e1 e2) = liftM2 (Let p y t) (annotate env e1) (annotate (M.insert y t env) e2)
annotate env (LetRec p f y t1 t2 e1 e2) =
  let tf = TArrow t1 t2 in
  liftM2 (LetRec p f y t1 t2) (annotate (M.insert f tf (M.insert y t1 env)) e1) (annotate (M.insert f tf env) e2)
annotate env (Abs p y t1 _ e) = do
  let env' = M.insert y t1 env
  t2 <- typeCheck env' e
  liftM (Abs p y t1 (Just t2)) (annotate env' e)
annotate env (ITE p e1 e2 e3) = liftM3 (ITE p) (annotate env e1) (annotate env e2) (annotate env e3)
annotate env (Case p e z e1 y e2) = do
  e' <- annotate env e
  t <- typeCheck env e
  case t of
    TSum t1 t2 -> do
      e1' <- annotate (M.insert z t1 env) e1
      e2' <- annotate (M.insert y t2 env) e2
      return $ Case p e' z e1' y e2'
    _ -> throw (p, "Expression should have a sum type")

annotateTop :: Exp -> Error Exp
annotateTop = annotate M.empty

-- Type checking for configurations (a value together with a store that maps
-- locations to values).

-- Constructing store typing for a store gets a bit technical as it requires to
-- sort the store in a topological order. This is always possible as the store
-- in ML-style references is always acyclic (no circular references in the
-- heap).

type StoreTyping = M.Map Loc Type

typeCheckV :: StoreTyping -> Value -> Error Type
-- Unit
typeCheckV _ VUnit = return TUnit
-- Numbers
typeCheckV _ (VNum _) = return TInt
-- Booleans
typeCheckV _ (VBool _) = return TBool
typeCheckV senv (VPair v1 v2) = do
  t1 <- typeCheckV senv v1
  t2 <- typeCheckV senv v2
  return $ TProd t1 t2
-- Sums
typeCheckV senv (VInl t2 v1) = do
  t1 <- typeCheckV senv v1
  return $ TSum t1 t2
typeCheckV senv (VInr t1 v2) = do
  t2 <- typeCheckV senv v2
  return $ TSum t1 t2
-- Closures
typeCheckV senv (VClo venv f x t1 t2 e) = do
  tenv <- mapM (typeCheckV senv) venv
  t2' <- typeCheck (M.insert x t1 (M.insert f (TArrow t1 t2) tenv)) e
  if t2 == t2' then return (TArrow t1 t2')
  else  typeError nowhere ("Type error")
-- Locations
typeCheckV senv (Memloc l) = case M.lookup l senv of
    Just typ -> return typ
    Nothing -> typeError nowhere ("Unbound location " <> show l)

typeCheckVTop :: Store -> Value -> Error Type
typeCheckVTop store val = do
    -- produces a store typing from the store by typechecking each value
    senv <- foldM typeCheckStoreValue M.empty (topologicalSort store)
    typeCheckV senv val
  where
    -- typechecks a value in the store and puts it in the store typing context
    typeCheckStoreValue :: StoreTyping -> (Loc, Value) -> Error StoreTyping
    typeCheckStoreValue senv' (loc, val') = do
        vtyp <- typeCheckV senv' val'
        return $ M.insert loc vtyp senv'


-- Sorts a store in topological order of locations so that we can find its typing

topologicalSort :: Store -> [(Loc, Value)]
topologicalSort store =
  -- OM.assoc will return the nodes in the reverse order they were
  -- visited (post-order). Reversing this gives as a topological
  -- ordering of the nodes.
    reverse . OM.assocs $ snd $ foldr (\l' (s,v) -> dfs s v l') (S.empty, OM.empty) (map fst (M.toList store))
  where
    dfs :: S.Set Loc -> OM.OMap Loc Value -> Loc -> (S.Set Loc, OM.OMap Loc Value)
    dfs seen visited l | OM.member l visited = (seen, visited)
    dfs seen _ l       | S.member l seen = error "Internal error: Detected cycle in heap"
    dfs seen visited l =
      let (vs, value) = adjacent l in
      let seen' = S.insert l seen in
      let (seen'', visited') = foldr (\l' (s,v) -> dfs s v l') (seen', visited) vs in
      (seen'', (l, value) OM.|< visited')

    adjacent :: Loc -> ([Loc], Value)
    adjacent l = case M.lookup l store of
        Just v -> (locsFromValue v, v)
        Nothing -> error "Internal error: node must be in the graph"

    locsFromValue :: Value -> [Loc]
    locsFromValue (Memloc l) = [l]
    locsFromValue VUnit = []
    locsFromValue (VNum _) = []
    locsFromValue (VBool _) = []
    locsFromValue (VInl _ v) = locsFromValue v
    locsFromValue (VInr _ v) = locsFromValue v
    locsFromValue (VPair v1 v2) = locsFromValue v1 ++ locsFromValue v2
    locsFromValue (VClo env f x t1 t2 e) =
      concatMap (locsFromValue . snd) $ filter isFree $ M.toList env
      where
        isFree (z, _) = occursFree z (Abs nowhere x t1 (Just t2) e) && x /= f