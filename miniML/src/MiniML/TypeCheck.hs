module MiniML.TypeCheck where
{-
Student name:
Student ID:
-}

import qualified Data.Map as M

import MiniML.Syntax
import MiniML.Error
import MiniML.Print

-- A typing context. Maps variables to their type. You may want to look at the
-- `Map` library for operations on maps:
-- https://hackage.haskell.org/package/containers-0.4.0.0/docs/Data-Map.html
type Ctx = M.Map String Type

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
typeCheck env (Abs _ x (Just t1) e) = do
  t2 <- typeCheck (M.insert x t1 env) e
  return $ TArrow t1 t2
typeCheck _ (Abs p _ Nothing _) =
  typeError p "Function parameter must have an explicit type annotation"
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
typeCheck env (Uop _ Not e1) = do
  t1 <- typeCheck env e1
  case t1 of
    TBool -> return TBool
    _ -> typeError (getPosn e1) ("Expression is expected to have type bool but has type  " <> showType t1)
-- Pairs
typeCheck env (Tuple _ [e1, e2]) = do
  t1 <- typeCheck env e1
  t2 <- typeCheck env e2
  return $ TProd t1 t2
typeCheck env (Proj _ 0 e1) = do
  t1 <- typeCheck env e1
  case t1 of
    TProd t1' _ -> return t1'
    _ -> typeError (getPosn e1) ("Expression is expected to have a product type but has type  " <> showType t1)
typeCheck env (Proj _ 1 e1) = do
  t1 <- typeCheck env e1
  case t1 of
    TProd _ t2' -> return t2'
    _ -> typeError (getPosn e1) ("Expression is expected to have a product type but has type  " <> showType t1)
-- Sums
typeCheck env (Inl _ (Just t2) e1) = do
  t1 <- typeCheck env e1
  return $ TSum t1 t2
typeCheck env (Inr _ (Just t1) e2) = do
  t2 <- typeCheck env e2
  return $ TSum t1 t2
typeCheck _ (Inl p Nothing _) =
  typeError p ("Inl must have an explicit type annotation")
typeCheck _ (Inr p Nothing _) =
  typeError p ("Inr must have an explicit type annotation")
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
typeCheck env (Let _ x (Just t) e1 e2) = do
    t1 <- typeCheck env e1
    if t1 == t then typeCheck (M.insert x t env) e2
    else typeError (getPosn e1) ("Expression is expected to have type " <> showType t <> " but has type " <> showType t1)
typeCheck _ (Let p _ Nothing _ _) = typeError p "Let bindings must have an explicit type annotation"
-- Let rec
typeCheck env (LetRec _ f x (Just t1) (Just t2) e1 e2) = do
    tres <- typeCheck (M.insert x t1 (M.insert f (TArrow t1 t2) env)) e1
    if tres == t2 then typeCheck (M.insert f (TArrow t1 t2) env) e2
    else typeError (getPosn e1) ("Expression is expected to have type " <> showType t2 <> " but has type " <> showType tres)
typeCheck _ (LetRec p _ _ _ _ _ _) = typeError p "Let rec must have explicit type annotations"
-- References
typeCheck env (Asgn _ e1 e2) = do
  t1 <- typeCheck env e1
  case t1 of
    TRef t1' -> do
      t2 <- typeCheck env e2
      if t2 == t1' then return TUnit
      else typeError (getPosn e2) ("Expression is expected to have type " <> showType t1' <> " but has type " <> showType t2)
    _ -> typeError (getPosn e1) ("Expression is expected to have a reference type but has type " <> showType t1)
typeCheck env (Deref _ e1) = do
  t1 <- typeCheck env e1
  case t1 of
    TRef t1' -> return t1'
    _ -> typeError (getPosn e1) ("Expression is expected to have a reference type but has type " <> showType t1)
typeCheck env (Ref _ e1) = do
  t1 <- typeCheck env e1
  return (TRef t1)
-- Lists
typeCheck _ (Nil _ (Just ty)) = return (TList ty)
typeCheck _ (Nil p Nothing) = typeError p "Nil must have an explicit type annotation"
typeCheck env (Cons _ e1 e2) = do
  t1 <- typeCheck env e1
  t2 <- typeCheck env e2
  case t2 of
    TList t2' -> if t1 == t2' then return t2
                    else typeError (getPosn e1) ("Expression is expected to have type " <> showType t2' <> " but has type " <> showType t1)
    _ -> typeError (getPosn e2) ("Expression is expected to have a list type but has type " <> showType t2)
typeCheck env (CaseL _ e1 e2 x y e3) = do
    t1 <- typeCheck env e1
    case t1 of
      TList t_elem -> do
        t_nil <- typeCheck env e2
        t_cons <- typeCheck (M.insert y (TList t_elem) (M.insert x t_elem env)) e3
        if t_nil == t_cons then return t_nil
        else typeError (getPosn e3) ("Expression is expected to have type " <> showType t_nil <> " but has type " <> showType t_cons)
      _ -> typeError (getPosn e1) ("Expression is expected to have a list type but has type " <> showType t1)
typeCheck env (Prim _ "lazy" e) = error "TODO!"
typeCheck env (Prim _ "force" e) = error "TODO!"
typeCheck _ (Prim p f _) = typeError p ("Unimplemented primitive function " <> f)
typeCheck _ e = typeError (getPosn e) ("Type checking of illegal expression: " <> show e)

-- Top-level typechecking function with an empty context
typeCheckTop :: Exp -> Error Type
typeCheckTop = typeCheck M.empty


