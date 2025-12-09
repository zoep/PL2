module MiniML.Syntax where

import qualified Data.Set as S
import Data.List 
import qualified Data.Map as M

import MiniML.Lex (AlexPosn(..))

-- The AST of MiniML

-- The source code position
type Posn = AlexPosn

type Id = String

-- Types
data Type = TUnit
          | TInt
          | TBool
          | TArrow Type Type
          | TProd  Type Type
          | TSum   Type Type
          | TRef   Type
          | TList  Type
          | TVar   String
          | TLazy  Type
   deriving (Eq,Show,Ord)

-- Binary and unary operators
data Bop = Plus | Minus | Mult | Div
         | And | Or
         | Lt | Gt | Le | Ge
         | Eq
   deriving (Eq,Show)

data Uop = Not
   deriving (Eq,Show)

-- Expressions. Observe some type annotations are optional. The source code is
-- always required to have these type annotations in place to facilitate type
-- checking. But after type checking, transformations may introduce terms that
-- are not fully annotated (and not even well-typed in the source language).
-- Food for thought: what is the type of a closure converted function? Can it be
-- represented in this type system?
data Exp =
  -- STLC
    Var     Posn String
  | App     Posn Exp Exp
  | Abs     Posn String (Maybe Type) Exp
  -- Unit
  | Unit    Posn
  -- Numbers
  | NumLit  Posn Integer
  -- Booleans
  | BoolLit Posn Bool
  | ITE     Posn Exp Exp Exp
  -- Operators
  | Bop     Posn Bop Exp Exp
  | Uop     Posn Uop Exp
  -- Tuples
  | Tuple   Posn [Exp]
  | Proj    Posn Int Exp
  -- Lists
  | Nil     Posn (Maybe Type)
  | Cons    Posn Exp Exp
  | CaseL   Posn Exp Exp String String Exp
  -- Sums
  | Inl     Posn (Maybe Type) Exp
  | Inr     Posn (Maybe Type) Exp
  | Case    Posn Exp Id Exp Id Exp
  -- Let
  | Let     Posn Id (Maybe Type) Exp Exp
  -- Let rec
  | LetRec  Posn Id Id (Maybe Type) (Maybe Type) Exp Exp
  -- References
  | Asgn    Posn Exp Exp
  | Deref   Posn Exp
  | Ref     Posn Exp
-- Primitive functions
  | Prim    Posn String Exp
  deriving Show


-- Custom equality for expressions that ignores the source code position
instance Eq Exp where
    Var _ x              == Var _ y                   = x == y
    App _ e1 e2          == App _ e1' e2'             = e1 == e1' && e2 == e2'
    Abs _ x t e          == Abs _ x' t' e'            = x == x' && t == t' && e == e'
    Unit _               == Unit _                    = True
    NumLit _ n1          == NumLit _ n2               = n1 == n2
    BoolLit _ b1         == BoolLit _ b2              = b1 == b2
    ITE _ e1 e2 e3       == ITE _ e1' e2' e3'         = e1 == e1' && e2 == e2' && e3 == e3'
    Bop _ b e1 e2        == Bop _ b' e1' e2'          = b == b' && e1 == e1' && e2 == e2'
    Uop _ u e1           == Uop _ u' e1'              = u == u'&& e1 == e1'
    Nil _ t              == Nil _ t'                  = t == t'
    Cons _ e1 e2         == Cons _ e1' e2'            = e1 == e1' && e2 == e2'
    CaseL _ e1 e2 x y e3 == CaseL _ e1' e2' x' y' e3' = e1 == e1' && e2 == e2' && x == x' && y == y' && e3 == e3'
    Tuple _ l            == Tuple _ l'                = l == l'
    Proj _ n e1          == Proj _ n' e1'             = n == n' && e1 == e1'
    Inl _ t1 e1          == Inl _ t1' e1'             = t1 == t1' && e1 == e1'
    Inr _ t1 e1          == Inr _ t1' e1'             = t1 == t1' && e1 == e1'
    Case _ e1 x e2 y e3  == Case _ e1' x' e2' y' e3'  = e1 == e1' && x == x' && e2 == e2' && y == y' && e3 == e3'
    Let _ x t1 e1 e2     == Let _ x' t1' e1' e2'      = x == x' && e1 == e1' && t1 == t1' && e2 == e2'
    LetRec _ f x t r b e == LetRec _ g y t' r' b' e'  = f == g && x == y && t == t' && r == r' && b == b'  && e == e'
    Asgn _ e1 e2         == Asgn _ e1' e2'            = e1 == e1' && e2 == e2'
    Deref _ e1           == Deref _ e1'               = e1 == e1'
    Ref _ e1             == Ref _ e1'                 = e1 == e1'
    _                    == _                         = False


nowhere :: Posn
nowhere = AlexPn 0 0 0

-- Get the source code position of an expression
getPosn :: Exp -> Posn
getPosn (Unit p) = p
getPosn (NumLit p _) = p
getPosn (BoolLit p _) = p
getPosn (Var p _) = p
getPosn (Tuple p _) = p
getPosn (Ref p _) = p
getPosn (Deref p _) = p
getPosn (App p _ _) = p
getPosn (Uop p _ _) = p
getPosn (Nil p _) = p
getPosn (Cons p _ _) = p
getPosn (CaseL p _ _ _ _ _) = p
getPosn (Proj p _ _) = p
getPosn (Inl p _ _) = p
getPosn (Inr p _ _) = p
getPosn (Bop p _ _ _) = p
getPosn (Asgn p _ _) = p
getPosn (Let p _ _ _ _) = p
getPosn (LetRec p _ _ _ _ _ _) = p
getPosn (Abs p _ _ _) = p
getPosn (ITE p _ _ _) = p
getPosn (Case p _ _ _ _ _) = p
getPosn (Prim p _ _) = p

-- Check if a variable occurs free in a term
occursFree :: String -> Exp -> Bool
occursFree _ (Unit _) = False
occursFree _ (NumLit _ _) = False
occursFree _ (BoolLit _ _) = False
occursFree x (Var _ y) = x == y
occursFree _ (Nil _ _) = False
occursFree x (Cons _ e1 e2) = occursFree x e1 || occursFree x e2
occursFree x (CaseL _ e e1 z y e2) = occursFree x e || occursFree x e1 || (occursFree x e2  && x /= y && x /= z)
occursFree x (Tuple _ es) = foldr ((||) . occursFree x) False es
occursFree x (Ref _ e) = occursFree x e
occursFree x (Deref _ e) = occursFree x e
occursFree x (App _ e1 e2) = occursFree x e1 || occursFree x e2
occursFree x (Uop _ _ e) = occursFree x e
occursFree x (Proj _ _ e) = occursFree x e
occursFree x (Inl _ _ e) = occursFree x e
occursFree x (Inr _ _ e) = occursFree x e
occursFree x (Bop _ _ e1 e2) = occursFree x e1 || occursFree x e2
occursFree x (Asgn _ e1 e2) = occursFree x e1 || occursFree x e2
occursFree x (Let _ y _ e1 e2) = occursFree x e1 || (occursFree x e2 && x /= y)
occursFree x (LetRec _ f y _ _ e1 e2) = (occursFree x e1 && x /= f && x /= y) || (occursFree x e2 && x /= f)
occursFree x (Abs _ y _ e) = occursFree x e && x /= y
occursFree x (ITE _ e1 e2 e3) = occursFree x e1 || occursFree x e2 || occursFree x e3
occursFree x (Case _ e z e1 y e2) = occursFree x e || (occursFree x e1  && x /= z) || (occursFree x e2  && x /= y)
occursFree _ Prim{} = False

-- Get the list of free variables in an expression excluding the bound variables
-- that are passed as the second argument (as a set for efficiency). You may
-- find it useful to look at the Set library from Data.Set
-- (https://hackage-content.haskell.org/package/containers-0.8/docs/Data-Set.html)
freeVars :: Exp -> S.Set String -> [String]
freeVars expr b = nub $ freeVarsAux expr b []
  where
    freeVarsAux Unit{} _ aux = aux
    freeVarsAux NumLit{} _ aux = aux
    freeVarsAux BoolLit{} _ aux = aux
    freeVarsAux (Var _ y) bound aux = if S.member y bound then aux else y:aux
    freeVarsAux (Nil _ _) _ aux = aux
    freeVarsAux (Cons _ e1 e2) bound aux = freeVarsAux e1 bound (freeVarsAux e2 bound aux)
    freeVarsAux (CaseL _ e e1 z y e2) bound aux = freeVarsAux e bound (freeVarsAux e1 bound (freeVarsAux e2 (S.insert y (S.insert z bound)) aux))
    freeVarsAux (Tuple _ es) bound aux = foldr (`freeVarsAux` bound) aux es
    freeVarsAux (Ref _ e) bound aux = freeVarsAux e bound aux
    freeVarsAux (Deref _ e) bound aux = freeVarsAux e bound aux
    freeVarsAux (App _ e1 e2) bound aux = freeVarsAux e1 bound (freeVarsAux e2 bound aux)
    freeVarsAux (Uop _ _ e) bound aux = freeVarsAux e bound aux
    freeVarsAux (Proj _ _ e) bound aux = freeVarsAux e bound aux
    freeVarsAux (Inl _ _ e) bound aux = freeVarsAux e bound aux
    freeVarsAux (Inr _ _ e) bound aux = freeVarsAux e bound aux
    freeVarsAux (Bop _ _ e1 e2) bound aux = freeVarsAux e1 bound (freeVarsAux e2 bound aux)
    freeVarsAux (Asgn _ e1 e2) bound aux = freeVarsAux e1 bound (freeVarsAux e2 bound aux)
    freeVarsAux (Let _ y _ e1 e2) bound aux = freeVarsAux e1 bound (freeVarsAux e2 (S.insert y bound) aux)
    freeVarsAux (LetRec _ f y _ _ e1 e2) bound aux = freeVarsAux e1 (S.insert y (S.insert f bound)) (freeVarsAux e2 bound aux)
    freeVarsAux (Abs _ y _ e) bound aux = freeVarsAux e (S.insert y bound) aux
    freeVarsAux (ITE _ e1 e2 e3) bound aux = freeVarsAux e1 bound (freeVarsAux e2 bound (freeVarsAux e3 bound aux))
    freeVarsAux (Case _ e z e1 y e2) bound aux = freeVarsAux e bound (freeVarsAux e1 (S.insert z bound) (freeVarsAux e2 (S.insert y bound) aux))
    freeVarsAux Prim{} _ aux = aux

-- Values. The result of evaluation.
type Loc = Integer

data Value =
  -- A memory location
    Memloc Loc
  -- A unit value
  | VUnit
  -- A integer value
  | VNum Integer
  -- A boolean value
  | VBool Bool
  -- A closure. Env is the environment where the closure was created,
  -- String is the name of the function, String is the name of the argument,
  -- Exp is the body of the function
  | VClo Env String String Exp
  -- A pair
  | VTuple [Value]
  -- A left injection
  | VInl Value
  -- A right injection
  | VInr Value
  -- A list
  | VList [Value]
  deriving (Eq,Show)

-- The evaluation environment. Maps variables to values.
type Env = M.Map String Value

-- The execution "heap", mapping memory location to values.
type Store = M.Map Loc Value