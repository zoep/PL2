module MiniML.Syntax where

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
          | TList  Type
          | TVar   String
   deriving (Eq,Show,Ord)

data TypeScheme = Type Type
                | Forall [String] Type
   deriving (Eq,Show)

data Bop = Plus | Minus | Mult | Div
         | And | Or
         | Lt | Gt | Le | Ge
         | Eq
   deriving (Eq,Show)

data Uop = Not
   deriving (Eq,Show)

-- Expressions

-- Note: lambda abstractions have an optional type annotation for the result
-- type. This is filled by the annotate pass in Typecheck.hs. It is needed so
-- that closure values can be correctly type annotated and typechecked.

data Exp =
  -- STLC
    Var     Posn String
  | App     Posn Exp Exp
  | Abs     Posn String (Maybe Type) (Maybe Type) Exp
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
  -- Pairs
  | Pair    Posn Exp Exp
  | Fst     Posn Exp
  | Snd     Posn Exp
  -- Lists
  | Nil     Posn
  | Cons    Posn Exp Exp
  | CaseL   Posn Exp Exp String String Exp
  -- Sums
  | Inl     Posn Exp
  | Inr     Posn Exp
  | Case    Posn Exp Id Exp Id Exp
  -- Let
  | Let     Posn Id (Maybe Type) Exp Exp
  -- Let rec
  | LetRec  Posn Id Id (Maybe Type) (Maybe Type) Exp Exp
  deriving Show


-- Custom equality for expressions that ignores the source code position
instance Eq Exp where
    Var _ x              == Var _ y                   = x == y
    App _ e1 e2          == App _ e1' e2'             = e1 == e1' && e2 == e2'
    Abs _ x t mt e       == Abs _ x' t' mt' e'        = x == x' && t == t' && mt == mt' && e == e'
    Unit _               == Unit _                    = True
    NumLit _ n1          == NumLit _ n2               = n1 == n2
    BoolLit _ b1         == BoolLit _ b2              = b1 == b2
    ITE _ e1 e2 e3       == ITE _ e1' e2' e3'         = e1 == e1' && e2 == e2' && e3 == e3'
    Bop _ b e1 e2        == Bop _ b' e1' e2'          = b == b' && e1 == e1' && e2 == e2'
    Uop _ u e1           == Uop _ u' e1'              = u == u'&& e1 == e1'
    Nil _                == Nil _                     = True
    Cons _ e1 e2         == Cons _ e1' e2'            = e1 == e1' && e2 == e2'
    CaseL _ e1 e2 x y e3 == CaseL _ e1' e2' x' y' e3' = e1 == e1' && e2 == e2' && x == x' && y == y' && e3 == e3'
    Pair _ e1 e2         == Pair _ e1' e2'            = e1 == e1' && e2 == e2'
    Fst _ e1             == Fst _ e1'                 = e1 == e1'
    Snd _ e1             == Snd _ e1'                 = e1 == e1'
    Inl _ e1             == Inl _ e1'                 = e1 == e1'
    Inr _ e1             == Inr _ e1'                 = e1 == e1'
    Case _ e1 x e2 y e3  == Case _ e1' x' e2' y' e3'  = e1 == e1' && x == x' && e2 == e2' && y == y' && e3 == e3'
    Let _ x t1 e1 e2     == Let _ x' t1' e1' e2'      = x == x' && e1 == e1' && t1 == t1' && e2 == e2'
    LetRec _ f x t r b e == LetRec _ g y t' r' b' e'  = f == g && x == y && t == t' && r == r' && b == b'  && e == e'
    _                    == _                         = False


nowhere :: Posn
nowhere = AlexPn 0 0 0

-- Get the source code position of an expression
getPosn :: Exp -> Posn
getPosn (Unit p) = p
getPosn (NumLit p _) = p
getPosn (BoolLit p _) = p
getPosn (Var p _) = p
getPosn (Pair p _ _) = p
getPosn (App p _ _) = p
getPosn (Uop p _ _) = p
getPosn (Nil p) = p
getPosn (Cons p _ _) = p
getPosn (CaseL p _ _ _ _ _) = p
getPosn (Fst p _) = p
getPosn (Snd p _) = p
getPosn (Inl p _) = p
getPosn (Inr p _) = p
getPosn (Bop p _ _ _) = p
getPosn (Let p _ _ _ _) = p
getPosn (LetRec p _ _ _ _ _ _) = p
getPosn (Abs p _ _ _ _) = p
getPosn (ITE p _ _ _) = p
getPosn (Case p _ _ _ _ _) = p
