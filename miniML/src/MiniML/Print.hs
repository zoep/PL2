module MiniML.Print where

import Prettyprinter
import Prettyprinter.Render.Text (renderStrict)
import qualified Data.Text as T (unpack)
import qualified Data.Text.IO as TIO (putStrLn)

import MiniML.Syntax

-- A pretty printer of miniML types and terms with minimal parenthesization.

-- Top-level functions. Mostly self-explanatory. You may ignore the rest of the
-- implementation details.

-- Show an expression as a string
showExp :: Exp -> String
showExp = T.unpack . renderStrict . layoutSmart optsShow . prettyExp 0

-- Print an expression in stdout
printExp :: Exp -> IO ()
printExp = TIO.putStrLn . renderStrict . layoutSmart optsPrint . prettyExp 0

-- Show a type as a string
showType :: Type -> String
showType = T.unpack . renderStrict . layoutSmart optsShow . prettyType 0

-- Print a type in stdout
printType :: Type -> IO ()
printType = TIO.putStrLn . renderStrict . layoutSmart optsPrint . prettyType 0

-- options for printing in stdout. Max line width is 50 chars.
optsPrint :: LayoutOptions
optsPrint = LayoutOptions { layoutPageWidth = AvailablePerLine 50 1 }

-- options for showing as string. No line breaks.
optsShow :: LayoutOptions
optsShow = LayoutOptions { layoutPageWidth = Unbounded }

-- Print a value in stdout
printValue :: Value -> IO ()
printValue = TIO.putStrLn . renderStrict . layoutSmart optsPrint . prettyValue

{- The pretty printer is based on the following unambiguous miniML grammar -}

{-

Types
-----

t0 ::= t1 -> t0
    | t1

t1 ::= t1 + t2
   | t2

t2 ::= t2 * t3
   | t3

t3 := ref t3 | list t3 | t4

t4 ::= () | Int | Bool | (t0)

Terms
-----

e0 ::= let x : t = e0 in e0
   | let rec f (x : t) : t = e0 in e0
   | if e0 then e0 else e0
   | case e0 of x -> e0 | y -> e0
   | case e0 of [] -> e0 | x::xs -> e0
   | fun (x : t) -> e0
   | e1

e1 ::= e1 := e2
   | e2

-- comparison operators
e2 ::= e2 [op] e3     where [op] ∈ { <, <=, >, >=, ==}
   | e3

-- list cons
e3 ::= e4 :: e3
   | e4

-- additive operators
e4 ::= e4 [op] e5     where [op] ∈ { + , - }
   | e5

-- multiplicative operators
e5 ::= e5 [op] e6    where [op] ∈ { *, / }
   | e6

-- unary and prefix operators
e6 ::= ~ e6
   | e7

- function application
e7 ::= e7 e8
   | e8

- reference, dereference, fst, snd, inl, inr
e8 ::= !e8 | ref e8
   | fst e8 | snd e8
   | inl(t) e8 | inr(t) e8
   | e9

- atomic expressions
e9 ::= () | n | true | false | [] | (e0, e0) | (e0) | x

-}

-- Pretty printing of types

-- Precedence level of types
levelOfType :: Type -> Int
levelOfType TUnit = 4
levelOfType TInt = 4
levelOfType TBool = 4
levelOfType (TVar _) = 4
levelOfType (TRef _) = 3
levelOfType (TList _) = 3
levelOfType (TLazy _) = 3
levelOfType (TProd _ _) = 2
levelOfType (TSum _ _) = 1
levelOfType (TArrow _ _) = 0


prettyLst :: [Doc ann] -> Doc ann
prettyLst = align . sep

-- Pretty printer for types. Takes as input the current level of precedence and
-- the type.
prettyType :: Int -> Type -> Doc ann
prettyType level typ | level > levelOfType typ = parens $ prettyType 0 typ
prettyType _     typ = case typ of
    TUnit        -> pretty "()"
    TVar a  -> pretty a
    -- TVar False a -> pretty $ "_weak" <> a
    TInt         -> pretty "int"
    TBool        -> pretty "bool"
    TRef t       -> prettyOp1 prettyType lvl "ref" t
    TList t      -> prettyOp1 prettyType lvl "list" t
    TLazy t      -> prettyOp1 prettyType lvl "lazy" t
    TProd t1 t2  -> prettyOp2Left prettyType lvl "*" t1 t2
    TSum t1 t2   -> prettyOp2Left prettyType lvl "+" t1 t2
    TArrow t1 t2 -> prettyOp2Right prettyType lvl "->" t1 t2
  where
    lvl = levelOfType typ


-- Pretty printing of terms

-- Precedence level of expressions
levelOfExp :: Exp -> Int
-- atomic
levelOfExp Unit{} = 11
levelOfExp NumLit{} = 11
levelOfExp BoolLit{} = 11
levelOfExp Var{} = 11
levelOfExp Tuple{} = 11
levelOfExp Nil{} = 11
-- ref and deref
levelOfExp Ref{} = 10
levelOfExp Deref{} = 10
levelOfExp Proj{} = 10
levelOfExp Inl{} = 10
levelOfExp Inr{} = 10
levelOfExp Prim{} = 10
-- function application
levelOfExp App{} = 9
-- unary
levelOfExp Uop{} = 8
-- multiplicative
levelOfExp (Bop _ Mult _ _) = 7
levelOfExp (Bop _ Div _ _) = 7
-- additive
levelOfExp (Bop _ Plus _ _) = 6
levelOfExp (Bop _ Minus _ _) = 6
-- cons
levelOfExp Cons{} = 5
-- comparison and equality
levelOfExp (Bop _ Gt _ _) = 4
levelOfExp (Bop _ Ge _ _) = 4
levelOfExp (Bop _ Lt _ _) = 4
levelOfExp (Bop _ Le _ _) = 4
levelOfExp (Bop _ Eq _ _) = 4
-- boolean and
levelOfExp (Bop _ And _ _) = 3
-- boolean or
levelOfExp (Bop _ Or _ _) = 2
-- assign
levelOfExp Asgn{} = 1
-- let and functions
levelOfExp Let{} = 0
levelOfExp LetRec{} = 0
levelOfExp Abs{} = 0
levelOfExp ITE{} = 0
levelOfExp Case{} = 0
levelOfExp CaseL{} = 0


-- Pretty printer for expressions. Takes as input the current level of
-- precedence and the expression.
prettyExp :: Int -> Exp -> Doc ann
-- parens
prettyExp level e | level > levelOfExp e = parens $ prettyExp 0 e
prettyExp _ e = case e of
  -- atomic
  Unit _          -> pretty "()"
  NumLit _ n      -> pretty n
  BoolLit _ b     -> pretty $ if b then "true" else "false"
  Var _ x         -> pretty x
  Tuple _ es      -> tupled $ prettyExp lvl <$> es
  -- ref and deref
  Ref _ e1        -> prettyOp1 prettyExp lvl "ref" e1
  Deref _ e1      -> pretty "!" <> prettyExp lvl e1
  -- nil and cons
  Nil _ Nothing   -> pretty "nil"
  Nil _ (Just ty) -> pretty "nil[" <+> prettyType 0 ty <> pretty "]"
  Cons _ e1 e2    -> prettyOp2Right prettyExp (levelOfExp e) "::" e1 e2
  -- application
  App _ e1 e2     -> nest 2 . sep $ [prettyExp lvl e1, prettyExp (lvl+1) e2]
  -- unary
  Uop _ Not e1    -> prettyOp1 prettyExp lvl "~" e1
  Proj _ 0 e1     -> prettyOp1 prettyExp lvl "fst" e1
  Proj _ 1 e1     -> prettyOp1 prettyExp lvl "snd" e1
  Proj _ i e1     -> prettyOp1 prettyExp lvl ("#" <> show i) e1
  Inl _ (Just t) e1      -> pretty "inl[" <> prettyType 0 t <> pretty "]" <+> prettyExp lvl e1
  Inr _ (Just t) e1      -> pretty "inr[" <> prettyType 0 t <> pretty "]" <+> prettyExp lvl e1
  Inl _ Nothing e1      -> pretty "inl" <+> prettyExp lvl e1  
  Inr _ Nothing e1      -> pretty "inr"<+> prettyExp lvl e1  
  -- left assoc binary ops
  Bop _ bop e1 e2 -> prettyOp2Left prettyExp (levelOfExp e) (prettyBop bop) e1 e2
  -- assign
  Asgn _ e1 e2    -> prettyOp2Right prettyExp (levelOfExp e) ":=" e1 e2
  -- let, let rec, function, ite, case
  Let _ x (Just typ) e1 e2 ->
    sep [ nest 2 $ sep [ pretty "let" <+> pretty x <+> 
                         colon <+> prettyType lvl typ <+> pretty "="
                       , prettyExp lvl e1 ]
        , pretty "in"
        , prettyExp lvl e2 ]
  Let _ x Nothing e1 e2 ->
    sep [ nest 2 $ sep [ pretty "let" <+> pretty x <+> pretty "="
                       , prettyExp lvl e1 ]
        , pretty "in"
        , prettyExp lvl e2 ]
  LetRec _ f x otyp ortyp e1 e2 ->
    sep [ nest 2 $ sep [ pretty "let rec" <+>
                         pretty f <+> 
                         case otyp of
                           Just typ -> parens (pretty x <+> colon <+> prettyType 0 typ)
                           Nothing -> pretty x
                         <+>
                         case ortyp of
                           Just rtyp -> colon <+> prettyType 0 rtyp <+> pretty "="
                           Nothing -> pretty "="
                       , prettyExp lvl e1 ]
        , pretty "in"
        , prettyExp lvl e2 ]
  Abs _ x (Just typ) e1 ->
    nest 2 $ sep [ pretty "fun" <+> pretty "(" <+> pretty x <+> colon <+> prettyType lvl typ <+> pretty ")" <+> pretty "->"
                 , prettyExp lvl e1 ]
  Abs _ x Nothing e1 ->
    nest 2 $ sep [ pretty "fun" <+> pretty x <+> pretty "->"
                 , prettyExp lvl e1 ]
  ITE _ e1 e2 e3 ->
    sep [ nest 2 $ sep [ pretty "if" , prettyExp lvl e1 ]
        , nest 2 $ sep [ pretty "then" , prettyExp lvl e2 ]
        , nest 2 $ sep [ pretty "else" , prettyExp lvl e3 ] ]
  Case _ e1 x e2 y e3 ->
    sep [ sep [nest 2 $ sep [ pretty "case" , prettyExp lvl e1], pretty "of" ]
        , nest 2 $ sep [ pretty "|" <+> pretty "inl" <+> pretty x <+> pretty "->", prettyExp lvl e2 ]
        , nest 2 $ sep [ pretty "|" <+> pretty "inr" <+> pretty y <+> pretty "->", prettyExp lvl e3 ] ]
  CaseL _ e1 e2 x y e3 ->
    sep [ sep [nest 2 $ sep [ pretty "case" , prettyExp lvl e1], pretty "of" ]
        , nest 2 $ sep [ pretty "|" <+> pretty "nil" <+> pretty "->", prettyExp lvl e2 ]
        , nest 2 $ sep [ pretty "|" <+> pretty x <+> pretty "::" <+> pretty y <+> pretty "->", prettyExp lvl e3 ] ]
  Prim _ f e1 -> prettyOp1 prettyExp lvl f e1

  where lvl = levelOfExp e

prettyBop :: Bop -> String
prettyBop Mult = "*"
prettyBop Div = "/"
prettyBop Plus = "+"
prettyBop Minus = "-"
prettyBop Eq = "=="
prettyBop Lt = "<"
prettyBop Le = "<="
prettyBop Gt = ">"
prettyBop Ge = ">="
prettyBop And = "&&"
prettyBop Or = "||"

prettyOp1 :: (Int -> a -> Doc ann) -> Int -> String-> a -> Doc ann
prettyOp1 printer level op e = pretty op <+> printer level e

prettyOp2Left :: (Int -> a -> Doc ann) -> Int -> String -> a -> a -> Doc ann
prettyOp2Left printer level op e1 e2 = prettyLst [printer level e1 , pretty op, printer (level + 1) e2]

prettyOp2Right :: (Int -> a -> Doc ann) -> Int -> String -> a -> a -> Doc ann
prettyOp2Right printer level op e1 e2 = prettyLst [printer (level + 1) e1 , pretty op, printer level e2]

prettyValue :: Value -> Doc ann
prettyValue VUnit = pretty "()"
prettyValue (VNum n) = pretty n
prettyValue (VBool b) = pretty $ if b then "true" else "false"
prettyValue VClo{} = pretty "<function>"
prettyValue (VTuple vs) = tupled (map prettyValue vs)
prettyValue (VInl v) = pretty "inl" <+> prettyValue v
prettyValue (VInr v) = pretty "inr" <+> prettyValue v
prettyValue (VList vs) = brackets $ hsep $ punctuate comma (map prettyValue vs)
prettyValue Memloc{} = pretty "<ref>"

