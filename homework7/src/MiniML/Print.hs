module MiniML.Print where

import Prettyprinter
import Prettyprinter.Render.Text (renderStrict)
import qualified Data.Text as T (unpack)
import qualified Data.Text.IO as TIO (putStrLn)
import qualified Data.Map as M

import MiniML.Syntax
import MiniML.Values

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


-- Show a configuration (store + value) as a string
showConf :: Store -> Value -> String
showConf s v = T.unpack . renderStrict . layoutSmart optsShow $ prettyConf s v

-- Print a configuration (store + value) in stdout
printConf :: Store -> Value -> IO ()
printConf s v = TIO.putStrLn . renderStrict . layoutSmart optsPrint $ prettyConf s v

-- options for printing in stdout. Max line width is 50 chars.
optsPrint :: LayoutOptions
optsPrint = LayoutOptions { layoutPageWidth = AvailablePerLine 50 1 }

-- options for showing as string. No line breaks.
optsShow :: LayoutOptions
optsShow = LayoutOptions { layoutPageWidth = Unbounded }


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

t3 := ref t3 | t4

t4 ::= () | Int | Bool | (t0)

Terms
-----

e0 ::= let x : t = e0 in e0
   | let rec f (x : t) : t = e0 in e0
   | if e0 then e0 else e0
   | case e0 of x -> e0 | y -> e0
   | fun (x : t) -> e0
   | e1

e1 ::= e1 := e2
   | e2

-- comparison operators
e2 ::= e2 [op] e3     where [op] ∈ { <, <=, >, >=, ==}
   | e3

-- additive operators
e3 ::= e3 [op] e4     where [op] ∈ { + , - }
   | e4

-- multiplicative operators
e4 ::= e4 [op] e5    where [op] ∈ { *, / }
   | e5

-- unary and prefix operators
e5 ::= ~ e5
   | e6

- function application
e6 ::= e6 e7
   | e7

- reference, dereference, fst, snd, inl, inr
e7 ::= !e7 | ref e7
   | fst e7 | snd e7
   | inl(t) e7 | inr(t) e7
   | e8

- atomic expressions
e8 ::= () | n | true | false | (e0, e0) | (e0) | x

-}

-- Pretty printing of types

-- Precedence level of types
levelOfType :: Type -> Int
levelOfType TUnit = 3
levelOfType TInt = 3
levelOfType TBool = 3
levelOfType (TRef _) = 3
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
    TInt         -> pretty "int"
    TBool        -> pretty "bool"
    TRef t       -> prettyOp1 prettyType lvl "ref" t
    TProd t1 t2  -> prettyOp2Left prettyType lvl "*" t1 t2
    TSum t1 t2   -> prettyOp2Left prettyType lvl "+" t1 t2
    TArrow t1 t2 -> prettyOp2Right prettyType lvl "->" t1 t2
  where
    lvl = levelOfType typ


-- Pretty printing of terms

-- Precedence level of expressions
levelOfExp :: Exp -> Int
-- atomic
levelOfExp Unit{} = 10
levelOfExp NumLit{} = 10
levelOfExp BoolLit{} = 10
levelOfExp Var{} = 10
levelOfExp Pair{} = 10
-- ref and deref
levelOfExp Ref{} = 9
levelOfExp Deref{} = 9
levelOfExp Fst{} = 9
levelOfExp Snd{} = 9
levelOfExp Inl{} = 9
levelOfExp Inr{} = 9
-- function application
levelOfExp App{} = 8
-- unary
levelOfExp Uop{} = 7
-- multiplicative
levelOfExp (Bop _ Mult _ _) = 6
levelOfExp (Bop _ Div _ _) = 6
-- additive
levelOfExp (Bop _ Plus _ _) = 5
levelOfExp (Bop _ Minus _ _) = 5
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
  Pair _ e1 e2    -> tupled $ prettyExp lvl <$> [ e1 , e2 ]
  -- ref and deref
  Ref _ e1        -> prettyOp1 prettyExp lvl "ref" e1
  Deref _ e1      -> pretty "!" <> prettyExp lvl e1
  -- application
  App _ e1 e2     -> nest 2 . sep $ [prettyExp lvl e1, prettyExp (lvl+1) e2]
  -- unary
  Uop _ Not e1    -> prettyOp1 prettyExp lvl "~" e1
  Fst _ e1        -> prettyOp1 prettyExp lvl "fst" e1
  Snd _ e1        -> prettyOp1 prettyExp lvl "snd" e1
  Inl _ t e1      -> pretty "inl(" <> prettyType 0 t <> pretty ")" <+> prettyExp lvl e1
  Inr _ t e1      -> pretty "inr(" <> prettyType 0 t <> pretty ")" <+> prettyExp lvl e1
  -- left assoc binary ops
  Bop _ bop e1 e2 -> prettyOp2Left prettyExp (levelOfExp e) (prettyBop bop) e1 e2
  -- assign
  Asgn _ e1 e2    -> prettyOp2Right prettyExp (levelOfExp e) ":=" e1 e2
  -- let, let rec, function, ite, case
  Let _ x typ e1 e2 ->
    sep [ nest 2 $ sep [ pretty "let" <+> pretty x <+> colon <+> prettyType lvl typ <+> pretty "="
                       , prettyExp lvl e1 ]
        , pretty "in"
        , prettyExp lvl e2]
  LetRec _ f x typ rtyp e1 e2 ->
    sep [ nest 2 $ sep [ pretty "let rec" <+>
                         pretty f <+> parens (pretty x <+> colon <+> prettyType 0 typ)
                         <+> colon <+> prettyType 0 rtyp <+> pretty "="
                       , prettyExp lvl e1 ]
        , pretty "in"
        , prettyExp lvl e2 ]
  Abs _ x typ _ e1 ->
    nest 2 $ sep [ pretty "fun" <+> pretty "(" <+> pretty x <+> colon <+> prettyType lvl typ <+> pretty ")" <+> pretty "->"
                 , prettyExp lvl e1 ]
  ITE _ e1 e2 e3 ->
    sep [ nest 2 $ sep [ pretty "if" , prettyExp lvl e1 ]
        , nest 2 $ sep [ pretty "then" , prettyExp lvl e2 ]
        , nest 2 $ sep [ pretty "else" , prettyExp lvl e3 ] ]
  Case _ e1 x e2 y e3 ->
    sep [ sep [nest 2 $ sep [ pretty "case" , prettyExp lvl e1], pretty "of" ]
        , nest 2 $ sep [ pretty "|" <+> pretty "inl" <+> pretty x <+> pretty "->", prettyExp lvl e2 ]
        , nest 2 $ sep [ pretty "|" <+> pretty "inr" <+> pretty y <+> pretty "->", prettyExp lvl e3 ] ]

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

-- Pretty print values
prettyConf :: Store -> Value -> Doc ann
prettyConf store (Memloc l) =
  case M.lookup l store of
   Just v -> pretty "{ contents =" <+> prettyConf store v <+> pretty "}"
   Nothing -> error "Undefined location"
prettyConf _ VUnit = pretty "()"
prettyConf _ (VNum n) = pretty n
prettyConf _ (VBool b) = pretty $ if b then "true" else "false"
prettyConf store (VPair v1 v2) = tupled $ prettyConf store <$> [ v1 , v2 ]
prettyConf store (VInl t v) = pretty "inl(" <> prettyType 0 t <> pretty ")" <+> prettyConf store v
prettyConf store (VInr t v) = pretty "inr(" <> prettyType 0 t <> pretty ")" <+> prettyConf store v
prettyConf _ VClo{} = pretty "<fun>"