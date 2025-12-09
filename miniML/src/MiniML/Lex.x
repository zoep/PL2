{
module MiniML.Lex
  ( LEX (..)
  , Lexeme (..)
  , AlexPosn (..)
  , lexer
  , posn
  , showposn
  , name
  , value
  , lastPos
  ) where

import Prelude hiding (EQ, GT, LT)

}

%wrapper "posn"

$digit = 0-9                    -- digits
$alpha = [a-z A-Z]              -- alphabetic characters
$ident = [$alpha _]
$space = [\ \t\f\v\r]
$negative = \-

tokens :-

  $white+                               ;

  -- reserved words
  let                                   { mk LET }
  rec                                   { mk REC }
  in                                    { mk IN }
  fun                                   { mk FUN }
  ref                                   { mk REF }
  list                                  { mk LIST }
  if                                    { mk IF }
  then                                  { mk THEN }
  else                                  { mk ELSE }
  fst                                   { mk FST }
  snd                                   { mk SND }
  true                                  { mk TRUE }
  false                                 { mk FALSE }
  case                                  { mk CASE }
  of                                    { mk OF }
  inl                                   { mk INL }
  inr                                   { mk INR }
  nil                                   { mk NIL }
  
  -- builtin types
  bool                                  { mk BOOL }
  int                                   { mk INT }

  lazy                                  { mk LAZY }
  force                                 { mk FORCE }


  -- symbols
  ":="                                  { mk ASSIGN }
  "->"                                  { mk ARROW }
  "!"                                   { mk BANG }
  "()"                                  { mk UNIT }

  "+"                                   { mk PLUS }
  "-"                                   { mk MINUS }
  "*"                                   { mk MULT }
  "/"                                   { mk DIV }

  "=="                                  { mk EQEQ }
  "/="                                  { mk NEQ }
  ">="                                  { mk GE }
  "<="                                  { mk LE }
  ">"                                   { mk GT }
  "<"                                   { mk LT }
  "~"                                   { mk NOT }
  "&&"                                  { mk AND }
  "||"                                  { mk OR }

  "("                                   { mk LPAREN }
  ")"                                   { mk RPAREN }

  ","                                   { mk COMMA }

  "="                                   { mk EQ }
  ":"                                   { mk COLON }
  "|"                                   { mk BAR }

  "::"                                  { mk CONS }
  "["                                   { mk LBRACKET }
  "]"                                   { mk RBRACKET }

  -- identifiers
  $ident ($ident | $digit)*             { \ p s -> L (ID s) p }

  -- literals
  $negative? $digit+                    { \ p s -> L (ILIT (read s)) p }

{

data LEX =

  -- reserved words
    LET
  | REC
  | IN
  | FUN
  | REF
  | LIST
  | IF
  | THEN
  | ELSE
  | FIX
  | FST
  | SND
  | TRUE
  | FALSE
  | CASE
  | OF
  | INL
  | INR
  | NIL
  | CONS

  -- primitives
  | LAZY
  | FORCE

  -- builtin types
  | INT
  | BOOL
  | UNIT

  -- symbols
  | ASSIGN
  | ARROW
  | BANG

  | PLUS
  | MINUS
  | MULT
  | DIV

  | EQEQ
  | NEQ
  | GE
  | LE
  | GT
  | LT
  | NOT
  | AND
  | OR

  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | COMMA
  | EQ
  | COLON
  | BAR

  -- identifiers
  | ID String

  -- literals
  | ILIT Integer

  deriving (Eq, Show)

data Lexeme = L LEX AlexPosn
  deriving (Eq, Show)

showposn (AlexPn _ line column) =
  concat [show line, ":", show column]

lastPos :: AlexPosn
lastPos = AlexPn (-1) (-1) (-1)

posn :: Lexeme -> AlexPosn
posn (L _ p) = p

name :: Lexeme -> String
name (L (ID s) _) = s
name _ = error "unsupported arg to name"

value :: Lexeme -> Integer
value (L (ILIT i) _) = i
value _ = error "unsupported arg to value"

mk :: LEX -> (AlexPosn -> String -> Lexeme)
mk lexeme p _ = L lexeme p

lexer :: String -> [Lexeme]
lexer = alexScanTokens
}