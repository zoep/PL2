{
module MiniML.Parse (module MiniML.Parse, showposn) where
import Prelude hiding (EQ, GT, LT)
import MiniML.Lex
import MiniML.Syntax
import MiniML.Error
}

%name parse
%monad { Error } { (>>=) } { pure }
%tokentype { Lexeme }
%error { parseError }

%token

  -- reserved word
  'let'                       { L LET _ }
  'rec'                       { L REC _ }
  'in'                        { L IN _ }
  'fun'                       { L FUN _ }
  'ref'                       { L REF _ }
  'list'                      { L LIST _ }
  'if'                        { L IF _ }
  'then'                      { L THEN _ }
  'else'                      { L ELSE _ }
  'fst'                       { L FST _ }
  'snd'                       { L SND _ }
  'true'                      { L TRUE _ }
  'false'                     { L FALSE _ }
  'case'                      { L CASE _ }
  'of'                        { L OF _ }
  'inl'                       { L INL _ }
  'inr'                       { L INR _ }
  
  'int'                       { L INT _ }
  'bool'                      { L BOOL _ }

  -- symbols
  ':='                        { L ASSIGN _ }
  '->'                        { L ARROW _ }
  '!'                         { L BANG _ }
  '+'                         { L PLUS _ }
  '-'                         { L MINUS _ }
  '*'                         { L MULT _ }
  '/'                         { L DIV _ }

  '=='                        { L EQEQ _ }
  '/='                        { L NEQ _ }
  '>='                        { L GE _ }
  '<='                        { L LE _ }
  '>'                         { L GT _ }
  '<'                         { L LT _ }
  '~'                         { L NOT _ }

  '&&'                        { L AND _ }
  '||'                        { L OR _ }

  '('                         { L LPAREN _ }
  ')'                         { L RPAREN _ }
  '()'                        { L UNIT _ }

  '='                         { L EQ _ }
  ','                         { L COMMA _ }
  ':'                         { L COLON _ }
  '|'                         { L BAR _ }

  '::'                        { L CONS _ }
  '[]'                        { L NIL _ }

  id                          { L (ID _) _ }

  ilit                        { L (ILIT _) _ }

{- --- associativity and precedence --- -}



%right    ':='
%right    '->'


%left     '||'
%left     '&&'

%left     '==' '/=' '<' '>' '>=' '<='

%right     '::'

%left     '+' '-'
%left     '*' '/'

%nonassoc 'list' '!'

%nonassoc '('

%%

ML : Exp                                                    { $1 }

-- rules --

Type : '()'                                                 { TUnit }
     | 'int'                                                { TInt }
     | 'bool'                                               { TBool }
     | Type '->' Type                                       { TArrow $1 $3 }
     | Type '*' Type                                        { TProd $1 $3 }
     | Type '+' Type                                        { TSum $1 $3 }
     | 'list' Type                                          { TList $2 }
     | '(' Type ')'                                         { $2 }


Exp : 'fun' '(' id ':' Type ')' '->' Exp                    { Abs (posn $1) (name $3) (Just $5) Nothing $8 }
    | 'fun' id '->' Exp                                     { Abs (posn $1) (name $2) Nothing Nothing $4 }
    | 'if' Exp 'then' Exp 'else' Exp                        { ITE (posn $1) $2 $4 $6 }
    | 'let' id ':' Type '=' Exp 'in' Exp                    { Let (posn $1) (name $2) (Just $4) $6 $8 }
    | 'let' id '=' Exp 'in' Exp                             { Let (posn $1) (name $2) Nothing $4 $6 }
    | 'let' 'rec' id '(' id ':' Type ')' ':' Type '=' Exp 'in' Exp
                                                            { LetRec (posn $1) (name $3) (name $5) (Just $7) (Just $10) $12 $14 }
    | 'let' 'rec' id '(' id ':' Type ')' '=' Exp 'in' Exp
                                                            { LetRec (posn $1) (name $3) (name $5) (Just $7) Nothing $10 $12 }
    | 'let' 'rec' id id ':' Type '=' Exp 'in' Exp
                                                            { LetRec (posn $1) (name $3) (name $4) Nothing (Just $6) $8 $10 }
    | 'let' 'rec' id id '=' Exp 'in' Exp
                                                            { LetRec (posn $1) (name $3) (name $4) Nothing Nothing $6 $8 }
    | 'case' Exp 'of' '|' 'inl' id '->' Exp '|' 'inr' id '->' Exp
                                                            { Case (posn $1) $2 (name $6) $8 (name $11) $13 }
    | 'case' Exp 'of' '|' '[]' '->' Exp '|' id '::' id '->' Exp
                                                            { CaseL (posn $1) $2 $7 (name $9) (name $11) $13 }
    | ExpBin                                                { $1 }

-- binary operators
ExpBin : ExpBin '+'  ExpBin                                    { Bop (posn $2) Plus $1 $3 }
    | ExpBin '-'  ExpBin                                    { Bop (posn $2) Minus $1 $3 }
    | ExpBin '*'  ExpBin                                    { Bop (posn $2) Mult $1 $3 }
    | ExpBin '/'  ExpBin                                    { Bop (posn $2) Div  $1 $3 }
    | ExpBin '=='  ExpBin                                   { Bop (posn $2) Eq $1 $3 }
    | ExpBin '/='  ExpBin                                   { Uop (posn $2) Not (Bop (posn $2) Eq $1 $3) }
    | ExpBin '<='  ExpBin                                   { Bop (posn $2) Le $1 $3 }
    | ExpBin '<'   ExpBin                                   { Bop (posn $2) Lt $1 $3 }
    | ExpBin '>='  ExpBin                                   { Bop (posn $2) Ge $1 $3 }
    | ExpBin '>'   ExpBin                                   { Bop (posn $2) Gt $1 $3 }
    | ExpBin '&&'  ExpBin                                   { Bop (posn $2) And $1 $3 }
    | ExpBin '||'  ExpBin                                   { Bop (posn $2) Or $1 $3 }
    | ExpBin '::'  ExpBin                                   { Cons (posn $2) $1 $3 }
    | ExpUn                                                 { $1 }

ExpUn : '~' ExpUn                                           { Uop (posn $1) Not $2 }
    | ExpApp                                                { $1 }

ExpApp : ExpApp ExpUn2                                      { App nowhere $1 $2 } -- TODO fix position
       | ExpUn2                                             { $1 }

ExpUn2 : -- pairs
         'fst' ExpUn2                                       { Fst (posn $1) $2 }
       | 'snd' ExpUn2                                       { Snd (posn $1) $2 }
       -- sums
       | 'inl' ExpUn2                                       { Inl (posn $1) $2 }
       | 'inr' ExpUn2                                       { Inr (posn $1) $2 }
       | ExpAtom                                            { $1 }

ExpAtom: ilit                                               { NumLit (posn $1) (value $1) }
    | 'true'                                                { BoolLit (posn $1) True }
    | 'false'                                               { BoolLit (posn $1) False }
    | '()'                                                  { Unit (posn $1) }
    | '[]'                                                  { Nil (posn $1) }
    | id                                                    { Var (posn $1) (name $1) }
    | '(' Exp ',' Exp ')'                                   { Pair (posn $1) $2 $4 }
    | '(' Exp ')'                                           { $2 }

{

parseError :: [Lexeme] -> Error a
parseError [] = throw (lastPos, "Expected more tokens")
parseError ((L token pn):_) =
  throw (pn, "parsing error at token " ++ show token)

}