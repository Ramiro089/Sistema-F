{
module Parse where
import Common
import Data.Maybe
import Data.Char
}

%monad { P } { thenP } { returnP }
%name parseStmt Def
%name term Exp

%tokentype { Token }
%lexer { lexer } { TEOF }

%token
    '='          { TEquals }
    ':'          { TColon }
    '\\'         { TAbs }
    '.'          { TDot }
    '('          { TOpen }
    ')'          { TClose }
    '->'         { TArrow }
    -- Sistema F
    '\\/'        { TAnyType }
    '/\\'        { TForAll }
    '<'          { TOpenBracket }
    '>'          { TCloseBracket }
    -- Bool
    'T'          { TTrue }
    'F'          { TFalse }
    'Bool'       { TTypeBool }
    'if'         { TIf }
    'then'       { TThen }
    'else'       { TElse }
    -- Nat
    '0'          { TZero }
    'suc'        { TSuc }
    'R'          { TNatRec }
    'Nat'        { TTypeNat }
    -- List
    'nil'        { TNil }
    'cons'       { TCons }
    'RL'         { TListRec }
    'List'       { TTypeList }
    VAR          { TVar $$ }
    TYPEE        { TTypeE }
    DEF          { TDef }
    ANY          { TAny $$ }


%left '<' '>'
%right '/\\' '.'
------------
%left '=' 
%right '->'
%right '\\' '.' 
------------
%right 'suc' 
%right 'cons'
%left 'ifthenelse'
%right 'R' 
%right 'RL'

%%

Def     :  Defexp                      { $1 }
        |  Exp	                       { Eval $1 }

Defexp  : DEF VAR '=' Exp              { Def $2 $4 } 

Exp     :: { LamTerm }
        : '/\\'  ANY '.' Exp           { LTAbs $2 $4 }
      --| Exp '<' Type '>'             { LTApp $1 $3 } 
        | '\\' VAR ':' X '.' Exp       { LAbs $2 $4 $6 }
        | NAbs                         { $1 }

X       :: { Type }
        : Type                         { $1 }
        | ANY                          { VarT $1 }

NAbs    :: { LamTerm }
        : Exp '<' Type '>'             { LTApp $1 $3 }
        | NAbs Atom                    { LApp $1 $2 }
        | 'suc' NAbs                   { LSuc $2 }
        | 'cons' NAbs NAbs             { LCons $2 $3 }
        | 'if' NAbs 'then' NAbs 'else' NAbs  { LIfThenElse $2 $4 $6 }
        | 'R' NAbs NAbs NAbs           { LRec $2 $3 $4 }
        | 'RL' NAbs NAbs NAbs          { LRecL $2 $3 $4 }
        | Atom                         { $1 }

Atom    :: { LamTerm }
        : VAR                          { LVar $1 }  
        | '0'                          { LZero }
        | 'T'                          { LTrue }
        | 'F'                          { LFalse }
        | 'nil'                        { LNil }
        | '(' Exp ')'                  { $2 }

Type    : TYPEE                        { EmptyT }
        | '\\/' ANY '.' Type           { ForAllT $4 }
        | Type '->' Type               { FunT $1 $3 }
        | 'Nat'                        { NatT }
        | 'Bool'                       { BoolT }
        | 'List' Type                  { ListT $2 }
        | '(' Type ')'                 { $2 }
        | ANY                          { VarT $1 }

{
data ParseResult a = Ok a | Failed String deriving Show         

type P a = String -> ParseResult a

thenP :: P a -> (a -> P b) -> P b
m `thenP` k = \s -> case m s  of
                      Ok a     -> k a s 
                      Failed e -> Failed e
                         
returnP :: a -> P a
returnP a = \s -> Ok a

failP :: String -> P a
failP err = \s -> Failed err

catchP :: P a -> (String -> P a) -> P a
catchP m k = \s -> case m s  of
                     Ok a     -> Ok a
                     Failed e -> k e s

happyError :: P a
happyError = \s -> Failed $ "Error de parseo\n"++(s)

data Token = TVar String
           | TTypeE
           | TDef
           | TAbs
           | TDot
           | TOpen
           | TClose 
           | TColon
           | TArrow
           | TEquals
           | TEOF
           -- Sistema F
           | TForAll
           | TAnyType
           | TOpenBracket
           | TCloseBracket
           | TAny String
           -- Bool
           | TTrue
           | TFalse
           | TTypeBool
           | TIf
           | TThen
           | TElse
           -- Nat
           | TZero
           | TSuc
           | TNatRec
           | TTypeNat
           -- List
           | TNil
           | TCons
           | TListRec
           | TTypeList
           deriving Show

----------------------------------
lexer cont s = case s of
                 [] -> cont TEOF []
                 (c:cs) | isSpace c -> lexer cont cs
                        | isAlpha c -> lexVar (c:cs)
                 ('\\':('/':cs)) -> cont TAnyType cs
                 ('/':('\\':cs)) -> cont TForAll cs
                 ('\\':cs)-> cont TAbs cs
                 ('.':cs) -> cont TDot cs
                 ('(':cs) -> cont TOpen cs
                 ('-':('>':cs)) -> cont TArrow cs
                 (')':cs) -> cont TClose cs
                 (':':cs) -> cont TColon cs
                 ('=':cs) -> cont TEquals cs
                 ('<':cs) -> cont TOpenBracket cs
                 ('>':cs) -> cont TCloseBracket cs
                 ('0':cs) -> cont TZero cs
                 unknown -> Failed $ "No se reconoce "++(show $ take 10 unknown)++ "..."

    where lexVar cs = case span isAlpha cs of
                        ("E",rest)    -> cont TTypeE rest
                        ("def",rest)  -> cont TDef rest
                        -- Bool
                        ("if", rest) -> cont TIf rest
                        ("then", rest) -> cont TThen rest
                        ("else", rest) -> cont TElse rest
                        ("T", rest) -> cont TTrue rest
                        ("F", rest) -> cont TFalse rest
                        ("Bool", rest) -> cont TTypeBool rest
                        -- Nat
                        ("suc", rest) -> cont TSuc rest
                        ("R", rest) -> cont TNatRec rest
                        ("Nat", rest) -> cont TTypeNat rest
                        -- List
                        ("nil", rest) -> cont TNil rest
                        ("cons", rest) -> cont TCons rest
                        ("RL", rest) -> cont TListRec rest
                        ("List", rest) -> cont TTypeList rest
                        (var, rest) | all isUpper var -> cont (TAny var) rest
                                    | otherwise       -> cont (TVar var) rest
}