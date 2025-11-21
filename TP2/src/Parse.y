{
module Parse where
import Common
import Data.Maybe
import Data.Char

}

%monad { P } { thenP } { returnP }
%name parseStmt Def
%name parseStmts Defs
%name term Exp

%tokentype { Token }
%lexer {lexer} {TEOF}

-- Tokens:
%token
    '='     { TEquals }
    ':'     { TColon }
    '\\'    { TAbs }
    '.'     { TDot }
    '('     { TOpen }
    ')'     { TClose }
    '->'    { TArrow }
    VAR     { TVar $$ }
    TYPEE   { TTypeE }
    DEF     { TDef }

    -- Para Let:
    LET     { TLet }
    IN      { TIn }

    -- Para Nat:
    ZERO    { TZero }
    SUC     { TSuc }
    REC     { TRec }
    NAT     { TNat }

    -- Para Listas:
    NIL     { TNil }
    CONS     { TCons }
    RECL     { TRecL }



-- Precedencias:
-- Precedencias (de mayor a menor)
%left APP            -- aplicación (más fuerte) VER OJO!! No existe el token APP CORREGIR
%left SUC       -- suc
%left CONS      -- cons
%left RECL      -- RL
%left REC       -- rec
%right '\\' '.' LET IN     -- lambda y let (menor precedencia)



%%
-- Reglas Gramaticales:

Def     :  Defexp                      { $1 }
        |  Exp	                       { Eval $1 }
Defexp  : DEF VAR '=' Exp              { Def $2 $4 } 

Exp     :: { LamTerm }
        : '\\' VAR ':' Type '.' Exp    { LAbs $2 $4 $6 }
        
        -- Para Let:
        | LET VAR '=' Exp IN Exp       { LLet $2 $4 $6 }

        -- Para Nat:
        | ZERO                         { LZero }
        | SUC Exp                      { LSuc $2 }
        | REC Exp Exp Exp              {LRec $2 $3 $4}

        -- Para Listas:
        | NIL                          { LNil }
        | CONS Exp Exp                 { LCons $2 $3 }
        | RECL Exp Exp Exp             { LRecL $2 $3 $4}

        | NAbs                         { $1 }
        
        -- Aca tenemos un problema. Si pongo cons zero no tipa pq zero es una exp no una Var ... CORREGIR
NAbs    :: { LamTerm }
        : NAbs Atom                    { LApp $1 $2 }
        | Atom                         { $1 }

Atom    :: { LamTerm }
        : VAR                          { LVar $1 }  
        | '(' Exp ')'                  { $2 }

Type    : NAT                          { NatT}
        | TYPEE                        { EmptyT }
        | Type '->' Type               { FunT $1 $3 }
        | '(' Type ')'                 { $2 }

Defs    : Defexp Defs                  { $1 : $2 }
        |                              { [] }


        
     
{

data ParseResult a = Ok a | Failed String
                     deriving Show                     
type LineNumber = Int
type P a = String -> LineNumber -> ParseResult a

getLineNo :: P LineNumber
getLineNo = \s l -> Ok l

thenP :: P a -> (a -> P b) -> P b
m `thenP` k = \s l-> case m s l of
                         Ok a     -> k a s l
                         Failed e -> Failed e
                         
returnP :: a -> P a
returnP a = \s l-> Ok a

failP :: String -> P a
failP err = \s l -> Failed err

catchP :: P a -> (String -> P a) -> P a
catchP m k = \s l -> case m s l of
                        Ok a     -> Ok a
                        Failed e -> k e s l

happyError :: P a
happyError = \ s i -> Failed $ "Línea "++(show (i::LineNumber))++": Error de parseo\n"++(s)

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

               -- Para Let:
               | TLet
               | TIn

               -- Para Nat:
               | TZero
               | TSuc
               | TRec
               | TNat

               -- Para Listas:
               | TNil 
               | TCons 
               | TRecL
        

               deriving Show

----------------------------------
lexer cont s = case s of
                    [] -> cont TEOF []
                    ('\n':s)  ->  \line -> lexer cont s (line + 1)
                    (c:cs)
                          | isSpace c -> lexer cont cs
                          | isAlpha c -> lexVar (c:cs)
                    ('-':('-':cs)) -> lexer cont $ dropWhile ((/=) '\n') cs
                    ('{':('-':cs)) -> consumirBK 0 0 cont cs	
                    ('-':('}':cs)) -> \ line -> Failed $ "Línea "++(show line)++": Comentario no abierto"
                    ('-':('>':cs)) -> cont TArrow cs
                    ('\\':cs)-> cont TAbs cs
                    ('.':cs) -> cont TDot cs
                    ('(':cs) -> cont TOpen cs
                    ('-':('>':cs)) -> cont TArrow cs
                    (')':cs) -> cont TClose cs
                    (':':cs) -> cont TColon cs
                    ('=':cs) -> cont TEquals cs
                    unknown -> \line -> Failed $ 
                     "Línea "++(show line)++": No se puede reconocer "++(show $ take 10 unknown)++ "..."
                    where lexVar cs = case span isAlpha cs of
                              ("E",rest)    -> cont TTypeE rest
                              ("def",rest)  -> cont TDef rest

                              -- Para Let:
                              ("let", rest) -> cont TLet rest
                              ("in", rest)  -> cont TIn  rest

                              -- Para Nat:
                              ("zero", rest) -> cont TZero rest
                              ("suc", rest ) -> cont TSuc rest 
                              ("rec", rest )   -> cont TRec rest
                              ("Nat", rest ) -> cont TNat rest 

                              -- Para listas:
                              ("nil", rest)  -> cont TNil rest
                              ("cons", rest)  -> cont TCons rest
                              ("recl", rest)  -> cont TRecL rest

                              

                              (var,rest)    -> cont (TVar var) rest
                          consumirBK anidado cl cont s = case s of
                              ('-':('-':cs)) -> consumirBK anidado cl cont $ dropWhile ((/=) '\n') cs
                              ('{':('-':cs)) -> consumirBK (anidado+1) cl cont cs	
                              ('-':('}':cs)) -> case anidado of
                                                  0 -> \line -> lexer cont cs (line+cl)
                                                  _ -> consumirBK (anidado-1) cl cont cs
                              ('\n':cs) -> consumirBK anidado (cl+1) cont cs
                              (_:cs) -> consumirBK anidado cl cont cs     
                                           
stmts_parse s = parseStmts s 1
stmt_parse s = parseStmt s 1
term_parse s = term s 1
}
