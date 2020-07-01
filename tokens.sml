structure MLMinusTokens =
struct

  datatype token =
    ID of Ast.ident
  | INT of int
  | REAL of real
  | CHAR of char
  | STRING of string
  | TRUE
  | FALSE
  | ORELSE 
  | ANDALSO 
  | PLUS 
  | MINUS 
  | TIMES 
  | DIV
  | SLASH
  | MOD
  | EQ 
  | NE
  | LT
  | LE
  | GT
  | GE
  | CAT
  | LP
  | RP
  | LBRACK
  | RBRACK
  | NIL
  | DCOLON
  | AT
  | FN
  | DARROW
  | LET
  | LETREC
  | IN
  | END
  | IF
  | THEN
  | ELSE
  | SEL of int
  | COMMA
  | VAL
  | FUN
  | SEMI
  | REF
  | BANG
  | ASSIGN
  | WHILE
  | DO
  | EOF

  fun toString(t : token) : string =
    case t of
           ID(s)               => String.concat ["ID(", s, ")"]
         | INT(n)              => String.concat ["INT(", Int.toString n, ")"]
         | REAL(n)             => String.concat ["REAL(", Real.toString n, ")"]
         | CHAR c              => String.concat ["CHAR(", Char.toString c, ")"]
         | STRING(s)           => String.concat ["STRING(", s, ")"]
         | TRUE                => "TRUE"
         | FALSE               => "FALSE"
         | ORELSE              => "ORELSE"
         | ANDALSO             => "ANDALSO"
         | PLUS                => "PLUS"
         | MINUS               => "MINUS"
         | TIMES               => "TIMES"
         | DIV                 => "DIV"
         | SLASH               => "SLASH"
         | MOD                 => "MOD"
         | EQ                  => "EQ"
         | NE                  => "NE"
         | LT                  => "LT"
         | LE                  => "LE"
         | GT                  => "GT"
         | GE                  => "GE"
         | CAT                 => "CAT"
         | LP                  => "LPAREN"
         | RP                  => "RPAREN"
         | LBRACK              => "LBRACK"
         | RBRACK              => "RBRACK"
         | NIL                 => "NIL"
         | DCOLON              => "DCOLON"
         | AT                  => "AT"
         | FN                  => "FN"
         | DARROW              => "DARROW"
         | LET                 => "LET"
         | LETREC              => "LETREC"
         | IN                  => "IN"
         | END                 => "END"
         | IF                  => "IF"
         | THEN                => "THEN"
         | ELSE                => "ELSE"
         | SEL(n)              => String.concat ["SEL", Int.toString n]
         | COMMA               => "COMMA"
         | VAL                 => "VAL"
         | FUN                 => "FUN"
         | SEMI                => "SEMI"
         | REF                 => "REF"
         | BANG                => "BANG"
         | ASSIGN              => "ASSIGN"
         | WHILE               => "WHILE"
         | DO                  => "DO"
         | EOF                 => "EOF"

end
