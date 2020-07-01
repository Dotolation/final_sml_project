%name MLMinusLexer ;

%let digit = [0-9] ;
%let num = {digit}+ ;
%let intlit = "~"?{digit}+ ;
%let reallit = {intlit}("."{num} | ("E"|"e"){intlit} | "."{num}("E"|"e"){intlit}) ;
%let sel = "#"{digit}+ ;
%let alpha = [a-zA-Z] ;
%let id = ({alpha}({alpha} | {digit} | [_'])*) ;
%let ws = [\n\ \t] ;
%let dquote_str = \"([^"] | "\\\"")*\" ;
%let char = "#"\".\" | "#"\"\\.\" ;
%let blockcomment = "(*" ~(.*"*)".*) "*)" ;

%defs (
  structure T = MLMinusTokens
  type lex_result = T.token
  fun eof() = T.EOF
  exception lex_error of string

  fun trimFirstLast (s : string) : string =
    String.substring(s, 1, String.size s - 2)

  fun trimFirst (s : string) : string =
    String.substring(s, 1, String.size s - 1)

  val intFromString = valOf o Int.fromString
) ;

{intlit}        => ( T.INT (valOf (Int.fromString yytext)) ) ;
{reallit}       => ( T.REAL (valOf (Real.fromString yytext)) ) ;
"("             => ( T.LP ) ;
")"             => ( T.RP ) ;
"["             => ( T.LBRACK ) ;
"]"             => ( T.RBRACK ) ;
"+"             => ( T.PLUS ) ;
"-"             => ( T.MINUS ) ;
"*"             => ( T.TIMES ) ;
"/"             => ( T.SLASH ) ;
"div"           => ( T.DIV ) ;
"mod"           => ( T.MOD ) ;
"^"             => ( T.CAT ) ;
"="             => ( T.EQ ) ;
"<>"            => ( T.NE ) ;
"<"             => ( T.LT ) ;
"<="            => ( T.LE ) ;
">"             => ( T.GT ) ;
">="            => ( T.GE ) ;
"fn"            => ( T.FN ) ;
"=>"            => ( T.DARROW ) ;
"let"           => ( T.LET ) ;
"in"           => ( T.IN ) ;
"end"           => ( T.END ) ;
"true"          => ( T.TRUE ) ;
"false"         => ( T.FALSE ) ;
"orelse"         => ( T.ORELSE ) ;
"andalso"         => ( T.ANDALSO ) ;
"if"         => ( T.IF ) ;
"then"         => ( T.THEN ) ;
"else"         => ( T.ELSE ) ;
","             => ( T.COMMA ) ;
"nil"           => ( T.NIL ) ;
"val"           => ( T.VAL ) ;
"fun"           => ( T.FUN ) ;
"while"         => ( T.WHILE ) ;
"do"            => ( T.DO ) ;
"ref"           => ( T.REF ) ;
";"             => ( T.SEMI ) ;
"::"            => ( T.DCOLON ) ;
":="            => ( T.ASSIGN ) ;
"!"             => ( T.BANG ) ;
"@"             => ( T.AT ) ;
{dquote_str}  => ( T.STRING (trimFirstLast (valOf (String.fromString yytext))) ) ;
{char}          => ( T.CHAR ((valOf o Char.fromString) (trimFirstLast (trimFirst yytext))) ) ;
{sel}           => ( T.SEL (intFromString (trimFirst yytext)) ) ;
{id}            => ( T.ID yytext ) ;
{ws}            => ( continue() ) ;
{blockcomment}  => ( skip() ) ;
.               => ( raise (lex_error (concat ["Illegal character: ", yytext]))) ;

