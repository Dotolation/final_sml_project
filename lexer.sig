(* COMP 323 sample code:  lexing and parsing.
*
* N. Danner
* Spring 2019
*)

signature LEXER =
sig

  type token

  type strm

  val lex : strm -> token*strm

end
