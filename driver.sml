(*  COMP 323 sample code:  lexing and parsing
*   
*   Upon building this driver, there are several ways of executing it from
*   the shell.  
*
*   - To lex a program that is in file f and print the resulting tokens to the
*     screen:
*
*       $ ./driver lex f
*
*   - To parse a program that is in file f and print the resulting
*     Ast.pgm value to the screen:
*
*       $ ./driver parse f
*
*   - To type-check a program that is in file f:
*
*       $ ./driver type f
*
*   - To execute a program that is in file f:
*
*       $ ./driver exec f
*
*   - Options:
*
*       --expr:  the contents of f are an expression, not a program; the 
*                exec command evaluates the expression and prints the result
*                to the terminal.
*       --arg:   the argument is the program itself or the expression itself,
*                rather than the name of a file with the program/expression.
*
*   N. Danner
*)

structure Main =
struct

  structure Toks = MLMinusTokens

  structure Lex : LEXER =
  struct
    type token = Toks.token

    type strm = MLMinusLexer.strm

    fun lex strm = 
      case MLMinusLexer.lex (AntlrStreamPos.mkSourcemap()) strm of
           (t, _, s) => (t, s)
  end
  structure Parse = ParseFn(Lex)

  structure T = TextIO

  val lex = Lex.lex

  (*  printnl s = ().
  *
  *   As a side-effect, s will be printed to the terminal followed by a newline.
  *)
  fun printnl(s : string) : unit =
    print (s ^ "\n")

  (* doLex strm = ()
  *
  * Side-effect:  prints tokens from strm to terminal until EOF reached.
  *)
  fun doLex (strm : Lex.strm) : unit =
  let
    fun printTokens (strm : Lex.strm) : unit =
      case lex strm of
           (Toks.EOF, _) => printnl (Toks.toString Toks.EOF)
         | (t, strm) => print ((Toks.toString t) ^ " ") 
                           before printTokens strm
  in
    printTokens strm
  end

  (*  tokStreamToString n <t_0,...> 
  *     = String.concatWith " " [t_0,...,t_{n-1}], t_i <> EOF for i < n,
  *       String.concatWith " " [t_0,...,t_{j-1}], t_j = EOF for j < n.
  *)
  fun tokStreamToString (n : int) (strm : Lex.strm) : string =
    if n = 0 then "..."
    else 
      case lex strm of
           (Toks.EOF, _) => "EOF"
         | (t, strm) => (Toks.toString t) ^ " " ^ (tokStreamToString n strm)

  (*  doParse parser toString strm = ().  
  *
  *  Side-effect:  parses strm using the function parser, and prints result
  *  using toString.
  *)
  fun doParse 
      (parser : Lex.strm -> 'a) 
      (toString : 'a -> string) 
      (strm : Lex.strm) : unit =
    printnl (toString (parser strm))
    handle
        Parse.ExtraTokens s =>
          raise (Fail (String.concatWith " " [
            "Got extra tokens ",
            tokStreamToString 10 s
          ]))

  (*  doTypePgm strm = ().
  *
  *  Side-effect:  type-checks the program defined by stream.  Assuming a
  *  successful type-check, the type of each top-level declaration in the
  *  program will be printed to the terminal.
  *)
  fun doTypePgm (strm : Lex.strm) : unit =
  let
    (*  typeToString t = a string representation of t.
    *)
    fun typeToString (t : Type.typ) : string =
      case t of
           Type.Var tv => Type.tyvarToString tv
         | Type.IntTy => "int"
         | Type.RealTy => "real"
         | Type.StringTy => "string"
         | Type.CharTy => "char"
         | Type.BoolTy => "bool"
         | Type.UnitTy => "unit"
         | Type.ProdTy ts =>
             ListFormat.fmt {
               init="(", final=")", sep=" * ", fmt=typeToString
             } ts
         | Type.ListTy t => "(" ^ typeToString t ^ " list)"
         | Type.ArrowTy(t0, t1) => 
             String.concat [
               "(",
               typeToString t0,
               (* ")", *)
               " -> ",
               (* "(", *)
               typeToString t1,
               ")"
             ]
         | Type.RefTy t =>
             String.concat [
               "(",
               typeToString t,
               " ref)"
             ]
         | Type.Scheme(vs, t) => 
             String.concat [
               "∀",
               ListFormat.listToString Type.tyvarToString vs,
               "(",
               typeToString t,
               ")"
             ]

    val results = Type.typePgm (Parse.parsePgm strm)
  in
    printnl (
      ListFormat.fmt {
        init="",
        final="",
        sep="\n",
        fmt=fn (id, t) => String.concatWith " : " [id, typeToString t]
      } results
    )
  end
  handle 
      Type.EqTypeError => printnl "Equality type error."
    | Type.TypeError => printnl "Type error."
    | Type.UnboundIdError x => printnl ("Unbound identifier:  " ^ x ^ ".")

  (*  doTypeExp strm = ().
  *
  *  Side-effect:  type-checks the expression defined by stream.  Assuming a
  *  successful type-check, the type of the expression will be printed to the
  *  terminal.
  *)
  fun doTypeExp (strm : Lex.strm) : unit =
  let
    val e : Ast.exp = Parse.parseExp strm

    val t : Type.typ = Type.infer e
  in
    printnl (Type.typeToString t)
  end
  handle
      Type.EqTypeError => printnl "Equality type error."
    | Type.TypeError => printnl "Type error."
    | Type.UnboundIdError x => printnl ("Unbound identifier:  " ^ x ^ ".")


  (*  doExec strm = ().
  *
  *  Side-effect:  executes the program defined by strm.
  *)
  fun doExec (strm : Lex.strm) : unit =
  let
    val p : Ast.pgm = Parse.parsePgm strm
    val _ = Type.typecheck p
  in
    CEKInterp.execPgm p
  end

  (*  doEval strm = ().
  *
  *  Side-effect:  evaluates the expression defined by strm.
  *)
  fun doEval (strm : Lex.strm) : unit =
  let
    val e : Ast.exp = Parse.parseExp strm
    val _ = Type.infer e
  in
    printnl (CEKInterp.valueToString (CEKInterp.evalExp e))
  end

  (*  doCompile (file, strm) = ().
  *
  *  Side-effect:  compile program in strm, write result to file.j.
  *)
  fun doCompile (filename : string, strm : Lex.strm) : unit =
  let
    val dir = OS.Path.dir filename
    val fileBase = OS.Path.base filename
    val jFile = OS.Path.joinBaseExt {base=fileBase, ext=SOME "j"}
    val outs = T.openOut jFile
  in
    (
      Compile.compile(
        (Type.typecheck o Parse.parsePgm) strm,
        outs
      ) ;
      T.closeOut outs ;
      printnl "Compilation successful"
    )
  end

  structure M = SplayMapFn(
    struct type ord_key = string val compare = String.compare end : ORD_KEY)

  exception Usage
  val usage = String.concatWith "\n" [
    "driver cmd [--expr] [--arg] s",
    "",
    "Process the file s according to cmd.  Possible values of cmd are:",
    "\tlex:      perform lexical analysis and print the token sequence.",
    "\tparse:    parse and print the abstract syntax tree.",
    "\ttype:     typecheck s",
    "\texec:     execute (evaluate with --expr).",
    "\tcompile:  compile s to s'.j, where s' is the basename of s.",
    "",
    "Options:",
    "\t--expr:  s specifies an expression, not a program (not with compile)",
    "\t--arg:   process s itself; i.e., s does not name a file to read (not with compile)",
    "\n"
  ]

  fun main(arg0 : string, argv : string list) : int =
  let

    val pgmHandlers = [
      ("lex", doLex o #2),
      ("parse", (doParse Parse.parsePgm Ast.pgmToString) o #2),
      ("type", doTypePgm o #2),
      ("exec", doExec o #2),
      ("compile", doCompile)
    ]

    val expHandlers = [
      ("lex", doLex o #2),
      ("parse", (doParse Parse.parseExp Ast.expToString) o #2),
      ("type", doTypeExp o #2),
      ("exec", doEval o #2)
    ]

    val makeHandlerMap =
      foldr (fn ((cmd, hndlr), m) => M.insert(m, cmd, hndlr)) M.empty

    val pgmHandlerMap = makeHandlerMap pgmHandlers
    val expHandlerMap = makeHandlerMap expHandlers

    val streamFromFile = (MLMinusLexer.streamifyInstream o TextIO.openIn)
    val streamFromString = (MLMinusLexer.streamifyInstream o TextIO.openString)

    val stream = ref (streamFromFile)
    val handlerMap = ref(pgmHandlerMap)

    (*  handleOpt : handle a single option by setting stream or parser
    *   appropriately.
    *
    *   Pre-condition:  oa = "--" ^ oa'.
    *)
    fun handleOpt (oa : string) : unit =
    let
    in
      case String.substring(oa, 2, String.size oa - 2) of
           "arg" => stream := streamFromString
         | "expr" => handlerMap := expHandlerMap
         | _ => raise Usage
    end

    (*  handleOpts : handle all options by calling handleOpt o for each option o
    *   on the command line.
    *)
    fun handleOpts (optsargs : string list) : string list =
    let
    in
      case optsargs of
           [] => []
         | oa :: oas =>
             if String.isPrefix "--" oa then (handleOpt oa ; handleOpts oas)
             else oa :: oas
    end

    val cmd :: optsArgs = argv

    val [arg] = handleOpts optsArgs

    val hndlr = valOf(M.find(!handlerMap, cmd))

  in
    BackTrace.monitor (fn () => ((hndlr (arg, !stream arg)) ; 0))
  end
  handle 
    (* Usage errors *)
      Usage => (print usage ; 1)
    | Bind => (print usage ; 1)
    | Option => (print usage ; 1)
    (* I/O errors *)
    | e as IO.Io {name=name, function=_, cause=cause} => 
        (printnl (String.concatWith " " [
          "I/O error reading",
          name,
          "(",
          exnMessage cause,
          ")"
        ]) ; 1)

end
