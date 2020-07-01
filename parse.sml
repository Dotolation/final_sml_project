
functor ParseFn (Lex : LEXER where type token = MLMinusTokens.token) =
struct

  structure T = MLMinusTokens

  type stream = Lex.strm

  type 'a parse_result = 'a*stream
  type 'a parser = stream -> 'a parse_result

  (*  In many cases, it is helpful to be able to refer to the kind of token,
  *  regardless of possible arguments (for tokens that take arguments).  tkn
  *  is just a copy of T.token, but with a nullary constructor corresponding
  *  to every value of type T.token.
  *)
  datatype tkn = ID_tkn
               | INT_tkn
               | REAL_tkn
               | CHAR_tkn
               | STRING_tkn
               | TRUE_tkn
               | FALSE_tkn
               | ORELSE_tkn
               | ANDALSO_tkn
               | PLUS_tkn
               | MINUS_tkn
               | TIMES_tkn
               | DIV_tkn
               | SLASH_tkn
               | MOD_tkn
               | EQ_tkn
               | NE_tkn
               | LT_tkn
               | LE_tkn
               | GT_tkn
               | GE_tkn
               | CAT_tkn
               | LP_tkn
               | RP_tkn
               | LBRACK_tkn
               | RBRACK_tkn
               | NIL_tkn
               | DCOLON_tkn
               | AT_tkn
               | FN_tkn
               | DARROW_tkn
               | LET_tkn
               | LETREC_tkn
               | IN_tkn
               | END_tkn
               | IF_tkn
               | THEN_tkn
               | ELSE_tkn
               | SEL_tkn
               | COMMA_tkn
               | VAL_tkn
               | FUN_tkn
               | SEMI_tkn
               | REF_tkn
               | BANG_tkn
               | ASSIGN_tkn
               | WHILE_tkn
               | DO_tkn
               | EOF_tkn
             
  exception NoParse
  exception ExtraTokens of Lex.strm

  val lex = Lex.lex 

  (*  token2tkn t = t', where t' is the tkn value corresponding to t.
  *)
  fun token2tkn (t : T.token) : tkn =
    case t of
         T.ID _ => ID_tkn
       | T.INT _ => INT_tkn
       | T.REAL _ => REAL_tkn
       | T.CHAR _ => CHAR_tkn
       | T.STRING _ => STRING_tkn
       | T.TRUE => TRUE_tkn
       | T.FALSE => FALSE_tkn
       | T.ORELSE => ORELSE_tkn
       | T.ANDALSO => ANDALSO_tkn
       | T.PLUS => PLUS_tkn
       | T.MINUS => MINUS_tkn
       | T.TIMES => TIMES_tkn
       | T.DIV => DIV_tkn
       | T.SLASH => SLASH_tkn
       | T.MOD => MOD_tkn
       | T.EQ => EQ_tkn
       | T.NE => NE_tkn
       | T.LT => LT_tkn
       | T.LE => LE_tkn
       | T.GT => GT_tkn
       | T.GE => GE_tkn
       | T.CAT => CAT_tkn
       | T.LP => LP_tkn
       | T.RP => RP_tkn
       | T.LBRACK => LBRACK_tkn
       | T.RBRACK => RBRACK_tkn
       | T.NIL => NIL_tkn
       | T.DCOLON => DCOLON_tkn
       | T.AT => AT_tkn
       | T.FN => FN_tkn
       | T.DARROW => DARROW_tkn
       | T.LET => LET_tkn
       | T.LETREC => LETREC_tkn
       | T.IN => IN_tkn
       | T.END => END_tkn
       | T.IF => IF_tkn
       | T.THEN => THEN_tkn
       | T.ELSE => ELSE_tkn
       | T.SEL _ => SEL_tkn
       | T.COMMA => COMMA_tkn
       | T.VAL => VAL_tkn
       | T.FUN => FUN_tkn
       | T.SEMI => SEMI_tkn
       | T.REF => REF_tkn
       | T.BANG => BANG_tkn
       | T.ASSIGN => ASSIGN_tkn
       | T.WHILE => WHILE_tkn
       | T.DO => DO_tkn
       | T.EOF => EOF_tkn
     
  (*  ****************************************
  *   Basic parsers, usually for parsing tkn or token values.
  *   ****************************************
  *)

  (*  parseTkn <t_0,...> = (t_0, <t_1,...>)
  *)
  val parseTkn : tkn parser =
    fn strm =>
    let
      val (t, strm) = lex strm
    in
      (token2tkn t, strm)
    end

  (*  parseNtkns n <t_0,...> = ([t_0,...,t_{n-1}], <t_n,...>).
  *)
  fun parseNtkns (n : int) : (tkn list) parser =
    fn strm =>
      if n = 0 then ([], strm)
      else 
        let
          val (t, strm) = parseTkn strm
          val (ts, strm) = parseNtkns (n-1) strm
        in
          (t :: ts, strm)
        end

  (* parseNullToken t <t, t_1, ...> = ((), <t_1,...>)
  *                 t <t', t_1, ...> = raise NoParse  (t' <> t)
  *)
  fun parseNullToken (t : T.token) : unit parser =
    fn strm =>
    let
      val (t', strm) = lex strm
    in
      if token2tkn t' = token2tkn t then ((), strm) else raise NoParse
    end

  val parseIdToken : Ast.ident parser =
    fn strm =>
      case lex strm of
           (T.ID x, strm) => (x, strm)
         | _ => raise NoParse

  (* parseIntToken <INT n, t_1,...> = (n, <t_1,...>)
  *                <t,...>          = raise BadToken(t)
  *)
  val parseIntToken : int parser =
    fn strm =>
    case lex strm of
         (T.INT n, strm) => (n, strm)
       | _ => raise NoParse

  (* parseRealToken <REAL n, t_1,...> = (n, <t_1,...>)
  *                <t,...>          = raise BadToken(t)
  *)
  val parseRealToken : real parser =
    fn strm =>
    case lex strm of
         (T.REAL x, strm) => (x, strm)
       | _ => raise NoParse

  (* parseCharToken <CHAR n, t_1,...> = (n, <t_1,...>)
  *                <t,...>          = raise BadToken(t)
  *)
  val parseCharToken : char parser =
    fn strm =>
    case lex strm of
         (T.CHAR c, strm) => (c, strm)
       | _ => raise NoParse

  (* parseSelToken <SEL n, t_1,...> = (n, <t_1,...>)
  *                <t,...>          = raise NoParse
  *)
  val parseSelToken : int parser =
    fn strm =>
    case lex strm of
         (T.SEL n, strm) => (n, strm)
       | _ => raise NoParse

  (* parseStringToken <STRING s, t_1,...> = (s, <t_1,...>)
  *  parseStringToken <ID s, t_1,...>     = (s, <t_1,...>)
  *                   <t,...>             = raise BadToken(t)
  *)
  val parseStringToken : string parser =
    fn strm =>
    case lex strm of
         (T.ID s, strm) => (s, strm)
       | (T.STRING s, strm) => (s, strm)
       | _ => raise NoParse



  (*  ****************************************
  *   Parser combinators
  *   ****************************************
  *)

  (*  failParser s always raises NoParse.
  *)
  val failParser : 'a parser =
    fn strm => raise NoParse

  (* compParser p1 p2 <t_0,...> = ((r1, r2), <t_N,...>), where
  *   p1 <t_0,...> = (r1, <t_n,...>)
  *   p2 <t_n,...> = (r2, <t_N,...>)
  *
  *  In other words, compParser p1 p2 is the parser that first parses with p1,
  *  the parses the remainder with p2, and returns the pair of results.
  *)
  fun compParsers (p1 : 'a parser, p2 : 'b parser) : ('a*'b) parser =
    fn strm =>
    let
      val (a, s) = p1 strm
      val (b, s') = p2 s
    in
      ((a, b), s')
    end

  (*  Infix version of compParsers.
  *)
  val <&> = compParsers
  infix <&>

  (* compParserDropLeft p1 p2 <t_0,...> = (r2, <t_N,...>), where
  *   p1 <t_0,...> = (r1, <t_n,...>)
  *   p2 <t_n,...> = (r2, <t_N,...>)
  *
  *  In other words, compParserDropLeft p1 p2 performs the same actions as
  *  p1 <&> p2, but discards the yield of the parse by p1.
  *)
  fun compParsersDropLeft (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
    fn strm =>
    let
      val (_, strm) = p1 strm
      val (b, strm) = p2 strm
    in
      (b, strm)
    end

  (*  Infix version of compParsersDropLeft.
  *)
  fun <!&> (p1 : 'a parser, p2 : 'b parser) : 'b parser =
    compParsersDropLeft p1 p2
  infix <!&>

  (* compParserDropRight p1 p2 <t_0,...> = (r1, <t_N,...>), where
  *   p1 <t_0,...> = (r1, <t_n,...>)
  *   p2 <t_n,...> = (r2, <t_N,...>)
  *
  *  In other words, compParserDropLeft p1 p2 performs the same actions as
  *  p1 <&> p2, but discards the yield of the parse by p2.
  *)
  fun compParsersDropRight (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
    fn strm =>
    let
      val (a, strm) = p1 strm
      val (_, strm) = p2 strm
    in
      (a, strm)
    end

  (*  Infix version of compParsersDropRight.
  *)
  fun <&!> (p1 : 'a parser, p2 : 'b parser) : 'a parser =
    compParsersDropRight p1 p2
  infix <&!>

  (* parseSeq p <t_0,...> = ([r_0,...,r_{k-1}], <t_N,...>), where:
  *    p <t_0,...>         = (r_0, <t_{j_0},...>)
  *    p <t_{j_0},...>     = (r_1, <t_{j_1},...>)
  *    ...
  *    p <t_{j_{k-2}},...> = (r_{k-1}, <t_N,...>)
  *
  *  In other words, parseEq p ts parses a maximal-length sequence of p-parses
  *  from ts.  Note that it is possible that k=0, in which case
  *  parseSeq p ts = ([], ts).
  *)
  fun parseSeq (p : 'a parser) : ('a list) parser =
    fn strm =>
    let
      val (first, strm) = p strm
      val (rest, strm) = parseSeq p strm
    in
      (first :: rest, strm)
    end
    handle NoParse => ([], strm)

  (* parseSeq p t <t_0,...> = ([r_0,...,r_{k-1}], <t_N,...>), where:
  *    p <t_0,...>         = (r_0, <t, t_{j_0},...>)
  *    p <t_{j_0},...>     = (r_1, <t, t_{j_1},...>)
  *    ...
  *    p <t_{j_{k-2}},...> = (r_{k-1}, <t, t_N,...>)
  *
  *  In other words, parseEq p ts parses a maximal-length sequence of p-parses
  *  from ts, where the p-parses are separated by t.  Note that it is possible
  *  that k=0, in which case parseSeq p ts = ([], ts).
  *
  *  Pre-condition:  t is a nullary token.
  *)
  fun parseSeparatedSeq (p : 'a parser) (t : T.token) : ('a list parser) =
    fn strm =>
    let
      val (first, strm) = p strm
      val (rest, strm) = parseSeq (parseNullToken t <!&> p) strm
    in
      (first :: rest, strm)
    end
    handle NoParse => ([], strm)

  (*  Infix version of parseSeq.  We would really like a postfix version of
  *  parseSeq, so we can write things like p<*>.  But ML doesn't give us any
  *  way to define postfix operators, only infix operators.  So we can only
  *  use <**> when we have a stream to parse:  p<**> s.  If we want the sequence
  *  parser itself as a value (typically, as an argument to some other parser
  *  combinator), we have to use parseSeq.
  *)
  fun <**> (p : 'a parser, strm : stream) : ('a list) parse_result =
    parseSeq p strm
  infix <**>

  (* parseOpt p <t_0,...> = (SOME x, <t_n,...>), if p <t_0,...> = (x, <t_n,...>)
  *                       = NONE, if p <t_0,...> does not parse.
  *
  * In other words, parseOpt p is an option parser:  it parses zero or one 'a
  * values using p, returning the result as an option so that the caller knows
  * whether zero or one values was successfully parsed.
  *)
  fun parseOpt (p : 'a parser) : ('a option) parser =
    fn strm =>
    let
      val (a, strm) = p strm
    in
      (SOME a, strm)
    end
    handle NoParse => (NONE, strm)

  (*  Infix version of parseOpt.  Like with <**> we would really like a postfix
  *  version, but oh well.
  *)
  fun <?> (p : 'a parser, strm : stream) : ('a option) parse_result =
    parseOpt p strm
  infix <?>

  (*  choiceParser [(ts_0, p_0),...,(ts_{n-1}, p_{n-1})] <t_0,...> =
  *   p_i <t_0,...>, where ts_i = [t_0,...,t_{n-1}].
  *
  *   Pre-conditions:  
  *   - length(ts_i) = n for all n;
  *   - there is i such that ts_i = [t_0,...,t_{n-1}].
  *
  *   In other words, choiceParser takes a list of pairs of the form (ts, p),
  *   where ts is a token sequence and p a parser.  When applied to a token
  *   stream <t_0,...>, the choiceParser tries to match 
  *   <t_0,...,t_{length ts - 1}> with each of the first components of the list;
  *   when it finds a match, it parses <t_0,...> with the corresponding second
  *   component.
  *)
  fun choiceParser 
      (choices : ((tkn list)*('a parser)) list) : 'a parser =
  let
    val n = length(#1(List.sub(choices, 0)))
  in
    fn strm =>
    let
      val (tks, _) : (tkn list)*stream = parseNtkns n strm
      val p : 'a parser = 
        #2(valOf(List.find (fn (tks', _) => tks' = tks) choices))
    in
      p strm
    end
    handle Option => raise NoParse
  end

  (* Infix version of choiceParser.
  *)
  val <|> = choiceParser

  (*  actionParser(p, act) strm = let (res, strm) = p strm in (act res, strm).
  *
  *  In other words, if p ts = x, then actionParser(p, act) ts = act(x).
  *)
  fun actionParser (p : 'a parser, act : 'a -> 'b) : 'b parser =
    fn strm =>
    let
      val (res, strm) = p strm
    in
      (act res, strm)
    end

  (*  Infix version of actionParser.
  *)
  val >> = actionParser
  infix >>

  fun parseSpecificTkn (t : tkn) : tkn parser =
    parseTkn >> (fn t' => if t' = t then t else raise NoParse)

  fun parseTknsChoice (tkns : tkn list) : tkn parser =
    <|> (map (fn tkn => ([tkn], parseTkn)) tkns)

  (*  ****************************************
  *   Association functions.
  *   ****************************************
  *)

  (*  leftAssoc lhs [(r_0, e_0),...,(r_{n-1}, e_{n-1})] =
  *     r_{n-1}(...r_1(r_0(e, e_0), e_1)..., e_{n-1}).
  *
  *   E.g., leftAssoc 1 [(+, 2), (+, 3), (+, 4)] = ((1 + 2) + 3) + 4
  *)
  fun leftAssoc
      (lhs : Ast.exp)
      (rrs : ((Ast.exp*Ast.exp -> Ast.exp) * Ast.exp) list) : Ast.exp =
    case rrs of
         [] => lhs
       | (rator, rhs) :: rrs =>
           leftAssoc (rator(lhs, rhs)) rrs

  (*  rightAssoc lhs [(r_0, e_0),...,(r_{n-1}, e_{n-1})] =
  *     r_0(lhs, e_0(...r_{n-2}(e_{n-3}, r_{n-1}(e_{n-2}, e_{n-1}))...))
  *
  *   E.g., rightAssoc xs [(::, ys), (:: zs)] = xs :: (ys :: zs).
  *)
  fun rightAssoc 
      (lhs : Ast.exp) 
      (rrs : ((Ast.exp*Ast.exp -> Ast.exp) * Ast.exp) list) : Ast.exp =
    case rrs of
         [] => lhs
       | (rator, rhs) :: rrs => rator(lhs, rightAssoc rhs rrs)


  (*  ****************************************
  *   Expression parsing functions.
  *   ****************************************
  *)

  fun parse_start (strm : stream) = parse_fn strm

  (*  Productions for ML's exp category.
  *)
  and parse_fn (strm : stream) : Ast.exp parse_result =
    case (parseNullToken T.FN)<?> strm of
         (NONE, strm) => parse_while strm
       | (SOME _, strm) =>
           ((parseStringToken <&!>
             parseNullToken T.DARROW <&>
             parse_start
             ) >> 
           (fn (x, e) => Ast.Lambda(x, e))) strm

  and parse_while (strm : stream) : Ast.exp parse_result =
    ((parseNullToken T.WHILE <!&> parse_start <&!>
     parseNullToken T.DO <&> parse_start) >> 
    (fn (e', e) => Ast.While(e', e)))
     strm
    handle NoParse => parse_cond strm

  and parse_cond (strm : stream) : Ast.exp parse_result =
    case (parseNullToken T.IF)<?> strm of
         (NONE, strm) => parse_orelse strm
       | (SOME _, strm) =>
           ((parse_start <&!>
             parseNullToken T.THEN <&>
             (
             parse_start <&!>
             parseNullToken T.ELSE <&>
             parse_start 
             )) >> 
           (fn (e, (e0, e1)) => Ast.Cond(e, e0, e1))) strm

  and parse_orelse (strm : stream) : Ast.exp parse_result =
  let
    val (lhs, strm) = parse_andalso strm
    val (rrs, strm) = 
      ((parseSpecificTkn ORELSE_tkn) <!&> parse_andalso)<**> strm
  in
    (leftAssoc lhs (map (fn rhs => (Ast.Orelse, rhs)) rrs), strm)
  end

  and parse_andalso (strm : stream) : Ast.exp parse_result =
  let
    val (lhs, strm) = parse_assign strm
    val (rrs, strm) = 
      ((parseSpecificTkn ANDALSO_tkn) <!&> parse_assign)<**> strm
  in
    (leftAssoc lhs (map (fn rhs => (Ast.Andalso, rhs)) rrs), strm)
  end


  (*  ML's infexp (infix expression) category.
  *)

  and parse_assign (strm : stream) : Ast.exp parse_result =
  let
    val (lhs, strm) = parse_comp strm
    val (es, strm) = (parseNullToken T.ASSIGN <!&> parse_comp)<**> strm
  in
    (leftAssoc lhs (map (fn e => (Ast.Assign, e)) es), strm)
  end

  and parse_comp (strm : stream) : Ast.exp parse_result =
  let
    val (lhs, strm) = parse_consapp strm

    fun tknToRator (t : tkn) : (Ast.exp*Ast.exp -> Ast.exp) =
      case t of
           EQ_tkn => Ast.Eq
         | NE_tkn => Ast.Ne
         | LT_tkn => Ast.Lt
         | LE_tkn => Ast.Le
         | GT_tkn => Ast.Gt
         | GE_tkn => Ast.Ge
  in
    case ((parseTknsChoice 
            [EQ_tkn, NE_tkn, LT_tkn, LE_tkn, GT_tkn, GE_tkn]) <&> 
            parse_consapp)<?> strm of
         (SOME (t, rhs), strm) => (tknToRator t (lhs, rhs), strm)
       | (NONE, _) => (lhs, strm)
  end

  and parse_consapp (strm : stream) : Ast.exp parse_result =
    let
      val choices = [
        ([DCOLON_tkn], 
           (parseTkn <!&> parse_plus) >> (fn e => (Ast.Cons, e))),
        ([AT_tkn], 
           (parseTkn <!&> parse_plus) >> (fn e => (Ast.Append, e)))
      ]
      val (lhs, strm) = parse_plus strm
      val (rrs, strm) = (<|> choices)<**> strm
    in
      (rightAssoc lhs rrs, strm)
    end

  and parse_plus (strm : stream) : Ast.exp parse_result =
    let
      val choices = [
        ([PLUS_tkn], parseTkn <&> parse_mul),
        ([MINUS_tkn], parseTkn <&> parse_mul),
        ([CAT_tkn], parseTkn <&> parse_mul)
      ]
      val (lhs, strm) = parse_mul strm
      val (rrs, strm) = (<|> choices)<**> strm
    in
      (
        leftAssoc 
          lhs 
          (map 
            (fn (tkn, e) => 
              case tkn of 
                   PLUS_tkn => (Ast.Plus, e)
                 | MINUS_tkn => (Ast.Minus, e)
                 | CAT_tkn => (Ast.Cat, e)
            ) 
            rrs
          ), 
        strm
      )
    end

  and parse_mul (strm : stream) : Ast.exp parse_result =
    let
      val choices = [
        ([TIMES_tkn], 
           (parseTkn <!&> parse_app) >> (fn e => (Ast.Times, e))),
        ([DIV_tkn], 
           (parseTkn <!&> parse_app) >> (fn e => (Ast.Div, e))),
        ([SLASH_tkn], 
           (parseTkn <!&> parse_app) >> (fn e => (Ast.Slash, e))),
        ([MOD_tkn], 
           (parseTkn <!&> parse_app) >> (fn e => (Ast.Mod, e)))
      ]
      val (lhs, strm) = parse_app strm
      val (rrs, strm) = (<|> choices)<**> strm
    in
      (leftAssoc lhs rrs, strm)
    end

  and parse_app (strm : stream) : Ast.exp parse_result =
    let
      val (rator, strm) = parse_brack strm
      val (rands, strm) = 
        ((parseSeq parse_brack) >> (map (fn e => (Ast.App, e)))) strm
    in
      (leftAssoc rator rands, strm)
    end

  (*  ML's atexp (atomic expression) category.
  *)
  and parse_brack (strm : stream) : Ast.exp parse_result =
    case (parseNullToken T.LBRACK <!&> 
          parseSeparatedSeq parse_start T.COMMA <&!> parseNullToken T.RBRACK)<?>
          strm
      of
         (NONE, strm) => parse_parenSeq strm
       | (SOME es, strm) => (Ast.List es, strm)

  and parse_parenSeq (strm : stream) : Ast.exp parse_result =
    case (parseNullToken T.LP <!&> 
          parseSeparatedSeq parse_start T.SEMI <&!> parseNullToken T.RP)<?> 
          strm
      of
         (NONE, strm) => parse_parenTuple strm
       | (SOME [], strm) => (Ast.Triv, strm)
       | (SOME [e], strm) => (e, strm)
       | (SOME es, strm) => (Ast.Seq es, strm)

  and parse_parenTuple (strm : stream) : Ast.exp parse_result =
    case (parseNullToken T.LP <!&> 
          parseSeparatedSeq parse_start T.COMMA <&!> parseNullToken T.RP)<?> 
          strm
      of
         (NONE, strm) => parse_let strm
       | (SOME [], strm) => (Ast.Triv, strm)
       | (SOME [e], strm) => (e, strm)
       | (SOME es, strm) => (Ast.Tuple es, strm)

  and parse_let (strm : stream) : Ast.exp parse_result =
    case (parseNullToken T.LET)<?> strm of
         (NONE, strm) => parse_lit_id_sel strm
       | (SOME _, strm) =>
           ((parseSeq (parse_decl <&!> parseOpt (parseNullToken T.SEMI)) <&!> 
            parseNullToken T.IN <&> 
            parse_start <&!>
            parseNullToken T.END) >>
           (fn (ds, e) => Ast.Let(ds, e))) strm

  and parse_lit_id_sel (strm : stream) : Ast.exp parse_result =
  let
    val choices : ((tkn list)*(Ast.exp parser)) list = [
      ([ID_tkn], parseStringToken >> (fn s => Ast.Ident s)),
      ([INT_tkn], parseIntToken >> (fn n => Ast.IntNum n)),
      ([REAL_tkn], parseRealToken >> (fn x => Ast.RealNum x)),
      ([CHAR_tkn], parseCharToken >> (fn c => Ast.Char c)),
      ([STRING_tkn], parseStringToken >> (fn s => Ast.Str s)),
      ([TRUE_tkn], parseTkn >> (fn _ => Ast.Bool true)),
      ([FALSE_tkn], parseTkn >> (fn _ => Ast.Bool false)),
      ([SEL_tkn], parseSelToken >> (fn n => Ast.Proj n)),
      ([NIL_tkn], parseTkn >> (fn _ => Ast.List [])),
      ([REF_tkn], parseTkn >> (fn _ => Ast.Ident "ref")),
      ([BANG_tkn], parseTkn >> (fn _ => Ast.Ident "!"))
    ]
  in
    <|> choices strm
  end

  (*  ****************************************
  *   Program parsing functions.
  *
  *   These must still be part of the mutual recursion used to define the
  *   expression parsers, becaues both programs and let expressions depend on
  *   declarations.
  *   ****************************************
  *)

  (*  Declaration parser.
  *)
  and parse_decl (strm : stream) : Ast.dec parse_result =
  let
    val choices : ((tkn list)*(Ast.dec parser)) list = [
      ([VAL_tkn], parse_valdec),
      ([FUN_tkn], parse_fundec),
      ([DO_tkn], parse_dodec)
    ]
  in
    <|> choices strm
  end

  (*  Value declaration parser.
  *)
  and parse_valdec (strm : stream) : Ast.dec parse_result =
    (((parseNullToken T.VAL) <!&>
    parseStringToken <&!>
    parseNullToken T.EQ <&>
    parse_start) >> (fn (x, e) => Ast.ValDec(x, e))) strm

  (*  Function definition parser.
  *)
  and parse_fundec (strm : stream) : Ast.dec parse_result =
    (((parseNullToken T.FUN) <!&>
    parseStringToken <&>
    parseSeq parseStringToken <&!>
    parseNullToken T.EQ <&>
    parse_start) >> (fn ((f, xs), e) => Ast.FunDec(f, xs, e))) strm

  and parse_dodec (strm : stream) : Ast.dec parse_result =
    ((parseNullToken T.DO <!&> parse_start) >> Ast.DoDec) strm

  (*  Expression statement parser.
  *)
  fun parse_exp (stm : stream) : Ast.exp parse_result =
    parse_start stm

  (*  Statement parser.
  *)
  fun parse_stm (strm : stream) : Ast.stm parse_result =
  let
    val choices : ((tkn list)*(Ast.stm parser)) list = [
      ([VAL_tkn], (parse_valdec <&!> parseNullToken T.SEMI) >>
                    (fn d => Ast.Dec d)),
      ([FUN_tkn], (parse_fundec <&!> parseNullToken T.SEMI) >>
                    (fn d => Ast.Dec d))
    ]
  in
    <|> choices strm
    handle NoParse =>
      ((parse_exp <&!> parseNullToken T.SEMI) >> (fn e => Ast.ExprStm e)) strm
  end

  (*  Program parser.
  *)
  fun parse_pgm (strm : stream) : Ast.pgm parse_result =
    ((parseSeq parse_stm) >> (fn ss => Ast.Program ss)) strm

  (* ****************************************
  *  Client-visible parsing functions.
  *  ****************************************
  *)

  fun parseExp (strm : stream) : Ast.exp =
  let
    val (e, s) = parse_exp strm
  in
    case lex s of
         (T.EOF, _) => e
       | _ => raise ExtraTokens s
  end

  fun parsePgm (strm : stream) : Ast.pgm =
  let
    val (p, s) = parse_pgm strm
  in
    case lex s of
         (T.EOF, _) => p
       | _ => raise ExtraTokens s
  end

end
