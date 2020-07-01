(*  COMP 323 Project 5:  compilation
*
*  N. Danner
*  Spring 2019
*)

structure Type =
struct

  (* ********************
  *  DEBUGGING
  *  ********************
  *)

  (*  Set debug = true to enable debugging output.
  *)
  val debug = false

  (*  dbg_printnl s = print (s ^ "\n"), if debugging is enabled
  *                 = (),               otherwise.
  *)
  fun dbg_printnl s = if debug then print (s ^ "\n") else ()

  (* ********************
  *  UTILITIES
  *  ********************
  *)

  (*  uniquify eq [x_0,...,x_{n-1}] = [y_0,...,y_{m-1}], where
  *   - For all i there is j such that x_i = y_j
  *   - For all j there is i such that x_i = y_j
  *   - For all i <> j, y_i <> y_j.
  *   Here, x = y means eq(x,y) and x <> y means not (eq (x, y)).
  *
  *   In other words, uniquify eq xs is a list of the set of elements of xs.
  *)
  fun uniquify (eq : 'a*'a -> bool) (xs : 'a list) : 'a list =
    case xs of
         [] => []
       | x :: xs =>
           x :: List.filter (fn y => not(eq(y, x))) (uniquify eq xs)

  (* ********************
  *  ENVIRONMENTS
  *  ********************
  *)

  (*  A structure for environments with identifier keys.
  *)
  structure Env = SplayMapFn(
    struct
      type ord_key = Ast.ident
      val compare = String.compare
    end)

  (*  Convenience abbreviation for environments.  In documentation, we treat an
  *  'a env as a function of type ident -> 'a and use standard notation for
  *  environments.
  *)
  type 'a env = 'a Env. map

  (*  Raised when looking up a key that is not in the domain of an environment.
  *)
  exception NotFound

  (*  get ρ x = ρ(x).
  *)
  fun get (rho : 'a env) (x : Ast.ident) : 'a =
    valOf(Env.find(rho, x))
    handle Option => raise NotFound

  (*  update ρ x y = ρ{x |-> y}.
  *)
  fun update (rho : 'a env) (x : Ast.ident) (y : 'a) : 'a env =
    Env.insert(rho, x, y)

  (*  update' ρ (x, y) = ρ{x |-> y}.
  *)
  fun update' (rho : 'a env) ((x, y) : Ast.ident*'a) : 'a env =
    update rho x y

  (*  updateMany ρ {(x_0, y_0),...,(x_{n-1},y_{n-1})} =
  *     ρ{x_0 |-> y_0,...,x_{n-1} |-> y_{n-1}}.
  *)
  fun updateMany (rho : 'a env) (kvs : (Ast.ident*'a) list) : 'a env =
    foldl Env.insert' rho kvs

  (* ********************
  *  TYPES
  *  ********************
  *)

  (*  Flags for type variables.
  *   - EQTYPE:  represents an equality type.
  *)
  datatype flag = EQTYPE | PLUSTYPE

  (*  Exception raised when a type is required to be an equality type, but
  *  cannot be.
  *)
  exception EqTypeError

  exception OverloadError

  (*  hasFlag f [f_0,...,f_{n-1}] = true,  f = f_i for some i
  *                                 false, otherwise.
  *)
  fun hasFlag (f : flag) (fs : flag list) : bool =
    List.exists (fn f' => f' = f) fs

  (*  mergeFlags (f0, f1) = uniquify (f0 @ f1).
  *)
  fun mergeFlags (f0 : flag list, f1 : flag list) : flag list =
    uniquify op= (f0 @ f1)

  (*  A tyvar value {sub, lvl, flags} names the type variable alpha_sub, which
  *  occurs at level !lvl, and which has flags !flags.
  *)
  type tyvar = {
    sub : int,
    lvl : int ref,
    flags : flag list ref
  }

  (*  Object language types and type schemes.
  *)
  datatype typ = Var of tyvar
               | IntTy | RealTy | StringTy | CharTy | BoolTy | UnitTy
               | ProdTy of typ list
               | ListTy of typ
               | ArrowTy of typ*typ
               | RefTy of typ
               | Scheme of tyvar list*typ

  (*  freevars t = free variables of t without duplicates.
  *)
  fun freevars (t : typ) : tyvar list =
  let
    (*  freevars' t = free variables of t, possibly with duplicates.
    *)
    fun freevars' (t : typ) : tyvar list =
      case t of
           Var v => [v]
         | (IntTy | RealTy | StringTy | CharTy | BoolTy | UnitTy) => []
         | ProdTy ts => List.concat (map freevars' ts)
         | ListTy t => freevars' t
         | ArrowTy(t0, t1) => freevars' t0 @ freevars' t1
         | RefTy t => freevars' t
         | Scheme _ => raise LibBase.Impossible "freevars of Scheme"
  in
    uniquify (fn ({sub=sub0,...}, {sub=sub1,...}) => sub0=sub1) (freevars' t)
  end

  (*  tyvarToString tv = a string representation of tv.
  *)
  fun tyvarToString ({sub, lvl, flags} : tyvar) : string =
  let
    val tvname =
      if hasFlag EQTYPE (!flags) then "''a"
      else if hasFlag PLUSTYPE (!flags) then "[+ ty]"
      else "'a"
  in
    String.concat [tvname, Int.toString sub]
  end

  (*  typeToString t = a string representation of t.
  *)
  fun typeToString (t : typ) : string =
    case t of
         Var tv => tyvarToString tv
       | IntTy => "int"
       | RealTy => "real"
       | StringTy => "string"
       | CharTy => "char"
       | BoolTy => "bool"
       | UnitTy => "unit"
       | ProdTy [] => raise LibBase.Impossible "Type.typeToString ProdTy []"
       | ProdTy [t] => raise LibBase.Impossible "Type.typeToString ProdTy [t]"
       | ProdTy ts =>
           ListFormat.fmt {
             init="", final="", sep=" * ", fmt=typeToString
           } ts
       | ListTy t => typeToString t ^ " list"
       | ArrowTy(t0, t1) => typeToString t0 ^ " -> " ^ typeToString t1
       | RefTy t0 => "(" ^ typeToString t0 ^ " ref)"
       | Scheme(vs, t) =>
           String.concat [
             "∀",
             ListFormat.listToString tyvarToString vs,
             "(",
             typeToString t,
             ")"
           ]

  (*  makeEqType t = ()
  *
  *  Side-effect:  all type variables in t have the EQTYPE flag set.
  *
  *  Pre-condition:  t is not a type scheme.
  *
  *  Raises:  EqTypeError if t cannot be an equality type.
  *)
  fun makeEqType (t : typ) : unit =
    case t of
         Var {sub, lvl, flags} =>
           flags := (if hasFlag EQTYPE (!flags) then (!flags)
                    else EQTYPE :: (!flags))
       | (IntTy | StringTy | CharTy | BoolTy | RealTy) => ()
       | ProdTy ts => List.app makeEqType ts
       | ListTy t => makeEqType t
       | RefTy t => ()
       | Scheme _ => raise LibBase.Impossible "Type.makeEqType Scheme"
       | _ => raise EqTypeError

  fun makePlusType (t : typ) : unit =
    case t of
         Var {sub, lvl, flags} =>
           flags := (if hasFlag PLUSTYPE (!flags) then (!flags)
                    else PLUSTYPE :: (!flags))
       | (IntTy | RealTy) => ()
       | Scheme _ => raise LibBase.Impossible "Type.makeEqType Scheme"
       | _ => raise OverloadError


  fun enforceFlags (fs : flag list) (t : typ) : unit =
    case fs of
         [] => ()
       | EQTYPE :: fs => ( makeEqType t ; enforceFlags fs t)
       | PLUSTYPE :: fs => ( makePlusType t ; enforceFlags fs t)


  (* ********************
  *  ANNOTATED ASTs
  *  ********************
  *)

  (*  Convenience abbreviation.
  *)
  type ident = Ast.ident

  (*  An annotated expression consists of an expression and a type.  The
  *  expression constructors are the same as the AST constructors, but the
  *  arguments must be annotated expressions.  We also define annotated
  *  declarations, etc. in the obvious way.
  *)
  datatype ann_exp = AnnExp of exp*typ
  and      exp = Ident of ident
               | IntNum of int
               | RealNum of real
               | Char of char
               | Str of string
               | Bool of bool
               | Plus of ann_exp*ann_exp
               | Minus of ann_exp*ann_exp
               | Times of ann_exp*ann_exp
               | Div of ann_exp*ann_exp
               | Mod of ann_exp*ann_exp
               | Lt of ann_exp*ann_exp
               | Gt of ann_exp*ann_exp
               | Le of ann_exp*ann_exp
               | Ge of ann_exp*ann_exp
               | Eq of ann_exp*ann_exp
               | Ne of ann_exp*ann_exp
               | Orelse of ann_exp*ann_exp
               | Andalso of ann_exp*ann_exp
               | Cat of ann_exp*ann_exp
               | Cond of ann_exp*ann_exp*ann_exp
               | Tuple of (ann_exp list)
               | Triv
               | List of (ann_exp list)
               | Cons of ann_exp*ann_exp
               | Append of ann_exp*ann_exp
               | App of ann_exp*ann_exp
               | Lambda of (ident*typ)*ann_exp
               | Let of (dec list)*ann_exp
               | Assign of ann_exp*ann_exp
               | Seq of ann_exp list
               | While of ann_exp*ann_exp

  and      dec = ValDec of ident*typ*ann_exp
               | FunDec of ident*typ*((ident*typ) list)*ann_exp
               | DoDec of ann_exp

  datatype stm = Dec of dec
               | ExprStm of ann_exp

  datatype pgm = Program of stm list

  (* expToString : t -> string
  *  expToString e is the string representation of ASTs.
  *)
  local
    fun wrap s = concat ["(", s, ")"]
  in
    fun binop s e1 e2 = concat [annExpToString e1, s, annExpToString e2]
    and annExpToString(AnnExp(e, tau)) =
      String.concat [
        "[",
        expToString e,
        " : ",
        typeToString tau,
        "]"
      ]
    and expToString(Ident(x)) = x
      | expToString(IntNum n) = Int.toString n
      | expToString(RealNum n) = Real.toString n
      | expToString(Char c) = Char.toString c
      | expToString(Str s) = concat ["\"", s, "\""]
      | expToString(Bool b) = Bool.toString b
      | expToString(Plus(e1, e2)) =
          concat ["(", annExpToString e1, " + ", annExpToString e2, ")"]
      | expToString(Minus(e1, e2)) =
          concat ["(", annExpToString e1, " - ", annExpToString e2, ")"]
      | expToString(Times(e1, e2)) =
          concat ["(", annExpToString e1, "*", annExpToString e2, ")"]
      | expToString(Div(e1, e2)) =
          concat ["(", annExpToString e1, " div ", annExpToString e2, ")"]
      | expToString(Mod(e1, e2)) =
          concat ["(", annExpToString e1, " mod ", annExpToString e2, ")"]
      | expToString(Eq(e1, e2)) = wrap (binop "=" e1 e2)
      | expToString(Ne(e1, e2)) = wrap (binop "<>" e1 e2)
      | expToString(Lt(e1, e2)) = wrap (binop "<" e1 e2)
      | expToString(Le(e1, e2)) = wrap (binop "<=" e1 e2)
      | expToString(Gt(e1, e2)) = wrap (binop ">" e1 e2)
      | expToString(Ge(e1, e2)) = wrap (binop ">=" e1 e2)
      | expToString(Orelse(e1, e2)) =
          concat ["(", annExpToString e1, " orelse ", annExpToString e2, ")"]
      | expToString(Andalso(e1, e2)) =
          concat ["(", annExpToString e1, " andalso ", annExpToString e2, ")"]
      | expToString(Cat(e1, e2)) =
          concat ["(", annExpToString e1, "^", annExpToString e2, ")"]
      | expToString(Cond(e1, e2, e3)) =
          String.concatWith " "
          ["if", annExpToString e1, "then", annExpToString e2,
                                 "else", annExpToString e3, "fi"]
      | expToString(Triv) = "(_)"
      | expToString(Tuple es) =
          ListFormat.fmt {init="(", final=")", sep=", ", fmt=annExpToString} es
      | expToString(List es) =
          ListFormat.listToString annExpToString es
      | expToString(Cons(e1, e2)) = wrap (binop "::" e1 e2)
      | expToString(Append(e1, e2)) = wrap (binop "@" e1 e2)
      | expToString(App(rator, rand)) =
          concat ["(", annExpToString rator, "@", annExpToString rand, ")"]
      | expToString(Lambda((x, _), e)) =
          concat ["( fn ", x, " => ", annExpToString e, ")"]
      | expToString(Let(decs, e2)) =
          concat ["( let ", ListFormat.listToString declToString decs,
                  " in ", annExpToString e2,
                  " end)"]
      | expToString(Assign(e1, e2)) =
          concat ["(", annExpToString e1, " := ", annExpToString e2, ")"]
      | expToString(While(e', e)) =
          concat ["while ", annExpToString e', " do ", annExpToString e, " endw"]
      | expToString(Seq es) =
          ListFormat.fmt {
            init="(", sep="; ", final=")", fmt=annExpToString
          } es

    (*  declToString d = s, where s is a string representation of the
    *   declaration d.
    *)
    and declToString (ValDec(x, tau, e)) =
          String.concatWith " " [
            "val", x, ":", typeToString tau, "=", annExpToString e
          ]
      | declToString (FunDec(f, tau, ps, e)) =
          String.concatWith " " [
            "fun",
            String.concatWith " " (map #1 ps),
            "=",
            annExpToString e
          ]
      | declToString (DoDec e) =
          String.concatWith " " ["do", annExpToString e]
  end

  (* ********************
  *  EQUATIONS
  *  ********************
  *)

  (*  Makes writing equations quite pleasant; instead of something like
  *  Eqn(t0, t1), we can write t0 == t1.
  *
  *  Invariant:  for any equation t0 == t1, neither t0 nor t1 are type schemes.
  *)
  infix 6 ==
  datatype equation = == of typ*typ

  (*  eqnToString e = a string representation of e.
  *)
  fun eqnToString ((t0 == t1) : equation) : string =
    typeToString t0 ^ " = " ^ typeToString t1

  (*  eqnLevelBound e lvl = true,  all type variables in e have level <= lvl
  *                       = false, otherwise.
  *)
  fun eqnLevelBound ((t0 == t1) : equation) (lvl : int) : bool =
  let
    fun typeLevelBound (t : typ) : bool =
      case t of
           Var {lvl=l,...} => !l <= lvl
         | (IntTy | RealTy | StringTy | CharTy | BoolTy | UnitTy) => true
         | ProdTy ts => List.all typeLevelBound ts
         | ListTy t => typeLevelBound t
         | ArrowTy(t0, t1) => typeLevelBound t0 andalso typeLevelBound t1
         | RefTy t => typeLevelBound t
         | Scheme _ => raise LibBase.Impossible "Type.eqnLevelBound Scheme"
  in
    typeLevelBound t0 andalso typeLevelBound t1
  end


  (* ********************
  *  TYPE SUBSTITUTIONS
  *  ********************
  *)

  (*  The type substitution [(α_0, τ_0),...,(α_{n-1}, τ_{n-1})] represents the
  *  *sequential* substitution of τ_{n-1} for α_{n-1},...,τ_0 for α_0.  In
  *  particular, if α_i occurs in τ_j for i < j, then α_i will be replaced by
  *  τ_i in τ_j.
  *)
  type typesubst = (tyvar*typ) list

  (*  typesubstToString ts = a string representation of sigma.
  *)
  fun typesubstToString (tysub : typesubst) : string =
    ListFormat.fmt {
      init="",
      final="",
      sep="",
      fmt=fn (tv, t) => "[" ^ typeToString t ^ "/" ^ tyvarToString tv ^ "]"
    } tysub

  (*  subst (α, τ) σ = σ{τ/α}
  *
  *  The sort of odd parameter type is so that we can use subst as the step
  *  function in foldr.
  *)
  fun subst (tysub as ({sub,...} : tyvar, t : typ), sigma : typ) : typ =
  let
    val () = dbg_printnl ("apply tysub to " ^ typeToString sigma)
  in
    case sigma of
         v as Var {sub=sub', ...} => if sub' = sub then t else v
       | IntTy => IntTy
       | RealTy => RealTy
       | CharTy => CharTy
       | StringTy => StringTy
       | BoolTy => BoolTy
       | UnitTy => UnitTy
       | ProdTy sigmas => ProdTy (map (fn s => subst (tysub, s)) sigmas)
       | ListTy rho => ListTy (subst (tysub, rho))
       | ArrowTy(sigma0, sigma1) =>
           ArrowTy(subst (tysub, sigma0), subst(tysub, sigma1))
       | RefTy t => RefTy (subst (tysub, t))
       | Scheme(vs, rho) =>
           if List.exists (fn {sub=sub',...} => sub'=sub) vs then sigma
           else Scheme(vs, subst (tysub, rho))
  end

  (*  apply [(alpha_0,sigma_0),...,(alpha_{n-1},sigma_{n-1})] sigma =
  *  sigma{sigma_{n-1}/alpha_{n-1}}...{sigma_0/alpha_0}.
  *
  *   Note that the substitution is sequential, so if alpha_i occurs in
  *   sigma_j for i < j, then sigma_i will be substituted for alpha_i in the
  *   occurrences of sigma_j that are substituted for alpha_j.
  *)
  fun apply (s : typesubst) (sigma : typ) : typ =
    foldr subst sigma s

  (*  applyExp tysub e = e', where e' is obtained from e by replacing each
  *  annotation τ in e with tysub(τ).
  *)
  fun applyExp (s : typesubst) (AnnExp(e, sigma) : ann_exp) : ann_exp =
    AnnExp(applyBareExp s e, apply s sigma)

  (*  appplyBarExp tysub e = e', where e' is obtained from e by replacing each
  *  annotation τ in e with tysub(τ).
  *)
  and applyBareExp (s : typesubst) (e : exp) : exp =
    case e of
         Ident x => Ident x
       | IntNum n => IntNum n
       | RealNum x => RealNum x
       | Char c => Char c
       | Str s => Str s
       | Bool b => Bool b
       | Plus(e0, e1) => Plus(applyExp s e0, applyExp s e1)
       | Minus(e0, e1) => Minus(applyExp s e0, applyExp s e1)
       | Times(e0, e1) => Times(applyExp s e0, applyExp s e1)
       | Div(e0, e1) => Div(applyExp s e0, applyExp s e1)
       | Mod(e0, e1) => Mod(applyExp s e0, applyExp s e1)
       | Lt(e0, e1) => Lt(applyExp s e0, applyExp s e1)
       | Gt(e0, e1) => Gt(applyExp s e0, applyExp s e1)
       | Le(e0, e1) => Le(applyExp s e0, applyExp s e1)
       | Ge(e0, e1) => Ge(applyExp s e0, applyExp s e1)
       | Eq(e0, e1) => Eq(applyExp s e0, applyExp s e1)
       | Ne(e0, e1) => Ne(applyExp s e0, applyExp s e1)
       | Orelse(e0, e1) => Orelse(applyExp s e0, applyExp s e1)
       | Andalso(e0, e1) => Andalso(applyExp s e0, applyExp s e1)
       | Cat(e0, e1) => Cat(applyExp s e0, applyExp s e1)
       | Cons(e0, e1) => Cons(applyExp s e0, applyExp s e1)
       | Append(e0, e1) => Append(applyExp s e0, applyExp s e1)
       | Cond(e, e0, e1) => Cond(applyExp s e, applyExp s e0, applyExp s e1)
       | Tuple(es) => Tuple(map (applyExp s) es)
       | Triv => Triv
       | List es => List(map (applyExp s) es)
       | App(e0, e1) => App(applyExp s e0, applyExp s e1)
       | Lambda((x, sigma), e) => Lambda((x, apply s sigma), applyExp s e)
       | Let(ds, e) => Let(applyDecs s ds, applyExp s e)
       | Assign(e', e) => Assign(applyExp s e', applyExp s e)
       | Seq es => Seq (map (applyExp s) es)
       | While(e', e) => While(applyExp s e', applyExp s e)

  (*  applyDecs tysub [d_0,...,d_{n-1}] = [d_0',...,d_{n-1}'], where
  *   d_i' is obtained by replacing each annotation τ in d_i with
  *   tysub(τ).
  *)
  and applyDecs (s : typesubst) (ds : dec list) : dec list =
  let
    fun applyDec (d : dec) : dec =
      case d of
           ValDec(x, t, e) => ValDec(x, apply s t, applyExp s e)
         | FunDec(f, t, xs, e) =>
             FunDec(
               f,
               apply s t,
               map (fn (x', t') => (x', apply s t')) xs,
               applyExp s e
             )
         | DoDec e => DoDec(applyExp s e)
  in
    map applyDec ds
  end

  (*  substEqn tysub (t0 == t1) = (subst (tysub, t0) == subst (tysub t1)).
  *)
  fun substEqn (tysub : tyvar*typ) ((t0 == t1) : equation) : equation =
    subst (tysub, t0) == subst (tysub, t1)

  (* ********************
  *  INFERENCE FUNCTIONS
  *  ********************
  *)

  exception TypeError
  exception UnifyError
  exception UnboundIdError of string

  fun typeOf (AnnExp(_, t) : ann_exp) : typ =
    t

  fun lowerLevels (l : int) (t : typ) : unit =
    case t of
         v as Var {sub, lvl, flags} => lvl := Int.min(!lvl, l)
       | (IntTy | RealTy | CharTy | StringTy | BoolTy | UnitTy) => ()
       | ProdTy ts => List.app (lowerLevels l) ts
       | ListTy t => lowerLevels l t
       | ArrowTy(t0, t1) => (lowerLevels l t0 ; lowerLevels l t1)
       | RefTy t => lowerLevels l t
       | Scheme(vs, t) => raise LibBase.Impossible "lowerLevels (Scheme)"

  (*  occurs v t = true,  if v occurs in t
  *              = false, otherwise.
  *  Pre-condition:  t is not a type scheme.
  *)
  fun occurs (v as {sub, lvl, flags} : tyvar) (t : typ) : bool =
    case t of
         Var {sub=sub', ...} => sub = sub'
       | IntTy => false
       | RealTy => false
       | CharTy => false
       | StringTy => false
       | BoolTy => false
       | UnitTy => false
       | ProdTy ts => List.exists (occurs v) ts
       | ListTy t => occurs v t
       | ArrowTy(t0, t1) => occurs v t0 orelse occurs v t1
       | RefTy t => occurs v t
       | Scheme _ => raise LibBase.Impossible "Type.occurs Scheme"

  (*  unify eqns = tysub, where tysub is the most general unifier of eqns.  In
  *  other words,
  *  - tysub is a unifier for eqns:  for each t0 == t1 in eqns,
  *    tysub(t0) = tysub(t1); and
  *  - If tysub' is a unifier for tysub, then tysub' is an instance of tysub'':
  *    tysub' = tysub'' o tysub for some tysub''.
  *
  *  Raises:  UnifyError if eqns does not have a unifier.
  *)
  fun unify (eqns : equation list) : typesubst =
  let
    (*  unify1 finished eqns = tysub, where tysub is a most general unifier of
    *  eqns that is an instance of finished.
    *
    *  Pre-conditions:
    *  - If α ∈ dom(finished), then α does not occur in eqns;
    *
    *  Raises:  UnifyError if eqns does not have a unifier that is an instance
    *  of finished.
    *)
    fun unify1 (finished : typesubst) (eqns : equation list) : typesubst =
    let
      val () = dbg_printnl (String.concat [
        "\tEqns:  ",
        ListFormat.listToString eqnToString eqns,
        "; finished:  ",
        typesubstToString finished
      ])
    in
      case eqns of
           [] => finished
         | (
             IntTy == IntTy |
             RealTy == RealTy |
             StringTy == StringTy |
             CharTy == CharTy |
             BoolTy == BoolTy |
             UnitTy == UnitTy
           ) :: eqns => unify1 finished eqns
         | (Var (tv0 as {sub=s0, lvl=l0, flags=f0})) ==
           (v1 as Var {sub=s1, lvl=l1, flags=f1}) :: eqns =>
             (*  Don't do an occurs check in this case in case s1 = s0.
             *)
             if s0 = s1 then unify1 finished eqns
             else
             let
               val () = l1 := Int.min(!l0, !l1)
               val () = f1 := mergeFlags(!f0, !f1)
               val sigma = (tv0, v1)
             in
               unify1 (sigma :: finished) (map (substEqn sigma) eqns)
             end
         | (
             (v as Var (tv as {sub, lvl, flags})) == t |
             t == (v as Var (tv as {sub, lvl, flags}))
           ) :: eqns =>
             if occurs tv t then raise UnifyError
             else
               let
                 (*  Comment this out to check whether the testing framework
                 *  catches bad generalization errors.
                 *)
                 val () = lowerLevels (!lvl) t
                 (*
                 val () = if hasFlag EQTYPE (!flags) then makeEqType t
                          else ()
                 *)
                 val () = enforceFlags (!flags) t
                 val sigma = (tv, t)
               in
                 unify1 (sigma :: finished) (map (substEqn sigma) eqns)
               end
         | ArrowTy(t0, t1) == ArrowTy(t0', t1') :: eqns =>
             unify1 finished (t0 == t0' :: t1 == t1' :: eqns)
         | ProdTy ts == ProdTy ts' :: eqns =>
             unify1 finished ((ListPair.map op== (ts, ts')) @ eqns)
         | ListTy t == ListTy t' :: eqns =>
             unify1 finished (t == t' :: eqns)
         | RefTy t == RefTy t' :: eqns =>
             unify1 finished (t == t' :: eqns)
         | _ => raise UnifyError
    end
  in
    unify1 [] eqns
  end

  fun generalize (lvl : int) (t : typ) : typ =
  let

    fun specPlusTy (fvs : tyvar list) : typesubst =
      case fvs of
           [] => []
         | (tv as {flags,...}) :: fvs =>
             if hasFlag PLUSTYPE (!flags) then (tv, IntTy) :: specPlusTy fvs
             else specPlusTy fvs

    val fvs = List.filter (fn {lvl=l,...} => !l > lvl) (freevars t)

    val (fvs, t) =
      if lvl > 0 then (fvs, t)
      else
      let
        val s = specPlusTy fvs
        val t = apply s t
        val fvs = List.filter (fn {lvl=l,...} => !l > lvl) (freevars t)
      in
        (fvs, t)
      end

  in
    Scheme(fvs, t)
  end


  fun inferDec
      (eta : typ env)
      (next : int)
      (lvl : int)
      (d : Ast.dec) : dec*int*(equation list) =
    case d of
         Ast.ValDec(x, e) =>
         let
           val (e_ann, next_e, eqns_e) = inferAll eta next (lvl+1) e
           val mgu = unify eqns_e
           val e_ann' = applyExp mgu e_ann
           val t = generalize lvl (typeOf e_ann')

           val () = dbg_printnl (
             "\tGot " ^ x ^ " : " ^ typeToString t
           )
         in
           (ValDec(x, t, e_ann'), next_e, eqns_e)
         end
       | Ast.FunDec(f, xs, e) =>
         let
           fun newtvs next ys =
             case ys of
                  [] => ([], next)
                | y :: ys =>
                  let
                    val (zs, next) = newtvs next ys
                    val v = Var {sub=next, lvl=ref (lvl+1), flags=ref []}
                  in
                    ((y, v) :: zs, next+1)
                  end

           val (xs', next') = newtvs next xs
           val eta' = updateMany eta xs'

           val t_e = Var {sub=next', lvl=ref (lvl+1), flags=ref []}
           val next'' = next' + 1

           fun makeArrowTy ys =
             case ys of
                  [] => t_e
                | (_, v) :: ys => ArrowTy(v, makeArrowTy ys)

           val t = makeArrowTy xs'
           val eta'' = update eta' f t

           val (e_ann, next_e, eqns_e) = inferAll eta'' next'' (lvl+1) e

           val eqns = (t_e == typeOf e_ann) :: eqns_e
           val mgu = unify eqns

           val xs' = map (fn (x, t) => (x, apply mgu t)) xs'
           val e_ann' = applyExp mgu e_ann
           val t_f = generalize lvl (apply mgu t)

           val () = dbg_printnl (
             "\tGot " ^ f ^ " : " ^ typeToString t_f
           )
         in
           (FunDec(f, t_f, xs', e_ann'), next_e, eqns)
         end
       | Ast.DoDec e =>
         let
           val (e_ann, next, eqns) = inferAll eta next lvl e
           val eqns = (typeOf e_ann == UnitTy) :: eqns
           val mgu = unify eqns

           val e_ann' = applyExp mgu e_ann
         in
           (DoDec e_ann', next, eqns)
         end

  and inferDecs
      (eta : typ env)
      (next : int)
      (lvl : int)
      (ds : Ast.dec list) : (dec list)*int*(equation list) =
    case ds of
         [] => ([], next, [])
       | d :: ds =>
         let
           val (d', next', eqns') = inferDec eta next lvl d
           (*
           val eta' = update' eta (
             case d' of
                  ValDec(x, t, _) => (x, t)
                | FunDec(f, t, _, _) => (f, t)
           )
           *)
           val eta' =
             case d' of
                  (ValDec(x, t, _) | FunDec(x, t, _, _)) =>
                    update' eta (x, t)
                | _ => eta
           val (ds', next'', eqns'') = inferDecs eta' next' lvl ds
         in
           (d' :: ds', next'', eqns' @ eqns'')
         end

  (*  inferAll eta next l e = (e', k, eqns), where
  *   - e' is an annotated version of e;
  *   - If α_i is created in annotating e, then i >= next;
  *   - k > max(next, max{ i | α_i created in annotating e})
  *   - eqns are the equations generated from the annotation of e.
  *)
  and inferAll
      (eta : typ env)
      (next : int)
      (lvl : int)
      (e : Ast.exp) : ann_exp*int*equation list =
  let
    val () = dbg_printnl (Ast.expToString e)

    (*  inferAllBin rator (e0, e1) eqns = (e, next', eqs), where
    *   - e = AnnExp(rator(e_0', e_1'), t_e), where e_i' is the annotated
    *         versions of e_i;
    *   - t_e is a fresh type variable assigned to e;
    *   - eqs = eqns (t_e, t_0, t_1) @ eqs0 @ eqs1, where t_i is the
    *     type of e_i' and eqs_i is the equations generated from the
    *     annotations for e_i.
    *)
    fun inferAllBin
        (rator : ann_exp*ann_exp -> exp)
        ((e0, e1) : Ast.exp*Ast.exp)
        (eqns : typ*typ*typ -> equation list) : ann_exp*int*equation list =
    let
      val (e0_ann, next0, eqns0) = inferAll eta next lvl e0
      val (e1_ann, next1, eqns1) = inferAll eta next0 lvl e1

      val t_e = Var{sub=next1, lvl=ref lvl, flags=ref []}
      val e_ann = AnnExp(rator(e0_ann, e1_ann), t_e)
      val next_e = next1 + 1

      val eqns_e = eqns (t_e, typeOf e0_ann, typeOf e1_ann)

      val () = dbg_printnl ("\t" ^ (ListFormat.listToString eqnToString eqns_e))
    in
      (e_ann, next_e, eqns_e @ eqns0 @ eqns1)
    end

    fun inferAllComparison
      (rator : ann_exp*ann_exp -> exp)
      ((e0, e1) : Ast.exp*Ast.exp) : ann_exp*int*equation list =
         inferAllBin
         rator
         (e0, e1)
         (fn (t_e, t0, t1) => [t_e == BoolTy, t0 == t1])

    fun inferEqNe
        (rator : ann_exp*ann_exp -> exp)
        ((e0, e1) : Ast.exp*Ast.exp) : ann_exp*int*equation list =
    let
      val (e0_ann, next0, eqns0) = inferAll eta next lvl e0
      val (e1_ann, next1, eqns1) = inferAll eta next0 lvl e1
      val v0 = Var {sub=next1, lvl=ref lvl, flags=ref [EQTYPE]}
      val v1 = Var {sub=next1+1, lvl=ref lvl, flags=ref [EQTYPE]}
      val e_ann = AnnExp(rator(e0_ann, e1_ann), BoolTy)
      val next = next1+2

      val eqns = [
        typeOf e0_ann == typeOf e1_ann,
        typeOf e0_ann == v0,
        typeOf e1_ann == v1
      ]
    in
      (e_ann, next, eqns @ eqns0 @ eqns1)
    end



    fun inferAllMany
        (es : Ast.exp list) : ann_exp list*int*equation list =
      case es of
           [] => ([], next, [])
         | e :: es =>
           let
             val (aes, next, eqs) = inferAllMany es
             val (ae, next', eqs') = inferAll eta next lvl e
           in
             (ae :: aes, next', eqs' @ eqs)
           end

  in
    case e of
         Ast.Ident x =>
         (
         (
           case get eta x of
                (*
                v as Var {sub,...} =>
                  (AnnExp(Ident x, v), Int.max(next, sub+1), [])
                *)
                Scheme(tvs, t) =>
                  let
                    fun makeSubsts
                        (nextSub : int) (tvs : tyvar list) : typesubst =
                      case tvs of
                           [] => []
                         | (v as {sub=sub,lvl=l,flags=fs}) :: tvs =>
                             (v, Var {sub=nextSub, lvl=ref lvl, flags=ref (!fs)}) ::
                             makeSubsts (nextSub+1) tvs
                    val s = makeSubsts next tvs
                  in
                    (AnnExp(Ident x, apply s t), next+length tvs, [])
                  end
              | t => (AnnExp(Ident x, t), next, [])
         )
         handle NotFound => raise UnboundIdError x
         )
       | Ast.IntNum n => (AnnExp(IntNum n, IntTy), next, [])
       | Ast.RealNum x => (AnnExp(RealNum x, RealTy), next, [])
       | Ast.Char c => (AnnExp(Char c, CharTy), next, [])
       | Ast.Str s => (AnnExp(Str s, StringTy), next, [])
       | Ast.Bool b => (AnnExp(Bool b, BoolTy), next, [])
       | Ast.Plus(e0, e1) =>
           inferAllBin
             Plus (e0, e1) (fn (t_e, t0, t1) => [t_e == t0, t0 == t1])
           (*
         let
           val (e0_ann, next0, eqns0) = inferAll eta next lvl e0
           val (e1_ann, next1, eqns1) = inferAll eta next lvl e1

           val v0 = Var {sub=next1, lvl=ref lvl, flags=ref [PLUSTYPE]}
           val v1 = Var {sub=next1+1, lvl=ref lvl, flags=ref [PLUSTYPE]}

           val v = Var {sub=next1+2, lvl=ref lvl, flags=ref []}

           val eqns = [
             v0 == typeOf e0_ann,
             v1 == typeOf e1_ann,
             v0 == v1,
             v == v0
           ]

           val () =
             dbg_printnl ("\t" ^ (ListFormat.listToString eqnToString eqns))
         in
           (AnnExp(Plus(e0_ann, e1_ann), v), next1+3, eqns @ eqns0 @ eqns1)
         end
         *)
       | Ast.Minus(e0, e1) =>
           inferAllBin
             Minus (e0, e1) (fn (t_e, t0, t1) => [t_e == t0, t0 == t1])
       | Ast.Times(e0, e1) =>
           inferAllBin
             Times (e0, e1) (fn (t_e, t0, t1) => [t_e == t0, t0 == t1])
       | Ast.Div(e0, e1) =>
           inferAllBin
             Div
             (e0, e1)
             (fn (t_e, t0, t1) => [t_e == IntTy, t0 == IntTy, t1 == IntTy])
       | Ast.Mod(e0, e1) =>
           inferAllBin
             Mod
             (e0, e1)
             (fn (t_e, t0, t1) => [t_e == IntTy, t0 == IntTy, t1 == IntTy])
       | Ast.Slash(e0, e1) =>
           inferAllBin
             Div
             (e0, e1)
             (fn (t_e, t0, t1) => [t_e == RealTy, t0 == RealTy, t1 == RealTy])
       | Ast.Cat(e0, e1) =>
           inferAllBin
             Cat
             (e0, e1)
             (fn (t_e, t0, t1) =>
               [t_e == StringTy, t0 == StringTy, t1 == StringTy])
       | Ast.Eq es => inferEqNe Eq es
       | Ast.Ne es => inferEqNe Ne es
       | Ast.Lt es => inferAllComparison Lt es
       | Ast.Le es => inferAllComparison Le es
       | Ast.Gt es => inferAllComparison Gt es
       | Ast.Ge es => inferAllComparison Ge es
       | Ast.Andalso(e0, e1) =>
           inferAllBin
             Andalso
             (e0, e1)
             (fn (t_e, t0, t1) => [t_e == BoolTy, t0 == BoolTy, t1 == BoolTy])
       | Ast.Orelse(e0, e1) =>
           inferAllBin
             Orelse
             (e0, e1)
             (fn (t_e, t0, t1) => [t_e == BoolTy, t0 == BoolTy, t1 == BoolTy])
       | Ast.Cons(e0, e1) =>
           inferAllBin
             Cons
             (e0, e1)
             (fn (t_e, t0, t1) => [t_e == t1, t1 == ListTy t0])
       | Ast.Append(e0, e1) =>
         let
           val (ae, next, eqs) =
             inferAllBin
               Append
               (e0, e1)
               (fn (t_e, t0, t1) => [t_e == t0, t0 == t1])
           val t = ListTy (Var {sub=next, lvl=ref lvl, flags=ref []})
         in
           (ae, next+1, typeOf ae == t :: eqs)
         end


       | Ast.Cond(e, e0, e1) =>
         let
           val (e_ann, next_e, eqns_e) = inferAll eta next lvl e
           val (e0_ann, next0, eqns0) = inferAll eta next_e lvl e0
           val (e1_ann, next1, eqns1) = inferAll eta next0 lvl e1

           val eqns = [
             typeOf e_ann == BoolTy,
             typeOf e0_ann == typeOf e1_ann
           ]

           val () =
             dbg_printnl ("\t" ^ (ListFormat.listToString eqnToString eqns_e))
         in
           (AnnExp(Cond(e_ann, e0_ann, e1_ann), typeOf e0_ann),
            next1,
            eqns @ eqns_e @ eqns0 @ eqns1
           )
         end

       | Ast.List [] =>
         let
           val t = Var {sub=next, lvl=ref lvl, flags=ref []}
         in
           (AnnExp(List [], ListTy t), next+1, [])
         end

       | Ast.List es =>
         let
           val (aes, next, eqs) = inferAllMany es

           fun identifyTypes (aes : ann_exp list) : equation list =
             case aes of
                  [] => []
                | [ae] => []
                | AnnExp(_, t) :: ae :: aes =>
                    t == typeOf ae :: identifyTypes (ae :: aes)

           val new_eqns = identifyTypes aes
         in
           (AnnExp(List aes, ListTy (typeOf (hd aes))), next, new_eqns @ eqs)
         end

       | Ast.App(e0, e1) =>
           inferAllBin
             App
             (e0, e1)
             (fn (t_e, t0, t1) => [t0 == ArrowTy(t1, t_e)])


       | Ast.Lambda(x, e) =>
           let
             val t_x = Var {sub=next, lvl=ref lvl, flags=ref []}
             val eta' = update eta x t_x
             val (e_ann, next_e, eqns_e) = inferAll eta' (next+1) lvl e

             val lambda_ann = AnnExp(Lambda((x, t_x), e_ann),
                                     ArrowTy(t_x, typeOf e_ann))
             val next_lambda = next_e
             val eqns_lambda = eqns_e
           in
             (lambda_ann, next_lambda, eqns_lambda)
           end

       | Ast.Tuple es =>
           let
             fun doAll es =
               case es of
                    [] => ([], next, [])
                  | e :: es =>
                      let
                        val (es', next', eqns') = doAll es
                        val (e_ann, next_e, eqns_e) = inferAll eta next' lvl e
                      in
                        (e_ann :: es', next_e, eqns_e @ eqns')
                      end
             val (es_ann, next_es, eqns_es) = doAll es
             val t_es = map typeOf es_ann
           in
             (AnnExp(Tuple es_ann, ProdTy t_es), next_es, eqns_es)
           end

       | Ast.Triv =>
           (AnnExp(Triv, UnitTy), next, [])

       | Ast.Let(ds, e) =>
         let
           val (ds_ann, next', eqns') = inferDecs eta next lvl ds

           fun decTypes (ds : dec list) : (ident*typ) list =
             case ds of
                  [] => []
                | ValDec(x, t, _) :: ds => (x, t) :: decTypes ds
                | FunDec(f, t, _, _) :: ds => (f, t) :: decTypes ds
                | DoDec _ :: ds => decTypes ds

           val eta' =
             updateMany eta (decTypes ds_ann)

           val (e_ann, next_e, eqns_e) = inferAll eta' next' lvl e
           val t_ann = typeOf e_ann

           val let_ann = AnnExp(Let(ds_ann, e_ann), t_ann)
           val let_next = next_e
           val let_eqns = List.filter (fn e => eqnLevelBound e lvl) eqns'
           val () =
             dbg_printnl
             ("\t" ^ (ListFormat.listToString eqnToString let_eqns))
         in
           (let_ann, let_next, let_eqns @ eqns_e)
         end

      | Ast.Assign(e', e) =>
        let
          val (e'_ann, next', eqns') = inferAll eta next lvl e'
          val (e_ann, next, eqns) = inferAll eta next' lvl e

          val assign_eqns = [typeOf e'_ann == RefTy(typeOf e_ann)]
           val () =
             dbg_printnl
             ("\t" ^ (ListFormat.listToString eqnToString assign_eqns))
        in
          (AnnExp(Assign(e'_ann, e_ann), UnitTy), next,
            assign_eqns @ eqns' @ eqns)
        end

      | Ast.Seq(es) =>
        let
          fun doAll es =
            case es of
                 [] => ([], next, [])
               | e :: es =>
                   let
                     val (es', next', eqns') = doAll es
                     val (e_ann, next_e, eqns_e) = inferAll eta next' lvl e
                   in
                     (e_ann :: es', next_e, eqns_e @ eqns')
                   end
          val (es_ann, next_es, eqns_es) = doAll es
        in
          (AnnExp(Seq es_ann, typeOf(List.last es_ann)), next_es, eqns_es)
        end

      | Ast.While(e', e) =>
        let
          val (e'_ann, next', eqns') = inferAll eta next lvl e'
          val (e_ann, next, eqns) = inferAll eta next' lvl e

          val while_eqns = [typeOf e'_ann == BoolTy]
          val () =
            dbg_printnl
            ("\t" ^ (ListFormat.listToString eqnToString while_eqns))
        in
          (AnnExp(While(e'_ann, e_ann), UnitTy), next,
            while_eqns @ eqns' @ eqns)
        end

      | Ast.Proj n =>
          raise LibBase.Unimplemented "Type.inferAll Proj"



  end


  (*  The base environment.
  *)
  fun baseEnv() : (typ env)*int =
  let
    val alpha : tyvar = {sub=0, lvl=ref 0, flags=ref []}
    val eta =
      updateMany Env.empty [
        ("not", ArrowTy(BoolTy, BoolTy)),
        ("hd", Scheme([alpha], ArrowTy(ListTy (Var alpha), Var alpha))),
        ("tl", Scheme([alpha], ArrowTy(ListTy (Var alpha), ListTy (Var alpha)))),
        ("null", Scheme([alpha], ArrowTy(ListTy (Var alpha), BoolTy))),
        ("length", Scheme([alpha], ArrowTy(ListTy (Var alpha), IntTy))),
        ("explode", ArrowTy(StringTy, ListTy CharTy)),
        ("implode", ArrowTy(ListTy CharTy, StringTy)),
        ("real", ArrowTy(IntTy, RealTy)),
        ("ref", Scheme([alpha], ArrowTy(Var alpha, RefTy(Var alpha)))),
        ("!", Scheme([alpha], ArrowTy(RefTy(Var alpha), Var alpha))),
        ("printInt", ArrowTy(IntTy, UnitTy)),
        ("printReal", ArrowTy(RealTy, UnitTy)),
        ("printBool", ArrowTy(BoolTy, UnitTy)),
        ("printString", ArrowTy(StringTy, UnitTy))
      ]
  in
    (eta, 1)
  end

  (*  infer e = τ, where τ is the type inferred for e in the base environment.
  *
  *   Raises:
  *   - EqTypeError if some declaration or expression statement in p cannot
  *     be typed because of an attempt to test equality between two expressions
  *     of non-equality type.
  *   - TypeError if some declaration or expression statement in p cannot
  *     be typed for any other reason.
  *)
  fun infer (e : Ast.exp) : typ =
  let
    val (baseEnv, next) = baseEnv()
    val () = dbg_printnl "inferAll..."
    val (AnnExp(_, ann), _, eqns) = inferAll baseEnv next 0 e
    val () = dbg_printnl (String.concat [
      "got equations:\n",
      ListFormat.fmt {init="\t", final="", sep="\n\t", fmt=eqnToString} eqns
    ])
    val () = dbg_printnl "unify..."
    val mgu = unify eqns
    val () = dbg_printnl (String.concat [
      "got mgu:\n",
      typesubstToString mgu
    ])
    val () = dbg_printnl "apply mgu..."
    val t = apply mgu ann
    val () = dbg_printnl "done."
  in
    t
  end
  handle UnifyError => raise TypeError

  (*  typecheck p = p', where p' is the type-annotated version of p.
  *
  *   Raises:
  *   - EqTypeError if some declaration or expression statement in p cannot
  *     be typed because of an attempt to test equality between two expressions
  *     of non-equality type.
  *   - TypeError if some declaration or expression statement in p cannot
  *     be typed for any other reason.
  *)
  fun typecheck (Ast.Program ss : Ast.pgm) : pgm =
  let
    val (baseEnv, next) = baseEnv()

    fun instantiateTVsAtUnit
        (tvs: tyvar list, tau : typ, ps : (Ast.ident*typ) list, e : ann_exp) =
    let
      val tysub : typesubst = map (fn alpha => (alpha, UnitTy)) tvs
      val tau' = apply tysub tau
      val ps' = map (fn (p, t) => (p, apply tysub t)) ps
      val e' = applyExp tysub e
    in
      (tau', ps', e')
    end


    fun instantiateSchemeAtUnit (d : dec) : dec =
      case d of
           FunDec(f, Scheme(tvs, tau), ps, e) =>
           let
             val (tau', ps', e') = instantiateTVsAtUnit(tvs, tau, ps, e)
           in
             FunDec(f, Scheme([], tau'), ps', e')
           end
         | _ => raise TypeError


    fun checkStms
        (eta : typ env)
        (next : int)
        (ss : Ast.stm list) : stm list =
      case ss of
           [] => []
         | Ast.Dec d :: ss =>
           let
             val (d', next', eqns') = inferDec eta next 0 d
             val d' = instantiateSchemeAtUnit d'
             val (id, t) =
               case d' of
                    ValDec(x, t, _) => (x, t)
                  | FunDec(f, t, _, _) => (f, t)
                  | DoDec _ => raise TypeError
             val eta' = update eta id t
           in
             Dec d' :: checkStms eta' next' ss
           end
         | _ =>
           LibBase.failure {
             module="Type",
             func="typecheck.checkStms",
             msg="Invalid program:  non-declaration at top level"
           }
  in
    Program (checkStms baseEnv next ss)
  end
  handle UnifyError => raise TypeError

  (*  typePgm p = [x_0, τ_0,...,(x_{n-1}, τ_{n-1}], where
  *   [x_0,...,x_{n-1}] is the list of identifiers in value and function
  *   declarations in p in the order they occur, and τ_i is the type inferred
  *   for the value of x_i.  An expression statement
  *     e ;
  *   is treated as the value declaration
  *     val it = e ;
  *
  *   The declaration for x_i is typed in the environment ρ_i, where
  *   - ρ_0 is the base environment;
  *   - ρ_{i+1} = ρ_i{x_i |-> τ_i}, if the i-th statement is a declaration
  *             = ρ_i,              if the i-th statement is an expression
  *                                 statement.
  *
  *   In other words, expression statements are typed as though the expression
  *   is the left-hand side of a value declaration with identifier "it", except
  *   that no type for "it" is added to the environment for later declarations.
  *
  *   Raises:
  *   - EqTypeError if some declaration or expression statement in p cannot
  *     be typed because of an attempt to test equality between two expressions
  *     of non-equality type.
  *   - TypeError if some declaration or expression statement in p cannot
  *     be typed for any other reason.
  *)
  fun typePgm (Ast.Program ss : Ast.pgm) : (ident*typ) list =
  let
    val (baseEnv, next) = baseEnv()

    fun checkStms
        (eta : typ env)
        (next : int)
        (ss : Ast.stm list) : (ident*typ) list =
      case ss of
           [] => []
         | Ast.ExprStm e :: ss =>
             let
               val (e, next, eqns) = inferAll eta next 0 e
               val mgu = unify eqns
               val t = generalize 0 (apply mgu (typeOf e))
             in
               ("it", t) :: checkStms eta next ss
             end
         | Ast.Dec d :: ss =>
           let
             val (d', next', eqns') = inferDec eta next 0 d
             val (id, t) =
               case d' of
                    ValDec(x, t, _) => (x, t)
                  | FunDec(f, t, _, _) => (f, t)
                  | DoDec _ => raise TypeError
             val eta' = update eta id t
           in
             (id, t) :: checkStms eta' next' ss
           end
  in
    checkStms baseEnv next ss
  end
  handle UnifyError => raise TypeError



end
