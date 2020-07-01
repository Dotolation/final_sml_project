(*  COMP 323 Project 4:  Imperative features.
*
*  N. Danner
*  Spring 2019
*)

structure CEKInterp =
struct

  val debug = false ;

  fun dbg_print (s : string) : unit =
    if debug then print s else ()

  fun dbg_printnl (s : string) : unit =
    dbg_print (s ^ "\n")

  (*  Environments.  We'll use ORD_MAPs.
  *)

  structure Env = SplayMapFn(
    struct 
      type ord_key = Ast.ident 
      val compare = String.compare 
    end)

  type 'a env = 'a Env. map

  exception NotFound of string

  fun get (rho : 'a env) (x : Ast.ident) : 'a =
    valOf(Env.find(rho, x))
    handle Option => raise NotFound x

  fun update (rho : 'a env) (x : Ast.ident) (y : 'a) : 'a env =
    Env.insert(rho, x, y)

  fun updateMany (rho : 'a env) (kvs : (Ast.ident*'a) list) : 'a env =
    foldl Env.insert' rho kvs

  fun envToString (toString : 'a -> string) (rho : 'a env) : string =
    ListFormat.fmt {
      init="{", sep=", ", final="}",
      fmt=fn(x, y) => String.concat [
        x,
        " |-> ",
        toString y
      ]
    }
    (Env.listItemsi rho)

  (*  Values.  Most are self-explanatory.
  *
  *  RecClosure(f, [x_k,...,x_{n-1}], e, rho, [(x_0,v_0),...,x_{k-1}, v_{k-1}])
  *  represents the (possibly) recursive function f x_0 ... x_{n-1} that has
  *  been partially applied to v_0,...,v_{k-1}.
  *
  *  Builtin id represents the built-in function id.  Each built-in function
  *  is associated to a function that maps values to values, specified by the
  *  baseEnv environment.
  *)
  datatype value = Int of int | Real of real | Char of char | Str of string
                 | Bool of bool | Triv
                 | Tuple of value list | List of value list
                 | Closure of Ast.ident*Ast.exp*value env
                 | RecClosure of Ast.ident*(Ast.ident list)*Ast.exp*value env*
                                 ((Ast.ident*value) list)
                 | Proj of int
                 | Builtin of Ast.ident


  (*  dbg_valueToString v = a string representation of v.
  *)
  fun dbg_valueToString (v : value) : string =
    case v of
         Int n => Int.toString n
       | Real x => Real.toString x
       | Char c => "#\"" ^ Char.toString c ^ "\""
       | Str s => "\"" ^ String.toString s ^ "\""
       | Bool b => Bool.toString b
       | Triv => "()"
       | Tuple vs => 
           ListFormat.fmt {init="(", final=")", sep=",", fmt=dbg_valueToString} vs
       | List vs =>
           ListFormat.listToString dbg_valueToString vs
       | Closure(x, _, _) => 
           String.concat [
             "(fn ",
             x,
             " => ...){...}"
           ]
       | RecClosure(f, xs, _, _, ps) =>
           String.concat [
             "(recfn ",
             ListFormat.fmt 
               {init="", final="", sep=" ", fmt=String.toString}
               xs,
             " => ...)",
             ListFormat.fmt
               {init="{", final="}", sep=", ",
                fmt=fn (x, v) => x ^ "|->" ^ (dbg_valueToString v)}
               ps
           ]
       | Proj n => "#" ^ (Int.toString n)
       | Builtin id => id

  (*  The base environment of built-in functions.  The parser considers these
  *  ordinary identifiers, but we know better...  The implementation of a
  *  built-in function is a function that maps values to values.  We only need
  *  the implementation when we've evaluated the argument to an application and
  *  the operator is a builtin (Builtin value), in which case we apply
  *  implementation to the operator value and continue.  
  *)
  val baseEnv : (value -> value) env = updateMany Env.empty [
    ("hd", fn (List (x :: xs)) => x),
    ("tl", fn (List (x :: xs)) => List xs),
    ("null", fn (List xs) => Bool(null xs)),
    ("not", fn (Bool b) => Bool(not b)),
    ("real", fn (Int n) => Real(real n)),
    ("length", fn (List xs) => Int(length xs)),
    ("implode", fn (List cs) => Str(implode (map (fn (Char c) => c) cs))),
    ("explode", fn (Str s) => List(map Char (explode s))),
    ("printInt", fn (Int n) => (print (Int.toString n ^ "\n") ; Triv)),
    ("printReal", fn (Real n) => (print (Real.toString n ^ "\n") ; Triv)),
    ("printBool", fn (Bool n) => (print (Bool.toString n ^ "\n") ; Triv))
  ]

  (*  **********
  *   CEK machine types.
  *   **********
  *)

  type exp = Ast.exp

  (*  A closure is an expression e along with an environment that binds the
  *  free variables of e.
  *)
  type closure = exp*value env

  (*  A control string for the CEK machine is either a closure or a value.
  *)
  datatype ctrl = C of closure | V of value

  (*  Arithmetic operations for the KArithOp continuations.
  *)
  datatype arith_op = AOPlus
                    | AOMinus
                    | AOTimes
                    | AODiv
                    | AOMod

  (*  Relational operations for the KRel continuations.
  *)
  datatype rel_op = ROLt
                  | ROLe
                  | ROGt
                  | ROGe

  (*  Continuations.
  *)
  datatype cont = KArithOp1 of closure*arith_op
                | KArithOp2 of value*arith_op
                | KRel1 of closure*rel_op
                | KRel2 of value*rel_op
                | KEq1 of closure | KEq2 of value
                | KNeq1 of closure | KNeq2 of value
                | KCons1 of closure | KCons2 of value
                | KAppend1 of closure | KAppend2 of value
                | KCat1 of closure | KCat2 of value
                | KOr of closure | KAnd of closure 
                | KCond of exp*exp*value env
                | KApp1 of closure | KApp2 of value
                | KTuple of (value list)*(exp list)*(value env)
                | KList of (value list)*(exp list)*(value env)
                | KLet of Ast.ident*(Ast.dec list)*exp*value env
                | KLetVal of Ast.ident*(Ast.dec list)*exp*value env
                | KLetDo of (Ast.dec list)*exp*value env

  (*  The state of the CEK machine is a control string and a continuation
  *  stack.
  *)
  type state = ctrl*(cont list)

  (*  stateToString s = a string representation of s.
  *)
  fun stateToString ((c, _) : state) : string =
    case c of
         C(e, rho) => Ast.expToString e ^ envToString (dbg_valueToString) rho
       | V v => dbg_valueToString v

  (*  Exception raised when testing equality of two values that are not of
  *  equality type.  Really, when the two values are not "equality-testable,"
  *  which means that they are both Int, Char, Str, or Bool, or they are Tuple
  *  of List values of equality-testable values.
  *)
  exception NotEquality of value*value

  (*  equal(v0, v1) = true,  if v0 and v1 represent the same value,
  *                 = false, otherwise.
  *   Raises NotEquality if v0 and v1 are not equality-testable.
  *)
  fun equal (v0 : value, v1 : value) : bool =
    case (v0, v1) of
         (Int n0, Int n1) => n0 = n1
       | (Char c0, Char c1) => c0 = c1
       | (Str s0, Str s1) => s0 = s1
       | (Bool b0, Bool b1) => b0 = b1
       | (Real x0, Real x1) => Real.==(x0, x1)
       | (Tuple vs0, Tuple vs1) => ListPair.allEq equal (vs0, vs1)
       | (List vs0, List vs1) => ListPair.allEq equal (vs0, vs1)
       | _ => raise (NotEquality(v0, v1))

  (* trans1 s = s', where s' is a one-step transition from s.
  *)
  fun trans1 (s : state) : state =
  let
    val () = dbg_printnl (stateToString s ^ "\n")
  in
    case s of

       (*  **********
       *   Arithmetic operators.
       *   **********
       *)

       (*  Initial closures.
       *)
         (C(Ast.Plus(e0, e1), rho), ks) =>
           (C(e0, rho), KArithOp1((e1, rho), AOPlus) :: ks)

       | (C(Ast.Minus(e0, e1), rho), ks) =>
           (C(e0, rho), KArithOp1((e1, rho), AOMinus) :: ks)

       | (C(Ast.Times(e0, e1), rho), ks) =>
           (C(e0, rho), KArithOp1((e1, rho), AOTimes) :: ks)

       | (C(Ast.Div(e0, e1), rho), ks) =>
           (C(e0, rho), KArithOp1((e1, rho), AODiv) :: ks)

       | (C(Ast.Slash(e0, e1), rho), ks) =>
           (C(e0, rho), KArithOp1((e1, rho), AODiv) :: ks)

       | (C(Ast.Mod(e0, e1), rho), ks) =>
           (C(e0, rho), KArithOp1((e1, rho), AOMod) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KArithOp1((e, rho), rator) :: ks) =>
           (C(e, rho), KArithOp2(v, rator) :: ks)

       (*  Right operand computed.
       *)
       | (V(Int n), KArithOp2(Int m, AOPlus) :: ks) =>
           (V(Int(m + n)), ks)
       | (V(Real n), KArithOp2(Real m, AOPlus) :: ks) =>
           (V(Real(m + n)), ks)

       | (V(Int n), KArithOp2(Int m, AOMinus) :: ks) =>
           (V(Int(m - n)), ks)
       | (V(Real n), KArithOp2(Real m, AOMinus) :: ks) =>
           (V(Real(m - n)), ks)

       | (V(Int n), KArithOp2(Int m, AOTimes) :: ks) =>
           (V(Int(m * n)), ks)
       | (V(Real n), KArithOp2(Real m, AOTimes) :: ks) =>
           (V(Real(m * n)), ks)

       | (V(Int n), KArithOp2(Int m, AODiv) :: ks) =>
           (V(Int(m div n)), ks)
       | (V(Real n), KArithOp2(Real m, AODiv) :: ks) =>
           (V(Real(m / n)), ks)

       | (V(Int n), KArithOp2(Int m, AOMod) :: ks) =>
           (V(Int(m mod n)), ks)

       (*  **********
       *   Relational operations.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Lt(e0, e1), rho), ks) =>
           (C(e0, rho), KRel1((e1, rho), ROLt) :: ks)
       | (C(Ast.Le(e0, e1), rho), ks) =>
           (C(e0, rho), KRel1((e1, rho), ROLe) :: ks)
       | (C(Ast.Gt(e0, e1), rho), ks) =>
           (C(e0, rho), KRel1((e1, rho), ROGt) :: ks)
       | (C(Ast.Ge(e0, e1), rho), ks) =>
           (C(e0, rho), KRel1((e1, rho), ROGe) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KRel1(cl, rator) :: ks) =>
           (C cl, KRel2(v, rator) :: ks)

       (*  Right operand computed.
       *)
       | (V(Int n), KRel2(Int m, ROLt) :: ks) =>
           (V(Bool(m < n)), ks)
       | (V(Real n), KRel2(Real m, ROLt) :: ks) =>
           (V(Bool(m < n)), ks)
       | (V(Char n), KRel2(Char m, ROLt) :: ks) =>
           (V(Bool(m < n)), ks)
       | (V(Str n), KRel2(Str m, ROLt) :: ks) =>
           (V(Bool(m < n)), ks)

       | (V(Int n), KRel2(Int m, ROLe) :: ks) =>
           (V(Bool(m <= n)), ks)
       | (V(Real n), KRel2(Real m, ROLe) :: ks) =>
           (V(Bool(m <= n)), ks)
       | (V(Char n), KRel2(Char m, ROLe) :: ks) =>
           (V(Bool(m <= n)), ks)
       | (V(Str n), KRel2(Str m, ROLe) :: ks) =>
           (V(Bool(m <= n)), ks)

       | (V(Int n), KRel2(Int m, ROGt) :: ks) =>
           (V(Bool(m > n)), ks)
       | (V(Real n), KRel2(Real m, ROGt) :: ks) =>
           (V(Bool(m > n)), ks)
       | (V(Char n), KRel2(Char m, ROGt) :: ks) =>
           (V(Bool(m > n)), ks)
       | (V(Str n), KRel2(Str m, ROGt) :: ks) =>
           (V(Bool(m > n)), ks)

       | (V(Int n), KRel2(Int m, ROGe) :: ks) =>
           (V(Bool(m >= n)), ks)
       | (V(Real n), KRel2(Real m, ROGe) :: ks) =>
           (V(Bool(m >= n)), ks)
       | (V(Char n), KRel2(Char m, ROGe) :: ks) =>
           (V(Bool(m >= n)), ks)
       | (V(Str n), KRel2(Str m, ROGe) :: ks) =>
           (V(Bool(m >= n)), ks)

       (*  **********
       *   Equality tests.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Eq(e0, e1), rho), ks) =>
           (C(e0, rho), KEq1 (e1, rho) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KEq1((e, rho)) :: ks) =>
           (C(e, rho), KEq2 v :: ks)

       (*  Right operand computed.
       *)
       | (V v1, KEq2 v0 :: ks) =>
           (V(Bool(equal(v0, v1))), ks)

       (*  **********
       *   Inequality tests.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Ne(e0, e1), rho), ks) =>
           (C(e0, rho), KNeq1(e1, rho) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KNeq1 cl :: ks) =>
           (C cl, KNeq2 v :: ks)

       (*  Right operand computed.
       *)
       | (V v1, KNeq2 v0 :: ks) =>
           (V(Bool(not (equal(v0, v1)))), ks)

       (*  **********
       *   Cons.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Cons(e0, e1), rho), ks) =>
           (C(e0, rho), KCons1(e1, rho) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KCons1 cl :: ks) =>
           (C cl, KCons2 v :: ks)

       (*  Right operand computed.
       *)
       | (V (List vs), KCons2 v :: ks) =>
           (V(List(v :: vs)), ks)

       (*  **********
       *   Append.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Append(e0, e1), rho), ks) =>
           (C(e0, rho), KAppend1(e1, rho) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KAppend1 cl :: ks) =>
           (C cl, KAppend2 v :: ks)

       (*  Right operand computed.
       *)
       | (V (List vs), KAppend2 (List vs') :: ks) =>
           (V(List(vs' @ vs)), ks)

       (*  **********
       *   String concatenation.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Cat(e0, e1), rho), ks) =>
           (C(e0, rho), KCat1(e1, rho) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KCat1 cl :: ks) =>
           (C cl, KCat2 v :: ks)

       (*  Right operand computed.
       *)
       | (V (Str s), KCat2 (Str s') :: ks) =>
           (V(Str(s' ^ s)), ks)

       (*  **********
       *   Orelse.  Ensure early termination if LHS is true.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Orelse(e0, e1), rho), ks) =>
           (C(e0, rho), KOr(e1, rho) :: ks)

       (*  Left operand true.
       *)
       | (v as V (Bool true), KOr cl :: ks) =>
           (v, ks)

       (*  Left operand false.  The value of the orelse expression is the value
       *  of the RHS.
       *)
       | (v as V (Bool false), KOr cl :: ks) =>
           (C cl, ks)

       (*  **********
       *   Andalso.  Ensure early termination if LHS is false.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Andalso(e0, e1), rho), ks) =>
           (C(e0, rho), KAnd(e1, rho) :: ks)

       (*  Left operand false.
       *)
       | (v as V (Bool false), KAnd cl :: ks) =>
           (v, ks)

       (*  Left operand true.  The value of the andalso expression is the value
       *  of the RHS.
       *)
       | (v as V (Bool true), KAnd cl :: ks) =>
           (C cl, ks)

       (*  **********
       *   Conditional.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Cond(e, e0, e1), rho), ks) =>
           (C(e, rho), KCond(e0, e1, rho) :: ks)

       (*  Test true.
       *)
       | (V (Bool true), KCond(e0, _, rho) :: ks) =>
           (C (e0, rho), ks)

       (*  Test false.
       *)
       | (V (Bool false), KCond(_, e1, rho) :: ks) =>
           (C (e1, rho), ks)

       (*  **********
       *   Application.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.App(e0, e1), rho), ks) =>
           (C (e0, rho), KApp1 (e1, rho) :: ks)

       (*  Operator evaluated.
       *)
       | (V v, KApp1 cl :: ks) =>
           (C cl, KApp2 v :: ks)

       (*  Operand evaluated and operator is projection.
       *)
       | (V (Tuple vs), KApp2 (Proj n) :: ks) =>
           (V (List.nth(vs, n-1)), ks)

       (*  Operand evaluated and operator is a built-in.
       *)
       | (V v, KApp2 (Builtin id) :: ks) =>
           (V(get baseEnv id v), ks)

       (*  Operand evaluated and operator is a non-recursive closure.
       *)
       | (V v1, KApp2 (Closure (x, e0', rho0')) :: ks) =>
           (C (e0', update rho0' x v1), ks)

       (*  Operand evaluated and operator is a (potentially) recursive closure
       *  with one unfilled parameter.  Evaluate the body.
       *)
       | (V v1, KApp2 (RecClosure (f, [x], e0', rho0', ps)) :: ks) =>
           let
             val ps' = (x, v1) :: ps
             val rho0'' = updateMany rho0' ps'
             (*  paramIds = (rev o (map #1)) ps' *)
             val paramIds = foldl (fn ((k, _), r) => k :: r) [] ps'
           in
             (C (e0', update rho0'' f (RecClosure(f, paramIds, e0', rho0', []))),
              ks)
           end

       (*  Operand evaluated and operator is a (potentially) recursive closure
       *  with more than one unfilled parameter.  Record the value for the
       *  parameter and return the closure corresponding to the rest of the
       *  parameters.
       *)
       | (V v1, KApp2 (RecClosure (f, x :: xs, e0', rho0', ps)) :: ks) =>
           (V (RecClosure(f, xs, e0', rho0', (x, v1) :: ps)), ks)

       (*  **********
       *   Tuples.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Tuple (e :: es), rho), ks) =>
           (C (e, rho), KTuple([], es, rho) :: ks)

       (*  Evaluated a component, have more to go.
       *)
       | (V v, KTuple (vs, e :: es, rho) :: ks) =>
           (C (e, rho), KTuple (v :: vs, es, rho) :: ks)

       (*  Evaluated last component.
       *)
       | (V v, KTuple (vs, [], _) :: ks) =>
           (V (Tuple (rev (v :: vs))), ks)

       (*  **********
       *   Lists.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.List [], rho), ks) =>
           (V (List []), ks)

       | (C(Ast.List (e :: es), rho), ks) =>
           (C (e, rho), KList ([], es, rho) :: ks)

       (*  Evaluated a component, have more to go.
       *)
       | (V v, KList (vs, e :: es, rho) :: ks) =>
           (C (e, rho), KList (v :: vs, es, rho) :: ks)

       (*  Evaluated last component.
       *)
       | (V v, KList (vs, [], _) :: ks) =>
           (V (List (rev (v :: vs))), ks)

       (*  **********
       *   Let expressions.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Let([], e), rho), ks) =>
           (C (e, rho), ks)

       | (C(Ast.Let(Ast.ValDec(x, e') :: ds, e), rho), ks) =>
           (C (e', rho), KLetVal(x, ds, e, rho) :: ks)

       | (C(Ast.Let(Ast.FunDec(f, xs, e') :: ds, e), rho), ks) =>
           (C (Ast.Let(ds, e), update rho f (RecClosure(f, xs, e', rho, []))), ks)

       | (C(Ast.Let(Ast.DoDec e' :: ds, e), rho), ks) =>
           (C (e', rho), KLetDo(ds, e, rho) :: ks)

       | (V v, KLetVal(x, ds, e, rho) :: ks) =>
           (C (Ast.Let(ds, e), update rho x v), ks)

       | (V Triv, KLetDo(ds, e, rho) :: ks) =>
           (C (Ast.Let(ds, e), rho), ks)


       (*  Closures that are values.
       *)
       | (C(Ast.IntNum n, rho), ks) => (V(Int n), ks)

       | (C(Ast.RealNum n, rho), ks) => (V(Real n), ks)

       | (C(Ast.Char c, rho), ks) => (V(Char c), ks)

       | (C(Ast.Str s, rho), ks) => (V(Str s), ks)

       | (C(Ast.Bool v, rho), ks) => (V(Bool v), ks)

       | (C(Ast.Triv, rho), ks) => (V Triv, ks)

       | (C(Ast.Lambda(x, e), rho), ks) => (V(Closure(x, e, rho)), ks)

       | (C(Ast.Ident x, rho), ks) =>
           (
           (V (get rho x), ks)
           handle NotFound _ => (V (Builtin x), ks)
           )

       | (C(Ast.Proj n, rho), ks) =>
           (V (Proj n), ks)

       | _ => raise LibBase.Impossible "trans1"

  end

  (*  iterate s = v, where s = s_0 -> s_1 -> ... -> s_k = (V v, []).
  *)
  fun iterate (s : state) : value =
    case trans1 s of
         (V v, []) => v
       | s' => iterate s'

  (*  **********
  *   Client-visible functions.
  *   **********
  *)

  (*  The driver is the only client program that uses evalExp and valueToString.
  *  In order for it to compile, the only constraint is that the range of
  *  evalExp be the same as the domain of valueToString.
  *)

  (*  valueToString v = a string representation of v.
  *
  *  Pre-condition:  v must be a ground value (built up from base types with
  *  products and lists).
  *
  *  You will need to add to this function in order to return a string
  *  representation of reference values.  The string representation of a
  *  reference to v must be exactly "ref X", where X is the string
  *  representation of v; this is exactly what the SML/NJ interpreter does.
  *)
  fun valueToString (v : value) : string =
    case v of
         Int n => Int.toString n
       | Real x => Real.toString x
       | Char c => "#\"" ^ Char.toString c ^ "\""
       | Str s => "\"" ^ String.toString s ^ "\""
       | Bool b => Bool.toString b
       | Triv => "()"
       | Tuple vs => 
           ListFormat.fmt {init="(", final=")", sep=",", fmt=valueToString} vs
       | List vs =>
           ListFormat.listToString valueToString vs
       | Proj n => "#" ^ (Int.toString n)
       | Builtin id => id
       | _ => raise LibBase.Unimplemented "CEKInterp.valueToString"

  (*  evalExp e = iterate (C(e, Env.empty), []).
  *)
  fun evalExp (e : Ast.exp) : value =
    iterate (C(e, Env.empty), [])

  (*  execPgm p = ().
  *
  *  Effect:  the program p is executed under the empty environment.  Each
  *  statement in p is executed in order.  A value declaration is executed by
  *  evaluating its RHS and then adding the binding to the current environment.
  *  A function declaration is executed by adding the function binding to the
  *  current environment as an unapplied RecClosure.  An expression statement is
  *  executed by evaluating the expression to a value v, then printing a string
  *  representation of v to the terminal using dbg_valueToString.
  *)
  fun execPgm (Ast.Program ss : Ast.pgm) : unit =
  let
    fun execDec (rho : value env) (d : Ast.dec) : value env =
      case d of
           Ast.FunDec(f, xs, e) =>
             update rho f (RecClosure(f, xs, e, rho, []))
         | _ =>
           LibBase.failure {
             module="CEKInterp",
             func="execPgm.execDec",
             msg="Invalid program:  top-level val or do declaration."
           }

    fun execDecs (rho : value env) (ss : Ast.stm list) : value env =
      case ss of
           [] => rho
         | Ast.Dec d :: ss =>
           let
             val rho' = execDec rho d
           in
             execDecs rho' ss
           end
         | _ =>
           LibBase.failure {
             module="CEKInterp",
             func="execPgm.execStms",
             msg="Invalid program:  top-level expression statement."
           }

    val entry = Ast.App(Ast.Ident "main", Ast.Triv)

    val rho = execDecs Env.empty ss

    val _ = iterate (C(entry, rho), [])
  in
    ()
  end




end
