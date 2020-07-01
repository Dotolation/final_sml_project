(*  COMP 323 Project 5:  Compilation
*
*  N. Danner
*  Spring 2019
*)

structure Compile =
struct

  (*  **********
  *   Debugging and printing.
  *   **********
  *)

  val debug = false ;

  fun dbg_print (s : string) : unit =
    if debug then print s else ()

  fun dbg_printnl (s : string) : unit =
    dbg_print (s ^ "\n")

  fun printnl (s : string) : unit =
    print(s ^ "\n")


  (*  **********
  *   Map with domain Ast.ident.
  *   **********
  *)

  structure IdentMap = SplayMapFn(
    struct
      type ord_key = Ast.ident
      val compare = String.compare
    end)

  (*  **********
  *   Compiler environment.
  *   **********
  *)

  structure Env = struct

    type env = {
      rho : int IdentMap.map,
      nextLoc : int,
      nextLbl : int ref
    }

    exception NotFound of string

    (*  empty = an empty environment.
    *)
    fun empty() : env =
      {
        rho=IdentMap.empty,
        nextLoc=0,
        nextLbl=ref 0
      }

    (*  empty1 = an empty environment with the next location set to 1.
    *
    *  This is a hack for main.
    *)
    fun empty1() : env =
      {
        rho=IdentMap.empty,
        nextLoc=1,
        nextLbl=ref 0
      }

  end

  exception Blergh of string
  (*Helper functions*)
  (*Very specific function that *)
  extract_funtype (t: Type.typ): string =
     case t of
        IntTy => "I"
      | RealTy => "D"
      | BoolTy => "Z"
      | UnitTy => "V"
      | ArrowTy (t0, t1) => extract_funtype t1
      | _ => raise Belrgh of "Weird Type."

  (*  **********
  *   Client-visible functions.
  *   **********
  *)

  (*  compile (ss, outs) = ()
  *
  *  Side-effect:  ss is compiled to outs.
  *
  *  All auxiliary functions are local to compile, so that they can all treat
  *  outs as a global variable.
  *)
  fun compile (Type.Program ss : Type.pgm, outs : TextIO.outstream) : unit =
  let

    (* **********
    *  Emission functions.
    *  **********
    *)

    (*  emit s emits s ^ "\n" to outs.
    *)
    fun emit (s : string) : unit =
      TextIO.output(outs, s ^ "\n") before TextIO.flushOut(outs)

    (*  emitClassHeader() emits the standard class header to outs.
    *)
    fun emitClassHeader() : unit =
    let
      val hdr = String.concatWith "\n" [
        ".class public C",
        ".super java/lang/Object",
        "",
        ".method public <init>()V",
        "  aload_0",
        "  invokenonvirtual java/lang/Object/<init>()V",
        "  return",
        ".end method",
        ""
      ]
    in
      emit hdr
    end

    (* **********
    *  Auxiliary compilation functions.
    *  **********
    *)

    (*  compileBinOp eta e0 e1 opInstr = eta', where eta' is the result of
    *  updating eta after compiling e0 and e1.
    *
    *  Side-effect:  compiles e0 and e1 and then applies opInstr.
    *)
    fun compileBinOp
        (eta : Env.env)
        (e0 : Type.ann_exp)
        (e1 : Type.ann_exp)
        (opInstr : string) : Env.env =
    let
      val eta = compileExp eta e0
      val eta = compileExp eta e1
      val () = emit opInstr
    in
      eta
    end

    (*  compileExp eta e' = eta', where eta' is the result of updating eta after
    *  compiling e.
    *
    *  Side-effect:  code generated to transform <S, Σ> -> <S.v, Σ'>, where e'
    *  evaluates to v.
    *)
    and compileExp
        (eta : Env.env)
        (e' as Type.AnnExp(e, tau) : Type.ann_exp) : Env.env =
    let
      val () = dbg_printnl ("compileExp " ^ Type.annExpToString e')
    in
      case (e, tau) of
           (Type.IntNum n, _) => eta before emit ("ldc " ^ (Int.toString n))
         | (Type.RealNum x, _) =>
             eta before emit ("ldc2_w " ^ (Real.toString x))
         | (Type.Bool true, _) => eta before emit "ldc 1"
         | (Type.Bool false, _) => eta before emit "ldc 0"
         | (Type.Triv, _) => eta before emit "nop"

         | (Type.Plus(e0, e1), Type.IntTy) => compileBinOp eta e0 e1 "iadd"
         | (Type.Plus(e0, e1), Type.RealTy) => compileBinOp eta e0 e1 "dadd"

         | (Type.Minus(e0, e1), Type.IntTy) => compileBinOp eta e0 e1 "isub"
         | (Type.Minus(e0, e1), Type.RealTy) => compileBinOp eta e0 e1 "dsub"

         | (Type.Times(e0, e1), Type.IntTy) => compileBinOp eta e0 e1 "imul"
         | (Type.Times(e0, e1), Type.RealTy) => compileBinOp eta e0 e1 "dmul"

         | (Type.Div(e0, e1), Type.IntTy) => compileBinOp eta e0 e1 "idiv"
         | (Type.Div(e0, e1), Type.RealTy) => compileBinOp eta e0 e1 "ddiv"

         | (Type.Mod(e0, e1), Type.IntTy) => compileBinOp eta e0 e1 "irem"

         | (Type.App _, _) =>
           let
             (* Get the function identifier and arguments; remember, this is a
             * complete application.
             *
             * But for this sample code, we know that the only functions are the
             * built-in functions printInt, printReal, printBool, so we can
             * simplify this implementation, because we know that an App
             * expression must be App(Ident f, e), where f is one of the print
             * functions.
             *)
             val Type.App(Type.AnnExp(Type.Ident f, _), e') = e

             (* Evaluate argument.
             *)
             val eta' = compileExp eta e'

             (* Call f.
             *)
             val () =
               case f of
                    "printInt" => emit "invokestatic CSupport/printInt(I)V"
                  | "printReal" => emit "invokestatic CSupport/printDouble(D)V"
                  | "printBool" => emit "invokestatic CSupport/printBool(Z)V"
           in
             eta'
           end
         | (Type.Let(ds, e'), _) =>
           let
             val eta = compileDecs eta ds
           in
             compileExp eta e'
           end
         | _ =>
             LibBase.failure {
               module="Compile",
               func="compileExp",
               msg=String.concat [
                 "Unimplemented case: ",
                 Type.annExpToString e'
               ]
             }
    end

    and compileDecs
        (eta : Env.env)
        (ds : Type.dec list) : Env.env =
      case ds of
           [] => eta

         | Type.DoDec e :: ds =>
           let
             val eta' = compileExp eta e
           in
             compileDecs eta' ds
           end

         | Type.FunDec("main", _, _, e) :: ds =>
           let
             val () = emit ".method public static main([Ljava/lang/String;)V"
             val () = emit ".limit locals 1000"
             val () = emit ".limit stack 1000"

             (*  Reserve Σ(0) for string array argument.
             *)
             val eta' = Env.empty1()

             val eta'' = compileExp eta' e

             val () = emit "return"

             val () = emit ".end method"
           in
             compileDecs eta'' ds
           end

         |Type.FunDec(name, ty, args, e) :: ds =>
           let
             val javastuff = ".method public static"
             val arg_types = map (fn (x,y) => Type.typeToString y) args
             val fun_type = Type.typeToString (extract_funtype ty)
             val details = name^"("^arg_types^")"^fun_type
             val () = emit (javastuff^name_n_type)
             val () = emit ".limit locals 1000"
             val () = emit ".limit stack 1000"
             val eta' = compileExp eta e
             val () = case fun_type of
                        "I" => emit "ireturn"
                       |"D" => emit "dreturn"
                       |"Z" => emit "ireturn"
                       |"V" => emit "return"
             val () = emit ".end method"
          in
             compileDecs eta' ds
          end

         | d :: _ =>
             LibBase.failure {
               module="Compile",
               func="compile.compileDecs",
               msg="Unimplemented declaration form: " ^ Type.declToString d
             }



    (* **********
    *  Do the actual compiling.
    *  **********
    *)

    (*  Convert the statement list to a declaration list for convenience.  This
    *  has to be OK, because a program is a sequence of declarations.
    *)
    val ds = map (fn (Type.Dec d) => d) ss
             handle Match =>
             LibBase.failure {
               module="Compile",
               func="compile",
               msg="Invalid program format:  non-declaration at top level"
             }

    (*  Get initial compile environment.
    *)
    val rho : Env.env = Env.empty()

    (*  Emit the class header.
    *)
    val () = emitClassHeader()

    (*  Compile the function declarations.
    *)
    val _ = compileDecs rho ds
  in
    ()
  end

end
