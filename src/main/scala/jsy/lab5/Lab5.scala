package jsy.lab5

import scala.collection.immutable.SortedMap
import jsy.lab5.Parser.parse

object Lab5 extends jsy.util.JsyApplication {
  import jsy.lab5.ast._
  import jsy.util.DoWith
  import jsy.util.DoWith._

  /*
   * CSCI 3155: Lab 5
   * David Benson
   *
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  /*** Type Inference ***/

  def hasloctype(env: Map[String, MTyp], e: Expr): Option[Typ] = 
    try { Some(hastype(env, e)) }
    catch { case _: StaticTypeError => None }


  def hasmodetype(env: Map[String, MTyp], e: Expr, d: Mode): Option[Typ] = 
    try {
      val typ = hastype(env, e)
      d match {
        case MConst => Some(typ)
        case MVar if typ != TUndefined => Some(typ)
        case MRef if typ != TUndefined => Some(typ)
        case _ => None
      }
    } catch {
      case e: StaticTypeError => None
    }


  def hastype(env: Map[String, MTyp], e: Expr): Typ = {
    /* Shortcuts for StaticTypeError. Use `err` when you can infer a type for e1 and `errnotype` when you cannot. */
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)
    def errnotype[T](e1: Expr): T = err(TUndefined, e1)

    e match {
      case Print(e1) => hastype(env, e1); TUndefined
        /***** Cases directly from before. We will minimize the test of these cases in Lab 5. */
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => env.get(x).map { case MTyp(_, typ) => typ }.getOrElse(errnotype(e))
      case Unary(Neg, e1) => hastype(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) =>
        hastype(env, e1) match {
          case TBool => TBool
          case tgot => err(tgot, e1)
        }
      case Binary(Plus, e1, e2) =>
        (hastype(env, e1), hastype(env, e2)) match {
          case (TNumber, TNumber) => TNumber
          case (TString, TString) => TString
          case (tgot1, _) => err(tgot1, e1)
        }
      case Binary(Minus|Times|Div, e1, e2) =>
        (hastype(env, e1), hastype(env, e2)) match {
          case (TNumber, TNumber) => TNumber
          case (tgot1, _) => err(tgot1, e1)
        }
      case Binary(Eq|Ne, e1, e2) =>
        (hastype(env, e1), hastype(env, e2)) match {
          case (t1, t2) if t1 == t2 => TBool
          case (tgot1, _) => err(tgot1, e1)
        }
      case Binary(Lt|Le|Gt|Ge, e1, e2) =>
        (hastype(env, e1), hastype(env, e2)) match {
          case (TNumber, TNumber) => TBool
          case (tgot1, _) => err(tgot1, e1)
        }
      case Binary(And|Or, e1, e2) =>
        (hastype(env, e1), hastype(env, e2)) match {
          case (TBool, TBool) => TBool
          case (tgot, _) => err(tgot, e1)
        }
      case Binary(Seq, e1, e2) =>
        hastype(env, e1)
        hastype(env, e2)
      
      case If(e1, e2, e3) =>
        hastype(env, e1) match {
          case (TBool) =>
            val t2 = hastype(env, e2)
            val t3 = hastype(env, e3)
            if (t2 == t3) t2
            else err(t2, e2)
          case tgot => err(tgot, e1)
        }

      case Obj(fields) => TObj(fields.map { case (f, e1) => (f, hastype(env, e1)) })
      case GetField(e1, f) => 
        hastype(env, e1) match {
          case TObj(fieldTypes) =>
            fieldTypes.getOrElse(f, err(TObj(fieldTypes), e1))
          case tgot => err(tgot, e1)
        }
      case Decl(m, x, e1, e2) =>
        val t1 = hastype(env, e1)
        val newEnv = env + (x -> MTyp(m, t1))
        hastype(newEnv, e2)


      case Fun(xopt, params, tretopt, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (xopt, tretopt) match {
          /***** Add cases here *****/
          case (Some(x), Some(tret)) =>
            env + (x -> MTyp(MConst, TFun(params, tret)))
          case (Some(x), None) => errnotype(e1)
          case (None, Some(tret)) => env
          case (None, None) => errnotype(e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = env1 ++ params.map { case (x, MTyp(m, t)) => x -> MTyp(m, t) }
        // Infer the type of the function body
        val t1 = hastype(env2, e1)
        // Check with the possibly annotated return type
        tretopt match {
          case Some(tret) if t1 == tret => TFun(params, tret)
          case Some(tret) => err(t1, e1)
          case None => TFun(params, t1)
        }
      }

      case Call(e1, args) => hastype(env, e1) match {
        case TFun(params, tret) if params.length == args.length =>
          (params zip args).foreach {
            case ((x, MTyp(_, paramType)), ex) =>
              val argType = hastype(env, ex)
              if (paramType != argType) err(paramType, ex) 
          }
          tret
        case tgot => err(tgot, e1)
      }

      case Assign(e1, e2) =>
        e1 match {

          case Var(x) =>
            env.get(x) match {
              case Some(MTyp(MConst, _)) =>
                errnotype(e1) 
              case Some(MTyp(MVar, t1)) =>
                val t2 = hastype(env, e2)
                if (t1 == t2) t2 
                else err(t1, e2) 
              case None =>
                errnotype(e1)
            }

          case Unary(Deref, a @ A(_)) =>
            val t1 = hastype(env, e1)
            val t2 = hastype(env, e2)
            if (t1 == t2) t2
            else err(t1, e2)

          case GetField(e1Inner, f) =>
            hastype(env, e1Inner) match {
              case TObj(fields) if fields.contains(f) =>
                val fieldType = fields(f)
                val t2 = hastype(env, e2)
                if (fieldType == t2) t2 
                else err(fieldType, e2)
              case tgot =>
                err(tgot, e1Inner) 
            }

          case _ =>
            errnotype(e1)
        }
        
      /* Should not match: non-source expressions */
      case A(_) | Unary(Deref, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }

  /*** Small-Step Interpreter ***/

  /* Scope-respecting substitution replacing variables `x` with `with_e` in `e`.
     Assume that the free variables of `with_e` and `e` have an empty intersection
    (to avoid free-variable capture). */
  def substitute(with_e: Expr, x: String, e: Expr): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e

      case Print(e1) => Print(subst(e1))

      case Unary(uop, e1) => Unary(uop, subst(e1))

      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))

      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))

      case Var(y) => if (y == x) with_e else e

      case Decl(d, y, e1, e2) => 
        if (y == x) Decl(d, y, subst(e1), e2) 
        else Decl(d, y, subst(e1), subst(e2))

      case Fun(xopt, params, tann, e1) =>
        if (xopt.contains(x) || params.exists(_._1 == x)) e
        else Fun(xopt, params, tann, subst(e1))

      case Call(e1, args) => Call(subst(e1), args.map(subst))

      case Obj(fields) => Obj(fields.map { case (f, e1) => (f, subst(e1)) })

      case GetField(e1, f) => GetField(subst(e1), f)

      case A(_) => e

      case Assign(e1, e2) => Assign(subst(e1), subst(e2))
    }
    subst(e)
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), s"stepping on a value: ${e}")
    e match {
      /* Base Cases */
      case Print(v1) if isValue(v1) => doget map { m => println(pretty(m, v1)); Undefined }
      case Unary(Neg, v1) if isValue(v1) => 
        v1 match {
          case N(n) => doreturn(N(-n))
          case _ => throw StuckError(e) 
        }
      case Unary(Not, v1) if isValue(v1) => v1 match {
        case B(n) => doreturn(B(!n))
        case _ => throw StuckError(e)
      }

      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) => memalloc(e)
      case GetField(a @ A(_), f) =>
        doget map { m => 
        m.get(a) match {
          case Some(Obj(fields)) => fields.getOrElse(f, throw StuckError(e))
          case _ => throw StuckError(e)
          }
        }
        

      case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) =>
        (v1, v2) match {
          case (N(n1), N(n2)) => doreturn(N(n1 + n2)) 
          case (S(s1), S(s2)) => doreturn(S(s1 + s2)) 
          case _ => throw StuckError(e) 
        }
      case Binary(Plus, e1, e2) if isValue(e1) => 
        step(e2) map { e2p => Binary(Plus, e1, e2p) }
      case Binary(Plus, e1, e2) =>
        step(e1) map { e1p => Binary(Plus, e1p, e2) }
       
      case Binary(Or,B(x),v2) => if (x) doreturn(B(true)) else doreturn(v2) 
      case Binary(Eq,v1,v2) if(isValue(v1) && isValue(v2)) => doreturn(B(v1 == v2)) 
      case Binary(Ne,v1,v2) if(isValue(v1) && isValue(v2)) => doreturn(B(v1 != v2)) 
      case Binary(Minus,N(x),N(y)) => doreturn(N(x - y)) 
      case Binary(Times,N(x),N(y)) => doreturn(N(x * y)) 
      case Binary(Div,N(x),N(y)) => doreturn(N(x / y)) 
      
      case If(B(true),v2,v3)  => doreturn(v2) 
      case If(B(false),v2,v3)  => doreturn(v3)

        /***** New cases. */
      case Decl(MConst, x, v1, e2) if isValue(v1) =>
        doreturn(substitute(v1,x,e2))

      case Decl(MVar, x, v1, e2) if isValue(v1) =>
        memalloc(v1) flatMap { a => doreturn(substitute(Unary(Deref, a), x, e2))}

      case Decl(MRef, x, l1, e2) if isValue(l1) => 
        doreturn(substitute(l1, x, e2))

      case Unary(Deref, a @ A(_)) =>
        doget[Mem] flatMap { m => doreturn(m(a))}
    
        
      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        domodify[Mem] { m => 
          if (m.contains(a)) { m + (a->v)} 
          else throw StuckError(e)
        } flatMap { _ => doreturn(v) }


      case Assign(GetField(a @ A(_), f), v) if isValue(v) =>
        domodify[Mem] { m =>
          m.get(a) match {
            case Some(Obj(fields)) =>
              val updatedFields = fields + (f -> v)
              m + (a -> Obj(updatedFields))
            case _ => throw StuckError(e)
          }
        } flatMap { _ => doreturn(v) }



      case Call(v @ Fun(xopt, params, _, e), args) => {
        val pazip = params zip args
        val ep = pazip.foldRight(e) {
          case (((x, MTyp(MConst, _)), arg), acc) =>
            substitute(arg, x, acc)

          case (((x, MTyp(MVar, _)), arg), acc) =>
            substitute(Unary(Deref, arg), x, acc)

          case (((x, MTyp(MRef, _)), arg), acc) =>
            substitute(arg, x, acc)
        }
        DoWith.doreturn(ep)
      }


      /* Inductive Cases */
      case Print(e1) => step(e1) map { e1p => Print(e1p) }
      case Unary(uop, e1) => step(e1) map { e1p => Unary(uop, e1p) }
        /***** More cases here */
      case GetField(e1, f) =>
        step(e1) map { e1p => GetField(e1p, f) }
      case Obj(fields) =>
        val (k, v) = fields.find { case (_, vi) => !isValue(vi) }.get
        step(v) map { vp => Obj(fields + (k -> vp)) }

      case Decl(d, x, e1, e2) =>
        step(e1) map { e1p => Decl(d, x, e1p, e2) }
      case Call(e1, args) =>
        step(e1) map { e1p => Call(e1p, args) }

        /***** New cases.  */
      case Assign(e1, e2) if !isValue(e1) =>
        step(e1) map { e1p => Assign(e1p, e2) }
      case Assign(e1, e2) if !isValue(e2) =>
        step(e2) map { e2p => Assign(e1, e2p) }

      case Assign(e1, e2) =>
        step(e1) map { v1 =>
          Assign(v1, e2)
        }

      /* Everything else is a stuck error. */
      case _ => throw StuckError(e)
    }
  }

  /*** External Interfaces ***/

  /** Interface to run your small-step interpreter
    * and print out the steps of evaluation if debugging. */
  def iterateStep(e: Expr): Expr = {
    require(closed(e), "input Expr to iterateStep is not closed: free variables: %s".format(freeVars(e)) )
    def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
      if (Some(n) == maxSteps) throw TerminationError(e, n)
      else if (isValue(e)) doreturn( e )
      else {
        doget[Mem] flatMap { m =>
          println("## step %4d:%n##  %s%n##  %s".format(n, m, e))
          step(e) flatMap { ep => loop(ep, n + 1) }
        }
      }
    val (m,v) = loop(e, 0)(memempty)
    println("## result:%n##  %s%n##  %s".format(m, v))
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(parse(s))

  /** Interface to run your type checker. */
  def inferType(e: Expr): Typ = {
    val t = hastype(Map.empty, e)
    println(s"## type ${e} : ${pretty(t)}")
    t
  }

  //this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

  // Interface for main
  def processFile(file: java.io.File): Unit = {
    if (debug) {
      println("# ============================================================")
      println("# File: " + file.getName)
      println("# Parsing ...")
    }

    val expr =
      handle(None: Option[Expr]) {Some{
        jsy.lab5.Parser.parseFile(file)
      }} getOrElse {
        return
      }

    if (debug) {
      println("# ------------------------------------------------------------")
      println("# Type checking %s ...".format(expr))
    }

    val welltyped = handle(false) {
      val t = inferType(expr)
      true
    }
    if (!welltyped) return

    if (debug) {
      println("# ------------------------------------------------------------")
      println("# Stepping %s ...".format(expr))
    }

    handle(()) {
      val v = iterateStep(expr)
      println(pretty(v))
    }
  }
}
