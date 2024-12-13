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
 * Partner: <None>
 * Collaborators: <None>
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


def hasloctype(env: Map[String, MTyp], e: Expr): Option[Typ] = e match {
// LocTypeVar: Check for mutable variables
case Var(x) =>
  env.get(x) match {
    case Some(MTyp(MVar | MRef, t)) => Some(t)
    case _ => None
  }


// LocTypeGetField: Check for object field access
case GetField(e1, f) =>
  hasloctype(env, e1) match {
    case Some(TObj(fields)) => fields.get(f)
    case _ => None
  }


// Otherwise, not a location
case _ => None
}


 def hasmodetype(env: Map[String, MTyp], e: Expr, d: Mode): Option[Typ] = d match {
     case MConst | MVar => Some(hastype(env, e))
     case MRef => hasloctype(env, e)
   }


def hastype(env: Map[String, MTyp], e: Expr): Typ = {
  def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)


  e match {
    // Base cases for literals
    case N(_) => TNumber
    case B(_) => TBool
    case Undefined => TUndefined
    case S(_) => TString


    // Variables
    case Var(x) =>
      env.get(x) match {
        case Some(MTyp(_, t)) => t
        case None => throw UnboundVariableError(Var(x))
      }


    // Unary operators
    case Unary(Neg, e1) =>
      if (hastype(env, e1) == TNumber) TNumber
      else err(hastype(env, e1), e1)

    case Unary(Not, e1) =>
      if (hastype(env, e1) == TBool) TBool
      else err(hastype(env, e1), e1)


    // Binary operators
    case Binary(Plus, e1, e2) =>
      (hastype(env, e1), hastype(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case (t1, _) => err(t1, e1)
      }

    case Binary(Minus | Times | Div, e1, e2) =>
      if (hastype(env, e1) == TNumber && hastype(env, e2) == TNumber) TNumber
      else err(TNumber, e1)

    case Binary(Eq | Ne, e1, e2) =>
      if (hastype(env, e1) == hastype(env, e2)) TBool
      else err(TBool, e1)

    case Binary(Lt | Le | Gt | Ge, e1, e2) =>
      if (hastype(env, e1) == TNumber && hastype(env, e2) == TNumber) TBool
      else err(TNumber, e1)

    case Binary(And | Or, e1, e2) =>
      if (hastype(env, e1) == TBool && hastype(env, e2) == TBool) TBool
      else err(TBool, e1)

    case Binary(Seq, e1, e2) =>
      hastype(env, e1); hastype(env, e2)


    // If-then-else
    case If(e1, e2, e3) =>
      if (hastype(env, e1) != TBool) err(TBool, e1)
      val t2 = hastype(env, e2)
      val t3 = hastype(env, e3)
      if (t2 == t3) t2 else err(t2, e2)


    // Declarations
    case Decl(MConst, x, e1, e2) =>
      val t1 = hastype(env, e1)
      hastype(env + (x -> MTyp(MConst, t1)), e2)

    case Decl(MVar, x, e1, e2) =>
      val t1 = hastype(env, e1)
      hastype(env + (x -> MTyp(MVar, t1)), e2)

    case Decl(MRef, x, e1, e2) =>
      hasloctype(env, e1) match {
        case Some(t1) => hastype(env + (x -> MTyp(MRef, t1)), e2)
        case None => err(TUndefined, e1)
      }


  // Assignments
    case Assign(e1, e2) =>
      hasloctype(env, e1) match {
        case Some(t1) if t1 == hastype(env, e2) => t1
        case Some(t1) => err(t1, e2)
        case None => err(TUndefined, e1)
      }


    // Objects
    case Obj(fields) =>
      val tfields = fields.map { case (f, e1) => f -> hastype(env, e1) }
      TObj(SortedMap(tfields.toSeq: _*))

    case GetField(e1, f) =>
      hastype(env, e1) match {
        case TObj(fields) => fields.getOrElse(f, throw StaticTypeError(TUndefined, e1, e))
        case tgot => err(tgot, e1)
      }


    // Functions and calls
    case Fun(p, params, tret, e1) =>
      val paramTypes = params.map { case (x, MTyp(m, t)) => x -> MTyp(m, t) }
      val env1 = env ++ paramTypes
      val env2 = p match {
        case Some(f) => env1 + (f -> MTyp(MConst, TFun(params, tret.getOrElse(TUndefined))))
        case None => env1
      }
      val t1 = hastype(env2, e1)
      tret match {
        case Some(tr) if t1 == tr => TFun(params, tr)
        case Some(tr) => err(tr, e1)
        case None => TFun(params, t1)
      }

    case Call(e1, args) =>
      hastype(env, e1) match {
        case TFun(params, tret) if params.length == args.length =>
          params.zip(args).foreach {
            case ((_, MTyp(_, t)), arg) =>
              if (hastype(env, arg) != t) err(t, arg)
          }
          tret
        case tgot => err(tgot, e1)
      }

    // Error for unsupported cases
    case _ => throw StuckError(e)
    }
  }


/*** Small-Step Interpreter ***/

/* Scope-respecting substitution replacing variables `x` with `with_e` in `e`.
   Assume that the free variables of `with_e` and `e` have an empty intersection
  (to avoid free-variable capture). */
def substitute(with_e: Expr, x: String, e: Expr): Expr = {

  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), s"stepping on a value: $e")
    e match {
      case N(_) | B(_) | S(_) | Undefined => doreturn(e)

      // Base Cases
      case Print(v1) if isValue(v1) =>
        doget map { m => println(pretty(m, v1)); Undefined }

      case Unary(Neg, N(n)) => doreturn(N(-n))

      case Binary(Plus, N(n1), N(n2)) => doreturn(N(n1 + n2))
      case Binary(Minus, N(n1), N(n2)) => doreturn(N(n1 - n2))
      case Binary(Times, N(n1), N(n2)) => doreturn(N(n1 * n2))
      case Binary(Div, N(n1), N(n2)) => doreturn(N(n1 / n2))

      case Binary(Plus, S(str1), S(str2)) => doreturn(S(str1 + str2))

      case Binary(Lt, N(n1), N(n2)) => doreturn(B(n1 < n2))
      case Binary(Le, N(n1), N(n2)) => doreturn(B(n1 <= n2))
      case Binary(Gt, N(n1), N(n2)) => doreturn(B(n1 > n2))
      case Binary(Ge, N(n1), N(n2)) => doreturn(B(n1 >= n2))

      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => doreturn(B(v1 == v2))
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => doreturn(B(v1 != v2))

      case Unary(Not, B(b1)) => doreturn(B(!b1))

      case Binary(And, B(true), e2) => doreturn(e2)
      case Binary(And, B(false), _) => doreturn(B(false))
      case Binary(Or, B(true), _) => doreturn(B(true))
      case Binary(Or, B(false), e2) => doreturn(e2)

      case If(B(true), e2, _) => doreturn(e2)
      case If(B(false), _, e3) => doreturn(e3)

      case Binary(Seq, v1, e2) if isValue(v1) => doreturn(e2)
      case Binary(Seq, e1, e2) if !isValue(e1) =>
        step(e1) map { e1p => Binary(Seq, e1p, e2) }

      case Decl(MConst, x, v1, e2) if isValue(v1) =>
        doreturn(substitute(v1, x, e2))

      case Decl(MVar, x, v1, e2) if isValue(v1) =>
        memalloc(v1) map { a =>
          substitute(Unary(Deref, a), x, e2)
        }

      case Decl(MRef, x, a @ A(_), e2) =>
        doreturn(substitute(Unary(Deref, a), x, e2))

      case Obj(fields) if fields.forall { case (_, v) => isValue(v) } =>
        memalloc(Obj(fields)) map { addr => A(addr.a) }

      case GetField(a @ A(_), f) =>
        doget map { m =>
          m(a) match {
            case Obj(fields) => fields.getOrElse(f, throw StuckError(e))
            case _ => throw StuckError(e)
          }
        }

      case Unary(Deref, a @ A(_)) =>
        doget map { m =>
          m.getOrElse(a, throw StuckError(e))
        }

      case Assign(Unary(Deref, a @ A(_)), e2) if !isValue(e2) =>
        step(e2) map { e2p => Assign(Unary(Deref, a), e2p) }

      case Assign(Unary(Deref, a @ A(_)), v2) if isValue(v2) =>
        domodify[Mem] { m => m + (a -> v2) } map { _ => v2 }

      case Assign(GetField(a @ A(_), f), v2) if isValue(v2) =>
        domodify[Mem] { m =>
          m + (a -> (m(a) match {
            case Obj(fields) => Obj(fields + (f -> v2))
            case _ => throw StuckError(e)
          }))
        } map { _ => v2 }

      case Assign(GetField(a @ A(_), f), e2) if !isValue(e2) =>
        step(e2) map { e2p => Assign(GetField(a, f), e2p) }

      case Assign(e1, e2) if !isLValue(e1) =>
        step(e1) map { e1p => Assign(e1p, e2) }

      case Assign(e1, e2) if !isValue(e2) =>
        step(e2) map { e2p => Assign(e1, e2p) }

      // Multi-parameter Procedures
      case Call(Fun(None, params, _, e1), args) if params.length == args.length && args.forall(isValue) =>
        val boundExpr = params.zip(args).foldRight(e1) {
          case (((y, MTyp(MConst, _)), v), acc) => substitute(v, y, acc)
          case (((y, MTyp(MVar, _)), v), acc) => substitute(Unary(Deref, v), y, acc)
          case (((y, MTyp(MRef, _)), a @ A(_)), acc) => substitute(Unary(Deref, a), y, acc)
        }
        doreturn(boundExpr)

      case Call(Fun(Some(f), params, _, e1), args) if params.length == args.length && args.forall(isValue) =>
        val boundExpr = params.zip(args).foldRight(e1) {
          case (((y, MTyp(MConst, _)), v), acc) => substitute(v, y, acc)
          case (((y, MTyp(MVar, _)), v), acc) => substitute(Unary(Deref, v), y, acc)
          case (((y, MTyp(MRef, _)), a @ A(_)), acc) => substitute(Unary(Deref, a), y, acc)
        }
        doreturn(substitute(Fun(Some(f), params, None, e1), f, boundExpr))

      case Call(e1, args) if !isValue(e1) =>
        step(e1) map { e1p => Call(e1p, args) }

      case Call(v1, args) =>
        mapFirstWith(args) {
          case arg if !isValue(arg) => Some(step(arg))
          case _ => None
        } map { argsp => Call(v1, argsp) }

      case Obj(fields) =>
        mapFirstWith(fields.toList) {
          case (f, v) if !isValue(v) => Some(step(v) map { vp => (f, vp) })
          case _ => None
        } map { fieldsp => Obj(SortedMap(fieldsp: _*)) }

      case GetField(e1, f) =>
        step(e1) map { e1p => GetField(e1p, f) }

      // Error Case
      case _ => throw StuckError(e)
    }
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
}
