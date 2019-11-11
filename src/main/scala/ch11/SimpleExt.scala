package ch11

object SimpleExt {
  sealed trait Info

  case object Info0 extends Info

  sealed trait ExternalTerm

  final case class TmSeq(info: Info, t1: Term, t2: Term) extends ExternalTerm

  sealed trait Term extends ExternalTerm

  final case class TmVar(info: Info, index: Int, contextLength: Int) extends Term

  final case class TmAbs(info: Info, v: String, ty: Type, t: Term) extends Term

  final case class TmApp(info: Info, t1: Term, t2: Term) extends Term

  final case class TmTrue(info: Info) extends Term

  final case class TmFalse(info: Info) extends Term

  final case class TmIf(info: Info, t1: Term, t2: Term, t3: Term) extends Term

  final case class TmUnit(info: Info) extends Term

  final case class TmProduct(info: Info, t1: Term, t2: Term) extends Term

  final case class TmFirst(info: Info, t: Term) extends Term

  final case class TmSecond(info: Info, t: Term) extends Term

  final case class TmInl(info: Info, t1: Term, ty2: Type) extends Term

  final case class TmInr(info: Info, ty1: Type, t2: Term) extends Term

  final case class TmCase(info: Info, t: Term, xl: String, tl: Term, xr: String, tr: Term) extends Term

  sealed trait Type

  final case class TyArr(ty1: Type, ty2: Type) extends Type

  case object TyBool extends Type

  case object TyUnit extends Type

  case class TyProduct(tyT1: Type, tyT2: Type) extends Type

  case class TySum(tyT1: Type, tyT2: Type) extends Type

  sealed trait Binding

  case object NameBind extends Binding

  final case class VarBind(ty: Type) extends Binding

  final case class NoRuleAppliesException(term: Term) extends RuntimeException

  case class Context(l: List[(String, Binding)]) {
    def pickFreshName(s: String): (Context, String) =
      if (isNameBound(s)) pickFreshName(s + "'")
      else (Context((s, NameBind) :: l), s)

    def index2Name(i: Int): String = get(i)._1

    def getBinding(i: Int): Binding = get(i)._2

    def addBinding(x: String, bind: Binding): Context = Context((x, bind) :: l)

    def getTypeFromContext(fi: Info, i: Int): Type = getBinding(i) match {
      case VarBind(tyT: Type) => tyT
      case _                  => error(fi, s"Wrong kind of binding for variable ${index2Name(i)}")
    }

    def isNameBound(x: String): Boolean = l.exists(_._1 == x)

    @throws
    private def get(i: Int): (String, Binding) = l(i)

    private def error(fi: Info, msg: String): Nothing = {
      println(msg)
      sys.exit(1) // Scala の sys.exit() は Nothing を返すので任意の型として扱える！
    }
  }
  object Context {
    def apply(): Context = Context(List.empty)
  }

  def applyAll(t: Term, f: Term => Term): Term = {
    t match {
      case TmVar(fi, x, n)       => TmVar(fi, x, n)
      case TmAbs(fi, x, ty, t1)  => TmAbs(fi, x, ty, f(t1))
      case TmApp(fi, t1, t2)     => TmApp(fi, f(t1), f(t2))
      case TmTrue(_)             => t
      case TmFalse(_)            => t
      case TmIf(fi, t1, t2, t3)  => TmIf(fi, f(t1), f(t2), f(t3))
      case TmUnit(_)             => t
      case TmProduct(fi, t1, t2) => TmProduct(fi, f(t1), f(t2))
      case TmFirst(fi, t1)        => TmFirst(fi, f(t1))
      case TmSecond(fi, t1)       => TmSecond(fi, f(t1))
      case TmInl(fi, t1, ty2) => TmInl(fi, f(t1), ty2)
      case TmInr(fi, ty1, t2) => TmInr(fi, ty1, f(t2))
      case TmCase(fi, t0, x1, t1, x2, t2) => TmCase(fi, f(t0), x1, f(t1), x2, f(t2))
    }
  }

  def termShift(d: Int, t: Term): Term = {
    def walk(c: Int, t: Term): Term = t match {
      case TmVar(fi, x, n) =>
        if (x >= c) TmVar(fi, x + d, n + d) else TmVar(fi, x, n + d)
      case TmAbs(fi, x, ty, t1) => TmAbs(fi, x, ty, walk(c + 1, t1))
      case t                    => applyAll(t, walk(c, _))
    }
    walk(0, t)
  }

  def termSubst(j: Int, s: Term, t: Term): Term = {
    def walk(c: Int, t: Term): Term = {
      t match {
        case TmVar(fi, x, n) =>
          if (x == j + c) termShift(c, s) else TmVar(fi, x, n)
        case TmAbs(fi, x, ty, t1) => TmAbs(fi, x, ty, walk(c + 1, t1))
        case _                    => applyAll(t, walk(c, _))
      }
    }
    walk(0, t)
  }

  def termSubstTop(s: Term, t: Term): Term =
    termShift(-1, termSubst(0, termShift(1, s), t))

  def isVal(ctx: Context, t: Term): Boolean = t match {
    case TmAbs(_, _, _, _)                                        => true
    case TmTrue(_)                                                => true
    case TmFalse(_)                                               => true
    case TmUnit(_)                                                => true
    case TmProduct(_, v1, v2) if isVal(ctx, v1) && isVal(ctx, v2) => true
    case TmInl(_, v1, _) if isVal(ctx, v1)                        => true
    case TmInr(_, _, v2) if isVal(ctx, v2)                        => true
    case _                                                        => false
  }

  def eval1(info: Info, ctx: Context, t: Term): Option[Term] = t match {
    case TmApp(_, TmAbs(_, _, _, t12), v2) if isVal(ctx, v2) =>
      Some(termSubstTop(v2, t12))
    case TmApp(fi, v1, t2) if isVal(ctx, v1) => for {
      t2prime <- eval1(fi, ctx, t2)
    } yield TmApp(fi, v1, t2prime)
    case TmApp(fi, t1, t2) => for {
      t1prime <- eval1(fi, ctx, t1)
    } yield TmApp(fi, t1prime, t2)
    case TmIf(_, TmTrue(_), t1, _)  => Some(t1)
    case TmIf(_, TmFalse(_), _, t2) => Some(t2)
    case TmIf(fi, t1, t2, t3)       => for {
      t1prime <- eval1(info, ctx, t1)
    } yield TmIf(fi, t1prime, t2, t3)
    case TmFirst(_, TmProduct(_, v1, v2)) if isVal(ctx, v1) && isVal(ctx, v2) =>
      Some(v1)
    case TmSecond(_, TmProduct(_, v1, v2))
        if isVal(ctx, v1) && isVal(ctx, v2) =>
      Some(v2)
    case TmFirst(fi, t1)       => for {
      t1prime <- eval1(fi, ctx, t1)
    } yield TmFirst(fi, t1prime)
    case TmSecond(fi, t1)      => for {
      t1prime <- eval1(fi, ctx, t1)
    } yield TmFirst(fi, t1prime)
    case TmProduct(fi, t1, t2) => for {
      t1prime <- eval1(fi, ctx, t1)
    } yield TmProduct(fi, t1prime, t2)
    case TmProduct(fi, v1, t2) if isVal(ctx, v1) => for {
      t2prime <- eval1(fi, ctx, t2)
    } yield TmProduct(fi, v1, t2prime)
    case TmCase(_, TmInl(_, v0, _), _, t1, _, _) if isVal(ctx, v0) => Some(termSubstTop(v0, t1))
    case TmCase(_, TmInr(_, _, v0), _, _, _, t2) if isVal(ctx, v0) => Some(termSubstTop(v0, t2))
    case TmCase(fi, t0, x1, t1, x2, t2) => for {
      t0prime <-eval1(info, ctx, t0)
    } yield TmCase(fi, t0prime, x1, t1, x2, t2)
    case TmInl(fi, t1, ty2) => for {
      t1prime <- eval1(info, ctx, t1)
    } yield TmInl(fi, t1prime, ty2)
    case TmInr(fi, ty1, t2) => for {
      t2prime <- eval1(info, ctx, t2)
    } yield TmInr(fi, ty1, t2prime)
    case _ => None
  }

  def eval(info: Info, ctx: Context, t: Term): Term =
    eval1(info, ctx, t) match {
      case Some(tPrime) => eval(info, ctx, tPrime)
      case None => t
    }

  def typeOf(ctx: Context, t: Term): Option[Type] = t match {
    case TmVar(fi, i, _) => Some(ctx.getTypeFromContext(fi, i))
    case TmAbs(_, x, tyT1, t2) =>
      val ctx_ = ctx.addBinding(x, VarBind(tyT1))
      for {
        tyT2 <- typeOf(ctx_, t2)
      } yield TyArr(tyT1, tyT2)
    case TmApp(_, t1, t2) =>
      for {
        tyT1 <- typeOf(ctx, t1)
        tyT2 <- typeOf(ctx, t2)
        res <- tyT1 match {
          case TyArr(tyT11, tyT12) if tyT2 == tyT11 => Some(tyT12)
          case TyArr(_, _)                          => None
          case _                                    => None
        }
      } yield res
    case TmTrue(_)  => Some(TyBool)
    case TmFalse(_) => Some(TyBool)
    case TmIf(_, t1, t2, t3) if typeOf(ctx, t1).contains(TyBool) =>
      if (typeOf(ctx, t2) == typeOf(ctx, t3)) typeOf(ctx, t2)
      else None
    case TmIf(_, _, _, _) => None
    case TmUnit(_)         => Some(TyUnit)
    case TmProduct(_, t1, t2) =>
      for {
        tyT1 <- typeOf(ctx, t1)
        tyT2 <- typeOf(ctx, t2)
      } yield TyProduct(tyT1, tyT2)
    case TmFirst(fi, t1) =>
      for {
        tyT1 <- typeOf(ctx, t1)
        tyT11 <- tyT1 match {
          case TyProduct(ty11, _) => Some(ty11)
          case _                  => None
        }
      } yield tyT11
    case TmSecond(_, t1) =>
      for {
        tyT1 <- typeOf(ctx, t1)
        tyT12 <- tyT1 match {
          case TyProduct(_, ty12) => Some(ty12)
          case _                  => None
        }
      } yield tyT12
    case TmInl(_, t1, tyT2) => for {
      tyT1 <- typeOf(ctx, t1)
    } yield TySum(tyT1, tyT2)
    case TmInr(_, tyT1, t2) => for {
      tyT2 <- typeOf(ctx, t2)
    } yield TySum(tyT1, tyT2)
    case TmCase(_, t0, x1, t1, x2, t2) =>
      typeOf(ctx, t0) match {
        case Some(TySum(ty1, ty2)) => for {
          tyT <-typeOf(ctx.addBinding(x1, VarBind(ty1)), t1)
          tyTPrime <- typeOf(ctx.addBinding(x2, VarBind(ty2)), t2)
          res <- if(tyT == tyTPrime) Some(tyT) else None
        } yield res
        case _ => None
      }
  }

  def refine(t: ExternalTerm): Term = {
    t match {
      case TmSeq(fi, t1, t2) => TmApp(fi, TmAbs(fi, "x", TyUnit, refine(t1)), refine(t2))
      case t1: Term => t1
    }
  }

  def externalEval(info: Info, ctx: Context, externalTerm: ExternalTerm): Term = {
    eval(info, ctx, refine(externalTerm))
  }

  def externalTypeOf(ctx: Context, externalTerm: ExternalTerm): Option[Type] = {
    typeOf(ctx, refine(externalTerm))
  }
}
