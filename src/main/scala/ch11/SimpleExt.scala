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

  /*
  ML 実装では Context 型のインスタンスが関数の引数に含まれているが，
  Context クラスの振る舞いとすることで省略する．
   */
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

    /*
    型検査．
    eval と似たことをしているが，異なる機構で行われる．
     */
    def typeOf(t: Term): Type = t match {
      case TmVar(fi, i, _) => getTypeFromContext(fi, i)
      case TmAbs(_, x, tyT1, t2) =>
        val ctx_ = addBinding(x, VarBind(tyT1))
        val tyT2 = ctx_.typeOf(t2)
        TyArr(tyT1, tyT2)
      case TmApp(fi, t1, t2) =>
        val tyT1 = typeOf(t1)
        val tyT2 = typeOf(t2)
        tyT1 match {
          case TyArr(tyT11, tyT12) if tyT2 == tyT11 => tyT12
          case TyArr(_, _)                          => error(fi, "parameter type mismatch")
          case _                                    => error(fi, "arrow type expected")
        }
      case TmTrue(_)  => TyBool
      case TmFalse(_) => TyBool
      case TmIf(fi, t1, t2, t3) if typeOf(t1) == TyBool =>
        if (typeOf(t2) == typeOf(t3)) typeOf(t2)
        else error(fi, "arms of conditional have different types")
      case TmIf(fi, _, _, _) => error(fi, "guard of conditional not a boolean")
      case TmUnit(_)         => TyUnit
      case TmProduct(_, t1, t2) =>
        val tyT1 = typeOf(t1)
        val tyT2 = typeOf(t2)
        TyProduct(tyT1, tyT2)
      case TmFirst(fi, t1) =>
        typeOf(t1) match {
          case TyProduct(ty11, _) => ty11
          case _                  => error(fi, "")
        }
      case TmSecond(fi, t1) =>
        typeOf(t1) match {
          case TyProduct(_, ty12) => ty12
          case _                  => error(fi, "")
        }
      case TmInl(_, t1, ty2) => TySum(typeOf(t1), ty2)
      case TmInr(_, ty1, t2) => TySum(ty1, typeOf(t2))
      case TmCase(fi, t0, x1, t1, x2, t2) =>
        typeOf(t0) match {
          case TySum(ty1, ty2) => {
            val tyT = addBinding(x1, VarBind(ty1)).typeOf(t1)
            val tyTPrime = addBinding(x2, VarBind(ty2)).typeOf(t2)
            if(tyT == tyTPrime) {
              tyT
            } else {
              error(fi, "")
            }
          }
          case _ => error(fi, "")
        }
    }

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

  def eval1(info: Info, ctx: Context, t: Term): Term = t match {
    case TmApp(_, TmAbs(_, _, _, t12), v2) if isVal(ctx, v2) =>
      termSubstTop(v2, t12)
    case TmApp(fi, v1, t2) if isVal(ctx, v1) =>
      TmApp(fi, v1, eval1(fi, ctx, t2))
    case TmApp(fi, t1, t2) =>
      TmApp(fi, eval1(fi, ctx, t1), t2)
    case TmIf(_, TmTrue(_), t1, _)  => t1
    case TmIf(_, TmFalse(_), _, t2) => t2
    case TmIf(fi, t1, t2, t3)       => TmIf(fi, eval1(info, ctx, t1), t2, t3)
    case TmFirst(_, TmProduct(_, v1, v2)) if isVal(ctx, v1) && isVal(ctx, v2) =>
      v1
    case TmSecond(_, TmProduct(_, v1, v2))
        if isVal(ctx, v1) && isVal(ctx, v2) =>
      v2
    case TmFirst(fi, t1)       => TmFirst(fi, eval1(fi, ctx, t1))
    case TmSecond(fi, t1)      => TmFirst(fi, eval1(fi, ctx, t1))
    case TmProduct(fi, t1, t2) => TmProduct(fi, eval1(fi, ctx, t1), t2)
    case TmProduct(fi, v1, t2) if isVal(ctx, v1) =>
      TmProduct(fi, v1, eval1(fi, ctx, t2))
    case TmCase(_, TmInl(_, v0, _), _, t1, _, _) if isVal(ctx, v0) => termSubstTop(v0, t1)
    case TmCase(_, TmInr(_, _, v0), _, _, _, t2) if isVal(ctx, v0) => termSubstTop(v0, t2)
    case TmCase(fi, t0, x1, t1, x2, t2) => TmCase(fi, eval1(info, ctx, t0), x1, t1, x2, t2)
    case TmInl(fi, t1, ty2) => TmInl(fi, eval1(info, ctx, t1), ty2)
    case TmInr(fi, ty1, t2) => TmInr(fi, ty1, eval1(info, ctx, t2))
    case _ => throw NoRuleAppliesException(t)
  }

  def eval(info: Info, ctx: Context, t: Term): Term =
    try {
      val t1 = eval1(info, ctx, t)
      eval(info, ctx, t1)
    } catch {
      case _: NoRuleAppliesException => t
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

  def externalTypeOf(ctx: Context, externalTerm: ExternalTerm): Type = {
    ctx.typeOf(refine(externalTerm))
  }
}
