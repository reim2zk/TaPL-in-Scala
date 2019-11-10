package ch13

object UnitRef {
  sealed trait Info

  case object Info0 extends Info

  sealed trait ExternalTerm

  final case class TmSeq(info: Info, t1: Term, t2: Term) extends ExternalTerm

  sealed trait Term extends ExternalTerm

  final case class TmVar(info: Info, index: Int, contextLength: Int) extends Term

  final case class TmAbs(info: Info, v: String, ty: Type, t: Term) extends Term

  final case class TmApp(info: Info, t1: Term, t2: Term) extends Term

  final case class TmRef(info: Info, t: Term) extends Term

  final case class TmGet(info: Info, t: Term) extends Term

  final case class TmAssign(info: Info, t1: Term, t2: Term) extends Term

  final case class TmLocation(info: Info, index: Int) extends Term

  final case class TmTrue(info: Info) extends Term

  final case class TmFalse(info: Info) extends Term

  final case class TmIf(info: Info, t1: Term, t2: Term, t3: Term) extends Term

  final case class TmUnit(info: Info) extends Term

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

  case class Store(l: Map[Int, Term]) {}

  case class TypeStore(l: Map[Int, Type]) {}

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

  def isVal(t: Term): Boolean = t match {
    case TmAbs(_, _, _, _)                              => true
    case TmTrue(_)                                      => true
    case TmFalse(_)                                     => true
    case TmUnit(_)                                      => true
    case _                                              => false
  }

  def eval1(info: Info, store: Store, t: Term): (Store, Term) = t match {
    case TmApp(_, TmAbs(_, _, _, t12), v2) if isVal(v2) =>
      (store, termSubstTop(v2, t12))
    case TmApp(fi, v1, t2) if isVal(v1) =>
      val (storePrime, t2prime) = eval1(fi, store, t2)
      (storePrime, TmApp(fi, v1, t2prime))
    case TmApp(fi, t1, t2) =>
      val (storePrime, t1prime) = eval1(fi, store, t1)
      (storePrime, TmApp(fi, t1prime, t2))
    case TmIf(_, TmTrue(_), t1, _)  => (store, t1)
    case TmIf(_, TmFalse(_), _, t2) => (store, t2)
    case TmIf(fi, t1, t2, t3)       => (store, TmIf(fi, eval1(info, store, t1)._2, t2, t3))
    case _ => throw NoRuleAppliesException(t)
  }

  def eval(info: Info, store: Store, t: Term): Term =
    try {
      val (storePrime, t1) = eval1(info, store, t)
      eval(info, storePrime, t1)
    } catch {
      case _: NoRuleAppliesException => t
    }

  def typeOf(ctx: Context, store: Store, t: Term): Type = t match {
    case TmVar(fi, i, _) => ctx.getTypeFromContext(fi, i)
    case TmAbs(_, x, tyT1, t2) =>
      val ctx_ = ctx.addBinding(x, VarBind(tyT1))
      val tyT2 = typeOf(ctx_, store, t2)
      TyArr(tyT1, tyT2)
    case TmApp(fi, t1, t2) =>
      val tyT1 = typeOf(ctx, store, t1)
      val tyT2 = typeOf(ctx, store, t2)
      tyT1 match {
        case TyArr(tyT11, tyT12) if tyT2 == tyT11 => tyT12
        case TyArr(_, _)                          => throw NoRuleAppliesException(t)
        case _                                    => throw NoRuleAppliesException(t)
      }
    case TmTrue(_)  => TyBool
    case TmFalse(_) => TyBool
    case TmIf(fi, t1, t2, t3) if typeOf(ctx, store, t1) == TyBool =>
      if (typeOf(ctx, store, t2) == typeOf(ctx, store, t3)) typeOf(ctx, store, t2)
      else throw NoRuleAppliesException(t)
    case TmIf(fi, _, _, _) => throw NoRuleAppliesException(t)
    case TmUnit(_)         => TyUnit
  }


  def refine(t: ExternalTerm): Term = {
    t match {
      case TmSeq(fi, t1, t2) => TmApp(fi, TmAbs(fi, "x", TyUnit, refine(t1)), refine(t2))
      case t1: Term => t1
    }
  }

  def externalEval(info: Info, store: Store, externalTerm: ExternalTerm): Term = {
    eval(info, store, refine(externalTerm))
  }

  def externalTypeOf(ctx: Context, store: Store, externalTerm: ExternalTerm): Type = {
    typeOf(ctx, store, refine(externalTerm))
  }
}
