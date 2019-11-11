package ch13

object ExternalUnitRef {
  import ch13.{UnitRef => I}
  import ch13.UnitRef.{Info, Type, Store, Context, ITerm}

  trait Term
  final case class TmSeq(info: Info, t1: Term, t2: Term) extends Term
  final case class TmVar(info: Info, index: Int, contextLength: Int)
      extends Term
  final case class TmAbs(info: Info, v: String, ty: Type, t: Term) extends Term
  final case class TmApp(info: Info, t1: Term, t2: Term) extends Term
  final case class TmRef(info: Info, t: Term) extends Term
  final case class TmDeRef(info: Info, t: Term) extends Term
  final case class TmAssign(info: Info, t1: Term, t2: Term) extends Term
  final case class TmLocation(info: Info, index: Int) extends Term
  final case class TmTrue(info: Info) extends Term
  final case class TmFalse(info: Info) extends Term
  final case class TmIf(info: Info, t1: Term, t2: Term, t3: Term) extends Term
  final case class TmUnit(info: Info) extends Term

  def refine(t: Term): ITerm = {
    t match {
      case TmSeq(fi, t1, t2) =>
        I.TmApp(fi, I.TmAbs(fi, "x", I.TyUnit, refine(t1)), refine(t2))
      case TmVar(fi, i, k)         => I.TmVar(fi, i, k)
      case TmAbs(fi, v, ty, t)     => I.TmAbs(fi, v, ty, refine(t))
      case TmApp(fi, t1, t2)       => I.TmApp(fi, refine(t1), refine(t2))
      case TmRef(fi, t)            => I.TmRef(fi, refine(t))
      case TmDeRef(fi, t)          => I.TmDeRef(fi, refine(t))
      case TmAssign(fi, t1, t2)    => I.TmAssign(fi, refine(t1), refine(t2))
      case TmLocation(info, index) => I.TmLocation(info, index)
      case TmTrue(info)            => I.TmTrue(info)
      case TmFalse(info)           => I.TmFalse(info)
      case TmIf(info, t1, t2, t3) =>
        I.TmIf(info, refine(t1), refine(t2), refine(t3))
      case TmUnit(info) => I.TmUnit(info)
    }
  }

  def eval(info: Info, store: Store, t: Term): ITerm = {
    I.eval(info, store, refine(t))
  }
  def typeOf(ctx: Context, store: Store, t: Term): Option[Type] =
    I.typeOf(ctx, store, refine(t))
}
