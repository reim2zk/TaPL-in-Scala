package ch11

object ExternalSimpleExt {
  import ch11.{SimpleExt => I}
  import ch11.SimpleExt.{Info, Context}
  sealed trait ETerm

  final case class TmSeq(info: Info, t1: ETerm, t2: ETerm) extends ETerm
  final case class TmVar(info: Info, index: Int, contextLength: Int)
      extends ETerm
  final case class TmAbs(info: Info, v: String, ty: I.Type, t: ETerm)
      extends ETerm
  final case class TmApp(info: Info, t1: ETerm, t2: ETerm) extends ETerm
  final case class TmTrue(info: Info) extends ETerm
  final case class TmFalse(info: Info) extends ETerm
  final case class TmIf(info: Info, t1: ETerm, t2: ETerm, t3: ETerm)
      extends ETerm
  final case class TmUnit(info: Info) extends ETerm
  final case class TmProduct(info: Info, t1: ETerm, t2: ETerm) extends ETerm
  final case class TmFirst(info: Info, t: ETerm) extends ETerm
  final case class TmSecond(info: Info, t: ETerm) extends ETerm
  final case class TmInl(info: Info, t1: ETerm, ty2: I.Type) extends ETerm
  final case class TmInr(info: Info, ty1: I.Type, t2: ETerm) extends ETerm
  final case class TmCase(info: Info,
                          t: ETerm,
                          xl: String,
                          tl: ETerm,
                          xr: String,
                          tr: ETerm)
      extends ETerm

  def refine(t: ETerm): I.Term = t match {
    case TmSeq(fi, t1, t2) =>
      I.TmApp(fi, I.TmAbs(fi, "x", I.TyUnit, refine(t1)), refine(t2))
    case TmVar(fi, i, d)       => I.TmVar(fi, i, d)
    case TmAbs(fi, v, ty, t)   => I.TmAbs(fi, v, ty, refine(t))
    case TmApp(fi, t1, t2)     => I.TmApp(fi, refine(t1), refine(t2))
    case TmTrue(fi)            => I.TmTrue(fi)
    case TmFalse(fi)           => I.TmFalse(fi)
    case TmIf(fi, t1, t2, t3)  => I.TmIf(fi, refine(t1), refine(t2), refine(t3))
    case TmUnit(fi)            => I.TmUnit(fi)
    case TmProduct(fi, t1, t2) => I.TmProduct(fi, refine(t1), refine(t2))
    case TmFirst(fi, t)        => I.TmFirst(fi, refine(t))
    case TmSecond(fi, t)       => I.TmSecond(fi, refine(t))
    case TmInl(fi, t1, tyT2)   => I.TmInl(fi, refine(t1), tyT2)
    case TmInr(fi, tyT1, t2)   => I.TmInr(fi, tyT1, refine(t2))
    case TmCase(fi, t, xl, tl, xr, tr) =>
      I.TmCase(fi, refine(t), xl, refine(tl), xr, refine(tr))
  }

  def eval(info: Info, ctx: Context, t: ETerm): I.Term =
    I.eval(info, ctx, refine(t))
  def typeOf(info: Info, ctx: Context, t: ETerm): Option[I.Type] =
    I.typeOf(ctx, refine(t))
}
