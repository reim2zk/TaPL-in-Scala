package ch04

sealed trait Term
sealed trait Info
final case class TmTrue(info: Info) extends Term
final case class TmFalse(info: Info) extends Term
final case class TmIf(info: Info, t1: Term, t2: Term, t3: Term) extends Term
final case class TmZero(info: Info) extends Term
final case class TmSucc(info: Info, t1: Term) extends Term
final case class TmPred(info: Info, t1: Term) extends Term
final case class TmIsZero(info: Info, t1: Term) extends Term

final case object DummyInfo extends Info
final class NoRuleAppliesException(message: String = null,
                                   cause: Throwable = null)
    extends RuntimeException(message, cause)

class ML {}

object isNumericVal {
  def apply(t: Term): Boolean = t match {
    case TmZero(_)           => true
    case TmSucc(_, t1: Term) => isNumericVal(t1)
    case _                   => false
  }
}

object isVal {
  def apply(t: Term): Boolean = t match {
    case TmTrue(_)            => true
    case TmFalse(_)           => true
    case t if isNumericVal(t) => true
    case _                    => false
  }
}

object evalOnce {
  def apply(t: Term): Term = t match {
    case TmIf(_, TmTrue(_), t2, _)                        => t2
    case TmIf(_, TmFalse(_), _, t3)                       => t3
    case TmIf(fi, t1, t2, t3)                             => TmIf(fi, evalOnce(t1), t2, t3)
    case TmSucc(fi, t1)                                   => TmSucc(fi, evalOnce(t1))
    case TmPred(_, TmZero(_))                             => TmZero(DummyInfo)
    case TmPred(_, TmSucc(_, nv1)) if isNumericVal(nv1)   => nv1
    case TmPred(fi, t1)                                   => TmPred(fi, evalOnce(t1))
    case TmIsZero(_, TmZero(_))                           => TmTrue(DummyInfo)
    case TmIsZero(_, TmSucc(_, nv1)) if isNumericVal(nv1) => TmFalse(DummyInfo)
    case TmIsZero(fi, t1)                                 => TmIsZero(fi, evalOnce(t1))
    case _                                                => throw new NoRuleAppliesException
  }
}

object eval {
  def apply(t: Term): Term = {
    try { eval(evalOnce(t)) } catch {
      case _: NoRuleAppliesException => t
    }
  }
}
