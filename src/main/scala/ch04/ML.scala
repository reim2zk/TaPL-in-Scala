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

object isNumricVal {
  def apply(t: Term): Boolean = t match {
    case TmZero(_)           => true
    case TmSucc(_, t1: Term) => isNumricVal(t1)
    case _                   => false
  }
}

object isVal {
  def apply(t: Term): Boolean = t match {
    case TmTrue(_)           => true
    case TmFalse(_)          => false
    case t if isNumricVal(t) => true
    case _                   => false
  }

  object evalOne {
    def apply(t: Term): Term = t match {
      case TmIf(_, TmTrue(_), t2, t3)                      => t2
      case TmIf(_, TmFalse(_), t2, t3)                     => t3
      case TmIf(fi, t1, t2, t3)                            => TmIf(fi, evalOne(t1), t2, t3)
      case TmSucc(fi, t1)                                  => TmSucc(fi, evalOne(t1))
      case TmPred(_, TmZero(_))                            => TmZero(DummyInfo)
      case TmPred(_, TmSucc(_, nv1)) if isNumricVal(nv1)   => nv1
      case TmPred(fi, t1)                                  => TmPred(fi, evalOne(t1))
      case TmIsZero(_, TmZero(_))                          => TmFalse(DummyInfo)
      case TmIsZero(_, TmSucc(_, nv1)) if isNumricVal(nv1) => TmFalse(DummyInfo)
      case TmIsZero(fi, t1)                                => TmIsZero(fi, evalOne(t1))
      case _                                               => throw new NoRuleAppliesException
    }
  }

  object eval {
    def apply(t: Term): Term = t match {
      case t: Term => {
        try {
          eval(evalOne(t))
        } catch {
          case _: NoRuleAppliesException => t
        }
      }
    }
  }
}

object bigStepEval {
  def apply(t: Term): Term = t match {
//    case t1 if isVal(t1) => t1
//    case TmIf(_, t1, t2, t3)
//      if isTrue(bigStepEval(t1)) && isVal(bigStepEval(t2)) =>
//      bigStepEval(t2)
//    case TmIf(_, t1, t2, t3)
//      if isFalse(bigStepEval(t1)) && isVal(bigStepEval(t3)) =>
//      bigStepEval(t3)
//    case TmSucc(_, t1) if isNumericVal(bigStepEval(t1)) =>
//      TmSucc(DummyInfo, bigStepEval(t1))
//    case TmPred(_, t1) if isZero(bigStepEval(t1)) => TmZero(DummyInfo)
//    case TmPred(_, TmSucc(_, nv)) if isNumericVal(bigStepEval(nv)) =>
//      bigStepEval(nv)
//    case TmIsZero(_, t1) if isZero(bigStepEval(t1)) => TmTrue(DummyInfo)
//    case TmIsZero(_, _: TmSucc)                     => TmFalse(DummyInfo)
//    case _                                          => t
    case t1 => t1
    case TmIf(_, TmTrue(_), t2, _) => bigStepEval(t2)
    case TmIf(_, TmFalse(_), _, t3) => bigStepEval(t3)
    case TmSucc(_, t1) if isNumricVal(t1) => bigStepEval(t1)
    case TmPred(_, t1) if isZero(t1) => bigStepEval(t1)
    case TmPred(_, t1) if isNumricVal(t1) => bigStepEval(t1)
    case TmIsZero(fi, t1) if isZero(t1) => TmTrue(fi)
    case TmIsZero(fi, t1) if !isZero(t1) => TmFalse(fi)

  }

 //TOOD: 実装する
  def isZero(t: Term): Boolean = ???
}