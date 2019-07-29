package ch04

sealed trait Term
final case object TmTrue extends Term
final case object TmFalse extends Term
final case class TmIf(t1: Term, t2: Term, t3: Term) extends Term
final case object TmZero extends Term
final case class TmSucc(t1: Term) extends Term
final case class TmPred(t1: Term) extends Term
final case class TmIsZero(t1: Term) extends Term

class ML {}

object isNumricVal {
  def apply(t: Term): Boolean = t match {
    case TmZero           => true
    case TmSucc(t1: Term) => isNumricVal(t1)
    case _                => false
  }
}

object isVal {
  def apply(t: Term): Boolean = t match {
    case TmTrue              => true
    case TmFalse             => false
    case t if isNumricVal(t) => true
    case _                   => false
  }

}
