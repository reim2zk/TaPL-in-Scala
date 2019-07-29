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

class ML {}

object isNumricVal {
  def apply(t: Term): Boolean = t match {
    case TmZero(_)           => true
    case TmSucc(_, t1: Term) => isNumricVal(t1)
    case _                => false
  }
}

object isVal {
  def apply(t: Term): Boolean = t match {
    case TmTrue(_)              => true
    case TmFalse(_)             => false
    case t if isNumricVal(t) => true
    case _                   => false
  }

}
