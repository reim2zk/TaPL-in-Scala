package ch03

//抽象構文木
sealed trait _Syntax
sealed trait Term extends _Syntax
sealed trait Value extends _Syntax
sealed trait NumericValue extends Value with _Syntax

final case object True extends Term with Value
final case object False extends Term with Value
final case class IfElse(t1: Term, t2: Term, t3: Term) extends Term
final object Zero extends Term with NumericValue
final case class Succ(t: Term) extends Term
final case class Pred(t: Term) extends Term
final case class IsZero(t: Term) extends Term

//評価器
object OneStepEval {
  val oneStepEval: Term => Term = t =>
    t match {
      case Succ(t)                       => Succ(oneStepEval(t))
      case Pred(Zero)                    => Zero
      case Pred(Succ(nv: NumericValue))  => nv
      case Pred(t)                       => Pred(oneStepEval(t))
      case IsZero(Zero)                  => True
      case IsZero(Succ(_: NumericValue)) => False
      case IsZero(t)                     => IsZero(oneStepEval(t))
  }
}
