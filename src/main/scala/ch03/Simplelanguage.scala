package ch03

import scala.collection.immutable.Set.empty

//抽象構文木
sealed trait _Syntax
sealed trait Term extends _Syntax
sealed trait Value extends _Syntax
sealed trait NumericValue extends Value

final case object True extends Term with Value
final case object False extends Term with Value
final case class IfElse(t1: Term, t2: Term, t3: Term) extends Term
final object Zero extends Term with NumericValue
final case class Succ(t: Term) extends Term
final case class Pred(t: Term) extends Term
final case class IsZero(t: Term) extends Term

//inference
sealed trait I_True[T <: Term]
sealed trait I_False[T <: Term]
sealed trait I_Zero[T <: Term]
sealed abstract class I_Succ[T <: Term](t: T)
final abstract class I_Pred[T <: Term](t: T)
final abstract class I_IsZero[T <: Term](t: T)
final abstract class I_IfElse[T1 <: Term, T2 <: Term, T3 <: Term](t1: T1,
                                                                  t2: T2,
                                                                  t3: T3)
//set
object SetTheory {
  private type S = Set[Term]
  private type StreamS = Stream[S]

  val S0: S = empty

  val SuccS: S => S = s => {
    Set[Term](True, False, Zero) | {
      for {
        t1: Term <- s
        expr1 <- Set[Term](Succ(t1), Pred(t1), IsZero(t1))
      } yield expr1
    } | {
      for {
        t1: Term <- s
        t2: Term <- s
        t3: Term <- s
        expr2 <- Set[Term](IfElse(t1, t2, t3))
      } yield expr2
    }
  }

  val StreamS: Stream[S] = S0 #:: StreamS
    .zip(SuccS(S0) #:: StreamS)
    .map(s => SuccS(s._1))

}

//評価器
object OneStepEval {
  val oneStepEval: Term => Term = {
    case Succ(t)                       => Succ(oneStepEval(t))
    case Pred(Zero)                    => Zero
    case Pred(Succ(nv: NumericValue))  => nv
    case Pred(t)                       => Pred(oneStepEval(t))
    case IsZero(Zero)                  => True
    case IsZero(Succ(_: NumericValue)) => False
    case IsZero(t)                     => IsZero(oneStepEval(t))
    case _                             => throw new RuntimeException
  }
}
