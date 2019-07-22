package ch03

import scala.collection.immutable.Set.empty

//抽象構文木
trait Syntax
trait Term extends Syntax
trait Value extends Syntax
trait BadNat
trait BadBool
trait NumericValue extends Value with BadBool

trait Zero extends Term with NumericValue with BadBool
trait True[T <: Term] extends Term with Value with BadNat
trait False[T <: Term] extends Term with Value with BadNat

trait Succ[T <: Term] extends Term
trait Pred[T <: Term] extends Term
trait IsZero[T <: Term] extends Term
trait IfElse[T1 <: Term, T2 <: Term, T3 <: Term] extends Term

final case object Wrong extends BadBool with BadNat

//final case object True extends Term with NumericValue with BadBool
//final case object False extends Term with Value with BadNat
//final case object Zero extends Term with Value with BadNat

//final case class Succ(t: Term) extends Term
//final case class Pred(t: Term) extends Term
//final case class IsZero(t: Term) extends Term
//final case class IfElse(t1: Term, t2: Term, t3: Term) extends Term

trait ToInt[T <: Term] { def apply(): Int }
object ToInt {
  def apply[T <: Term](implicit toInt: ToInt[T]): Int = toInt()
}

trait ToBool[T <: Term] { def apply(): Boolean }
object ToBool {
  def apply[T <: Term](implicit toBool: ToBool[T]): Boolean = toBool()
}

object Calculater {
  implicit def zero: ToInt[Zero] = () => 0

  implicit def succ[T <: Term](implicit toInt: ToInt[T]): ToInt[Succ[T]] =
    () => toInt() + 1

  //TODO: 0未満にならないようにする必要がある？
  implicit def pred[T <: Term](implicit toInt: ToInt[T]): ToInt[Pred[T]] =
    () => toInt() + 1

  implicit def isZero[T <: Term](implicit toInt: ToInt[T]): ToBool[IsZero[T]] =
    () =>
      toInt() match {
        case 0 => true
        case _ => false
    }
  implicit def ifElse[T1 <: Term, T2 <: Term, T3 <: Term](implicit toBool: ToBool[T1]): Term = {
    () => toBool() match {
      case true => T2
      case false => T3
    }
  }

}

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
  def apply(t: Term): Term = t match {
//    case Succ(_: BadNat)  => Wrong
    case Succ(t) => Succ(OneStepEval(t))
//    case Pred(_: BadBool) => Wrong
    case Pred(Zero)                   => Zero
    case Pred(Succ(nv: NumericValue)) => nv
    case Pred(t)                      => Pred(OneStepEval(t))
//    case IsZero(_: BadBool) => Wrong
    case IsZero(Zero)                  => True
    case IsZero(Succ(_: NumericValue)) => False
    case IsZero(t)                     => IsZero(OneStepEval(t))
    case IfElse(True, t2, _)           => t2
    case IfElse(False, _, t3)          => t3
    case IfElse(t1, t2, t3)            => IfElse(OneStepEval(t1), t2, t3)
    case _                             => throw new RuntimeException
  }
}

object Consts {
  def apply(t: Term): Set[Term] = t match {
    case True               => Set[Term](True)
    case False              => Set[Term](False)
    case Zero               => Set[Term](Zero)
    case Succ(t1)           => Consts(t1)
    case Pred(t1)           => Consts(t1)
    case IsZero(t1)         => Consts(t1)
    case IfElse(t1, t2, t3) => Consts(t1) | Consts(t2) | Consts(t3)
  }
}

object Size {
  def apply(t: Term): Int = t match {
    case True               => 1
    case False              => 1
    case Zero               => 1
    case Succ(t1)           => Size(t1) + 1
    case Pred(t1)           => Size(t1) + 1
    case IsZero(t1)         => Size(t1) + 1
    case IfElse(t1, t2, t3) => Size(t1) + Size(t2) + Size(t3) + 1
  }
}

object Depth {
  def apply(t: Term): Int = t match {
    case True               => 1
    case False              => 1
    case Zero               => 1
    case Succ(t1)           => Depth(t1) + 1
    case Pred(t1)           => Depth(t1) + 1
    case IsZero(t1)         => Depth(t1) + 1
    case IfElse(t1, t2, t3) => List(Depth(t1), Depth(t2), Depth(t3)).max + 1
  }
}
