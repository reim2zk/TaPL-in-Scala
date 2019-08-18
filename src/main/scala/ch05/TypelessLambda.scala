package ch05

sealed trait Term
final case class TmVar(name: String) extends Term
final case class TmAbs(x: TmVar, t: Term) extends Term
final case class TmApply(t1: Term, t2: Term) extends Term

object TypelessLambda {
  final class NoRuleAppliesException(term: Term) extends RuntimeException

  // substitution [x |-> s]t defined in TaPL p. 54
  def substitution(x: TmVar, s: Term, t: Term): Term = {
    t match {
      case y: TmVar if x==y => s
      case y: TmVar => y
      case TmAbs(y, t1) => TmAbs(y, substitution(x, s, t1))
      case TmApply(t1, t2) => TmApply(substitution(x, s, t1),
                                      substitution(x, s, t2))
    }
  }
  def evalOne(t: Term): Term =
    t match {
      case TmApply(t1, t2) => TmApply(evalOne(t1), t2)
      case TmApply(v: TmAbs, t2) => TmApply(v, evalOne(t2))
      case TmApply(TmAbs(x, t12), v2: TmAbs) => substitution(x, v2, t12)
      case _ => throw new NoRuleAppliesException(t)
    }
  def eval(t: Term): Term = try {
    eval(evalOne(t))
  } catch {
    case _: NoRuleAppliesException => t
  }
  def tmLambda2(x: TmVar, y: TmVar, t: Term): TmAbs = {
    TmAbs(x, TmAbs(y, t))
  }
  def tmLambda3(x: TmVar, y: TmVar, z: TmVar, t: Term): TmAbs = {
    TmAbs(x, TmAbs(y, TmAbs(z, t)))
  }
  def tmApply3(s: Term, t: Term, u: Term): Term = {
    TmApply(TmApply(s, t), u)
  }
  def tmApply4(s: Term, t: Term, u: Term, v: Term): Term = {
    TmApply(TmApply(TmApply(s, t), u), v)
  }
  // variables used in companion object
  val x = TmVar("x")
  val y = TmVar("y")
  val p = TmVar("p")
  val f = TmVar("f")
  val m = TmVar("m")
  val n = TmVar("n")

  // if-else
  val tru = tmLambda2(x, y, x)
  val fal = tmLambda2(x, y, y)
  def test(u: Term, v: Term, w: Term): Term = tmApply3(u, v, w)

  // pair
  def pair(t: Term, u: Term): Term = TmAbs(x, test(x, t, u))
  val fst = TmAbs(p, TmApply(p, tru))
  val snd = TmAbs(p, TmApply(p, fal))

  // charch number
  val zero = tmLambda2(f, x, x)
  val one  = tmLambda2(f, x, TmApply(f, x))
  val two  = tmLambda2(f, x, TmApply(f, TmApply(f, x)))
  val three= tmLambda2(f, x, TmApply(f, TmApply(f, TmApply(f, x))))
  val four = tmLambda2(f, x, TmApply(f, TmApply(f, TmApply(f, TmApply(f, x)))))
  def mult: Term = tmLambda2(m, n, TmApply(m, TmApply(n, f)))
  def pred: Term = {
    val g = TmVar("g")
    val h = TmVar("h")
    val u = TmVar("u")
    val u2 = TmVar("u2")
    val ff = tmLambda2(g, h, TmApply(h, TmApply(g, f)))
    val xx = TmAbs(u, x)
    val yy = TmAbs(u2, u2)
    tmLambda3(m, f, x, tmApply4(m, ff, xx, yy))
  }
  def succ(n: Term): Term = {
    //val nVal = eval(tmApply3(n, f, x))
    val nVal = tmApply3(n, f, x)
    tmLambda2(f, x, TmApply(f, nVal))
  }
  def pred(n: Term): Term = TmApply(snd, n)
  def naturalNumber(n: Int): Term = {
    eval((0 until n).foldLeft[Term](zero)((t, _) => succ(t)))
  }

  // fixed point combinator
  val Y = {
    val fx1 = TmAbs(x, TmApply(f, TmApply(x, x)))
    val fx2 = TmAbs(x, TmApply(f, TmApply(x, x)))
    TmAbs(f, TmApply(fx1, fx2))
  }


}

