package ch07

import org.scalatest.{DiagrammedAssertions, FlatSpec}

class LambdaSpec extends FlatSpec with DiagrammedAssertions {
  import ch07.Util._

  def eq(t1: Term, t2: Term): Boolean = {
    (ev(t1), ev(t2)) match {
      case (TmVar(_, i1, _), TmVar(_, i2, _))   => i1 == i2
      case (TmAbs(_, v1, t1), TmAbs(_, v2, t2)) => v1 == v2 && eq(t1, t2)
      case (TmApp(_, t11, t12), TmApp(_, t21, t22)) =>
        eq(t11, t21) && eq(t12, t22)
      case _ => false
    }
  }
  def eqn(t1: Term, t2: Term): Boolean = {
    eq(tru, app(equalNumber, t1, t2))
  }
  def ev(t: Term): Term = eval(Info0, Context(List.empty), t)
  def pr(t: Term): String = Eval.rec(Info0, Context(List.empty), t)

  "Lambda" should "have identity operator" in {
    assert(c1 === ev(app(id, c1)))
  }

  it should "have boolean" in {
    assert(c0 === ev(app(test, tru, c0, c1)))
    assert(c1 === ev(app(test, fls, c0, c1)))
    assert(eq(tru, app(and, tru, tru)))
    assert(eq(fls, app(and, tru, fls)))
    assert(eq(tru, app(or, tru, tru)))
    assert(eq(tru, app(or, tru, fls)))
  }

  it should "have pair" in {
    assert(eq(c0, app(fst, app(pair, c0, c1))))
    assert(eq(c1, app(snd, app(pair, c0, c1))))
  }

  it should "have number" in {
    assert(eq(tru, app(iszero, app(pred, c1))))
    assert(eq(fls, app(iszero, app(pred, c2))))

    assert(eq(tru, app(iszero, app(minus, c3, c3))))
    assert(eq(tru, app(iszero, app(minus, c2, c3))))
    assert(eq(fls, app(iszero, app(minus, c3, c2))))

    assert(eqn(c2, app(scc, c1)))
    assert(eqn(c3, app(plus, c1, c2)))
    assert(eqn(c1, app(minus, c2, c1)))
  }

  it should "evaluate factorial" in {
    val fct2 = lazyEval(Info0, Context(List.empty), app(factorial, c2))
    assert(eqn(c2, fct2))

    val fct3 = lazyEval(Info0, Context(List.empty), app(factorial, c3))
    assert(eqn(app(times, c2, c3), fct3))
  }

}
