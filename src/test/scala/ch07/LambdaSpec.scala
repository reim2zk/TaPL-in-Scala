package ch07

import org.scalatest.{DiagrammedAssertions, FlatSpec}

class LambdaSpec extends FlatSpec with DiagrammedAssertions {
  import ch07.Util._

  def ev(t: Term): Term = eval(Info0, Context(List.empty), t)
  def pr(t: Term): String = Eval.rec(Info0, Context(List.empty), t)

  "Lambda" should "have identity operator" in {
    assert(c1 === ev(app(id, c1)))
  }

  it should "have boolean" in {
    assert(c0 === ev(app(test, tru, c0, c1)))
    assert(c1 === ev(app(test, fls, c0, c1)))
    assert(equalTerm(tru, ev(app(and, tru, tru))))
    assert(equalTerm(fls, ev(app(and, tru, fls))))
    assert(equalTerm(tru, ev(app(or, tru, tru))))
    assert(equalTerm(tru, ev(app(or, tru, fls))))
  }

  it should "have pair" in {
    assert(equalTerm(c0, ev(app(fst, app(pair, c0, c1)))))
    assert(equalTerm(c1, ev(app(snd, app(pair, c0, c1)))))
  }

  it should "have number" in {
    assert(equalTerm(tru, ev(app(iszero, app(pred, c1)))))
    assert(equalTerm(fls, ev(app(iszero, app(pred, c2)))))
    assert(equalTerm(tru, ev(app(equalNumber, c2, app(scc, c1)))))
    assert(equalTerm(tru, ev(app(equalNumber, c3, app(plus, c1, c2)))))
    assert(equalTerm(tru, ev(app(equalNumber, c1, app(minus, c2, c1)))))
  }

  it should "evaluate factorial" ignore {
    val t = app(factorial, c2)
    val s = ev(app(equalNumber, c2, t))
    val res = equalTerm(c2, s)
    assert(res)
  }

}
