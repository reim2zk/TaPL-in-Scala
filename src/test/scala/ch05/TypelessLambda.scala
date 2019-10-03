package ch05

import org.scalatest.{DiagrammedAssertions, FlatSpec}
import ch05.TypelessLambda._


class TypelessLambdaSpec extends FlatSpec with DiagrammedAssertions {
  "TypelessLambda" should "have identity operator" in {
    val id = TmAbs(x, x)
    val term = TmApply(id, y)
    val res = eval(term)
    assert(res === y)
  }
  it should "have test" in {
    val a = TmVar("a")
    val b = TmVar("b")
    val term0 = test(tru, a, b)
    val aa = eval(term0)
    assert(aa === a)
    val term1 = test(fal, a, b)
    val bb = eval(term1)
    assert(bb === b)
  }
  it should "have pair" in {
    val a = TmVar("a")
    val b = TmVar("b")
    val ab = pair(a, b)
    val term0 = TmApply(fst, ab)
    val aa = eval(term0)
    assert(aa == a)
    val term1 = TmApply(snd, ab)
    val bb = eval(term1)
    assert(bb == b)
  }
  it should "have natural number" in {
    val one2 = eval(succ(zero))
    assert(one === one2)

    val two2 = eval(succ(one))
    println("two2", two2)
    assert(two === two2)

    val two3 = eval(naturalNumber(2))
    println("two3", two3)
    assert(two == two3)

    val two5 = eval(TmApply(pred, four))
    println("two5", two5)
    assert(two === two5)

    val two4 = eval(tmApply3(mult, one, two))
    println(two4)
  }
}
