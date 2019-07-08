package ch03

import org.scalatest.{DiagrammedAssertions, FlatSpec}

import ch03.SetTheory._
import scala.collection.Set.empty

class SimpleLanguageSpec extends FlatSpec with DiagrammedAssertions {

  "SuccS関数" should "【定義3.2.3】" in {
    assert(S0 === empty)
    assert(SuccS(S0) === Set[Term](True, False, Zero))
    assert(
      SuccS(SuccS(S0)) ===
        Set[Term](
          IfElse(Zero, True, False),
          IfElse(Zero, Zero, True),
          IfElse(Zero, True, Zero),
          IfElse(True, True, True),
          IfElse(True, Zero, True),
          IfElse(False, False, Zero),
          IfElse(Zero, Zero, Zero),
          IfElse(False, False, False),
          IfElse(True, False, Zero),
          IfElse(Zero, False, Zero),
          IfElse(True, Zero, False),
          True,
          False,
          IfElse(True, Zero, Zero),
          Succ(Zero),
          Pred(Zero),
          IsZero(Zero),
          IfElse(False, True, Zero),
          IfElse(False, True, True),
          Zero,
          IfElse(False, Zero, Zero),
          Succ(True),
          Pred(True),
          IsZero(True),
          IfElse(True, False, True),
          IfElse(Zero, Zero, False),
          IfElse(Zero, False, False),
          IfElse(True, True, Zero),
          IfElse(False, True, False),
          Succ(False),
          Pred(False),
          IsZero(False),
          IfElse(False, Zero, True),
          IfElse(True, False, False),
          IfElse(True, True, False),
          IfElse(False, Zero, False),
          IfElse(Zero, True, True),
          IfElse(Zero, False, True),
          IfElse(False, False, True)
        ))
  }

  "SuccS関数" should "【演習3.2.4】 S3の要素数" in {
    assert(SuccS(SuccS(SuccS(S0))).size === 59439)
  }
}
