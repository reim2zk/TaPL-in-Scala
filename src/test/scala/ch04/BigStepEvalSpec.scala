package ch04

import org.scalatest.FlatSpec

import scala.collection.immutable.Set.empty

class BigStepEvalSpec extends FlatSpec {

  val S0: Set[Term] = empty

  val SuccS: Set[Term] => Set[Term] = s => {
    Set[Term](TmTrue(DummyInfo), TmFalse(DummyInfo), TmZero(DummyInfo)) | {
      for {
        t1: Term <- s
        expr1 <- Set[Term](TmSucc(DummyInfo, t1),
                           TmPred(DummyInfo, t1),
                           TmIsZero(DummyInfo, t1))
      } yield expr1
    } | {
      for {
        t1: Term <- s
        t2: Term <- s
        t3: Term <- s
        expr2 <- Set[Term](TmIf(DummyInfo, t1, t2, t3))
      } yield expr2
    }
  }

  val StreamS: Stream[Set[Term]] = S0 #:: StreamS
    .zip(SuccS(S0) #:: StreamS)
    .map(s => SuccS(s._1))

  "bigStepEval result" should "be equal to OneStepEval result, only if result is value" in {
    StreamS(3)
      .filter(s => isVal(eval(s))) // 「t ->* v のとき，かつそのときに限り t ⇓ v」. この条件を外すと…
      .foreach { s =>
        println(s)
        assert(bigStepEval(s) === eval(s))
      }
  }
}
