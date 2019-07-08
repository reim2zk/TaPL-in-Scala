package ch03

import org.scalatest.{DiagrammedAssertions, FlatSpec}

import ch03.SetTheory._

class SimpleLanguageSpec  extends FlatSpec with DiagrammedAssertions{

  "SuccS関数" should "【演習3.2.4】 S3の要素数" in {
    assert(SuccS(SuccS(SuccS(S0))).size === 59439)
  }
}
