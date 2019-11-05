package ch11

import org.scalatest.{DiagrammedAssertions, FlatSpec}

class LambdaSpec extends FlatSpec with DiagrammedAssertions {
  "Lambda" should "have identity operator" in {
    assert(2 === 1+1)
  }
}