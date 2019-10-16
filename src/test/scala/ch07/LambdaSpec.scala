package ch07

import org.scalatest.{DiagrammedAssertions, FlatSpec}

class LambdaSpec extends FlatSpec with DiagrammedAssertions {
  import ch07.Util._

  "Lambda" should "have identity operator" in {
    val term = eval1(Info0, Context(List.empty), app(id, c1))
    assert(c1 === term)
  }
}
