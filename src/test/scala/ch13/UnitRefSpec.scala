package ch13

import org.scalatest.{DiagrammedAssertions, FlatSpec}

class UnitRefSpec extends FlatSpec with DiagrammedAssertions {
  import ch13.ExternalUnitRef._
  import ch13.UnitRef.{Info, Type, Store, Context, equalTerm, ITerm, TypeStore}
  def eq(t1: Term, t2: Term): Boolean = equalTerm(ev(t1), ev(t2))
  def ev(t: Term): ITerm = eval(Info(), Store(), t)
  def ty(t: Term): Type = typeOf(Context(), TypeStore(), t).get

  "UnitRef" should "support evaluating boolean" in {
    val info = Info()
    val unit = TmUnit(info)
    val ts = Seq(TmTrue(info), TmFalse(info))
    ts.foreach { t =>
      assert(eq(t, TmIf(info, TmTrue(info), t, unit)))
      assert(eq(t, TmIf(info, TmFalse(info), unit, t)))
    }
  }

  "UnitRef" should "return assign and reference" in {
    val info = Info()
    val ts = Seq(TmTrue(info), TmFalse(info))
    ts.foreach { t =>
      eq(t, TmDeRef(info, TmRef(info, t)))
    }
  }
}
