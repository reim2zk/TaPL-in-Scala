package ch11

import org.scalatest.{DiagrammedAssertions, FlatSpec}

class SimpleExtSpec extends FlatSpec with DiagrammedAssertions {
  import ch11.SimpleExt._

  def vari(index: Int): Term = TmVar(Info0, index, index)
  def abs(xs0: (String, Type)*)(t: Term): Term = {
    val xs = xs0.reverse
    xs.tail.foldLeft(TmAbs(Info0, xs.head._1, xs.head._2, t))(
      (t1, x) => TmAbs(Info0, x._1, x._2, t1)
    )
  }
  def app(ts: Term*): Term = {
    ts.tail.foldLeft(ts.head)((t1, t2) => TmApp(Info0, t1, t2))
  }
  def eq(t1: Term, t2: Term): Boolean = {
    (ev(t1), ev(t2)) match {
      case (TmVar(_, i1, _), TmVar(_, i2, _)) => i1 == i2
      case (TmAbs(_, v1, _, t1), TmAbs(_, v2, _, t2)) =>
        v1 == v2 && eq(t1, t2)
      case (TmApp(_, t11, t12), TmApp(_, t21, t22)) =>
        eq(t11, t21) && eq(t12, t22)
      case (TmTrue(_), TmTrue(_))   => true
      case (TmFalse(_), TmFalse(_)) => true
      case (TmIf(_, t11, t12, t13), TmIf(_, t21, t22, t23)) =>
        eq(t11, t21) && eq(t12, t22) && eq(t13, t23)
      case (TmUnit(_), TmUnit(_)) => true
      case (TmProduct(_, t11, t12), TmProduct(_, t21, t22)) =>
        eq(t11, t21) && eq(t12, t22)
      case (TmFirst(_, t1), TmFirst(_, t2))   => eq(t1, t2)
      case (TmSecond(_, t1), TmSecond(_, t2)) => eq(t1, t2)
      case _                                  => false
    }
  }
  def ev(t: Term): Term = eval(Info0, Context(), t)
  def ty(t: Term): Type = typeOf(Info0, Context(), t)

  "SimpleExt" should "contain typeless Lambda eval" in {
    // FIXME: absTypeLess can be defined using abs
    def absTypeLess(xs0: String*)(t: Term): Term = {
      val xs = xs0.map(x => (x, TyBool)).reverse
      xs.tail.foldLeft(TmAbs(Info0, xs.head._1, xs.head._2, t))(
        (t1, x) => TmAbs(Info0, x._1, x._2, t1)
      )
    }
    val id = absTypeLess("x")(vari(0))
    val tru = absTypeLess("t", "f")(vari(1))
    val fls = absTypeLess("t", "f")(vari(0))
    val test = absTypeLess("l", "m", "n")(app(vari(2), vari(1), vari(0)))
    val and = absTypeLess("b", "c")(app(vari(0), vari(1), fls))
    val or = absTypeLess("b", "c")(app(vari(0), tru, vari(1)))

    val ts = Seq(tru, fls)
    ts.foreach { t =>
      assert(eq(t, app(id, t)))
      assert(eq(t, app(test, tru, t, fls)))
      assert(eq(t, app(test, fls, fls, t)))
    }
    assert(eq(tru, app(and, tru, tru)))
    assert(eq(fls, app(and, tru, fls)))
    assert(eq(tru, app(or, tru, tru)))
    assert(eq(tru, app(or, tru, fls)))
  }

  it should "support evaluating boolean" in {
    val unit = TmUnit(Info0)
    val ts = Seq(TmTrue(Info0), TmFalse(Info0))
    ts.foreach { t =>
      assert(eq(t, TmIf(Info0, TmTrue(Info0), t, unit)))
      assert(eq(t, TmIf(Info0, TmFalse(Info0), unit, t)))
      assert(
        eq(
          t,
          TmIf(Info0, TmIf(Info0, TmTrue(Info0), TmTrue(Info0), unit), t, unit)
        )
      )
    }
  }

  it should "support evaluating pair" in {
    val unit = TmUnit(Info0)
    val ts = Seq(TmTrue(Info0), TmFalse(Info0))
    ts.foreach { t =>
      assert(eq(t, TmFirst(Info0, TmProduct(Info0, t, unit))))
      assert(eq(t, TmSecond(Info0, TmProduct(Info0, unit, t))))
    }
  }

  it should "support typing" in {
    assert(TyBool === ty(TmTrue(Info0)))
    assert(TyBool === ty(TmFalse(Info0)))

    val ts = Seq(TmTrue(Info0), TmFalse(Info0))
    ts.foreach { t =>
      assert(ty(t) === ty(TmIf(Info0, TmTrue(Info0), TmUnit(Info0), t)))
    }

  }
}
