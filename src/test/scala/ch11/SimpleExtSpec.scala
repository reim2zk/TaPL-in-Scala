package ch11

import org.scalatest.{DiagrammedAssertions, FlatSpec}

class SimpleExtSpec extends FlatSpec with DiagrammedAssertions {
  import ch11.SimpleExt._

  def vari(index: Int): Term = TmVar(Info(), index, index)
  def abs(xs0: (String, Type)*)(t: Term): Term = {
    val xs = xs0.reverse
    xs.tail.foldLeft(TmAbs(Info(), xs.head._1, xs.head._2, t))(
      (t1, x) => TmAbs(Info(), x._1, x._2, t1)
    )
  }
  def app(ts: Term*): Term = {
    ts.tail.foldLeft(ts.head)((t1, t2) => TmApp(Info(), t1, t2))
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
  def ev(t: Term): Term = eval(Info(), Context(), t)
  def ty(t: Term): Type = typeOf(Context(), t).get

  "SimpleExt" should "contain typeless Lambda eval" in {
    // FIXME: absTypeLess can be defined using abs
    def absTypeLess(xs0: String*)(t: Term): Term = {
      val xs = xs0.map(x => (x, TyBool)).reverse
      xs.tail.foldLeft(TmAbs(Info(), xs.head._1, xs.head._2, t))(
        (t1, x) => TmAbs(Info(), x._1, x._2, t1)
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
    val unit = TmUnit(Info())
    val ts = Seq(TmTrue(Info()), TmFalse(Info()))
    ts.foreach { t =>
      assert(eq(t, TmIf(Info(), TmTrue(Info()), t, unit)))
      assert(eq(t, TmIf(Info(), TmFalse(Info()), unit, t)))
      assert(
        eq(
          t,
          TmIf(
            Info(),
            TmIf(Info(), TmTrue(Info()), TmTrue(Info()), unit),
            t,
            unit
          )
        )
      )
    }
  }

  it should "support evaluating product" in {
    val unit = TmUnit(Info())
    val ts = Seq(TmTrue(Info()), TmFalse(Info()))
    ts.foreach { t =>
      assert(eq(t, TmFirst(Info(), TmProduct(Info(), t, unit))))
      assert(eq(t, TmSecond(Info(), TmProduct(Info(), unit, t))))
    }
  }

//  it should "support evaluating sum" in {
//    val info = Info()
//
//    val boolNot =
//      TmAbs(
//        info,
//        "x",
//        TyBool,
//        TmIf(info, TmVar(info, 0, 0), TmFalse(info), TmTrue(info))
//      )
//    val t1 = TmTrue(info)
//    val t2 = TmFalse(info)
//    val sl = TmInl(info, t1, TyBool)
//    val sr = TmInr(info, TyBool, t2)
//    val t = TmCase(info, sl, "x", t2, "y", t1)
//  }

  it should "support typing" in {
    val ts = Seq(TmTrue(Info()), TmFalse(Info()), TmUnit(Info()))
    assert(TyBool === ty(TmTrue(Info())))
    assert(TyBool === ty(TmFalse(Info())))
    assert(TyUnit === ty(TmUnit(Info())))

    ts.foreach { t1 =>
      val tyT1 = ty(t1)
      assert(tyT1 === ty(TmIf(Info(), TmTrue(Info()), t1, t1)))
      ts.foreach { t2 =>
        val tyT2 = ty(t2)

        val f = TmAbs(Info(), "x", tyT1, t2)
        assert(TyArr(tyT1, tyT2) === ty(f))
        assert(tyT2 === ty(TmApp(Info(), f, t1)))

        val p = TmProduct(Info(), t1, t2)
        assert(TyProduct(tyT1, tyT2) === ty(p))
        assert(tyT1 === ty(TmFirst(Info(), p)))
        assert(tyT2 === ty(TmSecond(Info(), p)))

        val sl = TmInl(Info(), t1, tyT2)
        val sr = TmInr(Info(), tyT1, t2)
        assert(TySum(tyT1, tyT2) == ty(sl))
        assert(TySum(tyT1, tyT2) == ty(sr))

        if (tyT1 == tyT2) {
          val cl = TmCase(Info(), sl, "x", t1, "y", t2)
          val cr = TmCase(Info(), sr, "x", t1, "y", t2)
          assert(tyT1 == ty(cl))
          assert(tyT2 == ty(cr))
        }
      }
    }
  }
}
