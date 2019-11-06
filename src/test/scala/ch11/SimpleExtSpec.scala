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
      case _ => false
    }
  }
  def ev(t: Term): Term = eval(Info0, Context(), t)

  "SimpleExt" should "contain typeless Lambda" in {
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
    val ts = Seq(tru, fls)
    ts.foreach { t =>
      assert(eq(t, app(id, t)))
    }
  }
}
