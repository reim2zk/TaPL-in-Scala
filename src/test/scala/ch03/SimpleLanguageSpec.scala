package ch03

import org.scalatest.{DiagrammedAssertions, FlatSpec}

import ch03.SetTheory._
import scala.collection.Set.empty

class SimpleLanguageSpec extends FlatSpec with DiagrammedAssertions {

  "Interence" should "【定義3.2.1 3.2.2】" in {
    //TODO: Tの定義とは？
    val T1 = StreamS(1)
    val T2 = StreamS(2)

    assert(T1 contains True)
    assert(T1 contains False)
    assert(T1 contains Zero)

    val f1 = for {
      t1 <- T1
      expr <- Set[Term](Succ(t1))
    } yield expr
    assert(f1 subsetOf T2)

    val f2 = for {
      t1 <- T1
      expr <- Set[Term](Pred(t1))
    } yield expr
    assert(f2 subsetOf T2)

    val f3 = for {
      t1 <- T1
      expr <- Set[Term](IsZero(t1))
    } yield expr
    assert(f3 subsetOf T2)

    val g1 = for {
      t1 <- T1
      t2 <- T1
      t3 <- T1
      expr <- Set[Term](IfElse(t1, t2, t3))
    } yield expr
    assert(g1 subsetOf T2)
  }

  "SuccS関数" should "【定義3.2.3】" in {
    assert(StreamS(0) === empty)
    assert(StreamS(1) === Set[Term](True, False, Zero))
    assert(
      StreamS(2) ===
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
    assert(StreamS(3).size === 59439)
  }
  "Const関数" should "【定義3.3.1】" in {
    val T1: Set[Term] = StreamS(1)
    val T2: Set[Term] = StreamS(2)

    assert(Consts(True) === Set[Term](True))
    assert(Consts(False) === Set[Term](False))
    assert(Consts(Zero) === Set[Term](Zero))

    for {
      t1 <- T1
      res = assert(Consts(Succ(t1)) === Consts(t1))
    } yield res

    for {
      t1 <- T1
      res = assert(Consts(Pred(t1)) === Consts(t1))
    } yield res

    for {
      t1 <- T1
      res = assert(Consts(IsZero(t1)) === Consts(t1))
    } yield res

    for {
      t1 <- T1
      t2 <- T1
      t3 <- T1
      res = assert(
        Consts(IfElse(t1, t2, t3)) === (Consts(t1) union Consts(t2) union Consts(t3)))
    } res
  }
}
