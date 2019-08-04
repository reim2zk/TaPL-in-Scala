package ch04

/*
`最終的に評価される値` の判定を便宜的に追加
 */
object isTrue {
  def apply(t: Term): Boolean = t match {
    case TmTrue(_) => true
    case _         => false
  }
}

object isFalse {
  def apply(t: Term): Boolean = t match {
    case TmFalse(_) => true
    case _          => false
  }
}

object isZero {
  def apply(t: Term): Boolean = t match {
    case TmZero(_) => true
    case _         => false
  }
}

object isSuccNv {
  def apply(t: Term): Boolean = t match {
    case TmSucc(_, t1) if isNumericVal(t1) => true
    case _                                 => false
  }
}

/*
最終的な評価値
今回は簡易的に，小ステップ意味論の最終的な評価値を使う
 */
object finalVal {
  def apply(t: Term): Term = eval(t)
}

/*
大ステップ意味論の評価規則
演習 4.2.2
 */
object bigStepEval {
  def apply(t: Term): Term = t match {
    case t if isVal(finalVal(t)) => finalVal(t)
    case TmIf(_, t1, t2, _)
        if isTrue(bigStepEval(t1)) && isVal(bigStepEval(t2)) =>
      bigStepEval(t2)
    case TmIf(_, t1, _, t3)
        if isFalse(bigStepEval(t1)) && isVal(bigStepEval(t3)) =>
      bigStepEval(t3)
    case TmSucc(_, t1) if isNumericVal(bigStepEval(t1)) =>
      TmSucc(DummyInfo, bigStepEval(t1))
    case TmPred(_, t1) if isZero(bigStepEval(t1))     => TmZero(DummyInfo)
    case TmPred(_, t1) if isSuccNv(bigStepEval(t1))   => bigStepEval(t1)
    case TmIsZero(_, t1) if isZero(bigStepEval(t1))   => TmTrue(DummyInfo)
    case TmIsZero(_, t1) if isSuccNv(bigStepEval(t1)) => TmFalse(DummyInfo)
    case _                                            => t // 行き詰まり状態の表現
  }
}
