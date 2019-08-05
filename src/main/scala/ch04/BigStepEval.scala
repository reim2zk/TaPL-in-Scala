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

/*
大ステップ意味論の評価規則
演習 4.2.2
 */
object bigStepEval {
  def apply(t: Term): Term = t match {
    case t1 if isVal(t1) => t1
    case TmIf(_, t1, t2, t3)
        if isTrue(bigStepEval(t1)) && isVal(bigStepEval(t2)) =>
      bigStepEval(t2)
    case TmIf(_, t1, t2, t3)
        if isFalse(bigStepEval(t1)) && isVal(bigStepEval(t3)) =>
      bigStepEval(t3)
    case TmSucc(_, t1) if isNumericVal(bigStepEval(t1)) =>
      TmSucc(DummyInfo, bigStepEval(t1))
    case TmPred(_, t1) if isZero(bigStepEval(t1)) => TmZero(DummyInfo)
    case TmPred(_, TmSucc(_, nv)) if isNumericVal(bigStepEval(nv)) =>
      bigStepEval(nv)
    case TmIsZero(_, t1) if isZero(bigStepEval(t1)) => TmTrue(DummyInfo)
    case TmIsZero(_, _: TmSucc)                     => TmFalse(DummyInfo)
    case _                                          => t
  }
}
