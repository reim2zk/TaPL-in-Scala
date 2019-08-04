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
object bigStep {
  def apply(t: Term): Term = t match {
    case t1 if isVal(t1) => t1
    case TmIf(_, t1, t2, t3) => {
      if (isTrue(bigStep(t1)) && isVal(bigStep(t2))) bigStep(t2)
      else if (isFalse(bigStep(t1)) && isVal(bigStep(t3))) bigStep(t3)
      else TmIf(DummyInfo, bigStep(t1), t2, t3)
    }
    case TmSucc(_, t1) if isNumericVal(bigStep(t1)) =>
      TmSucc(DummyInfo, bigStep(t1))
    case TmPred(_, t1) if isZero(bigStep(t1))         => TmZero(DummyInfo)
    case TmPred(_, TmSucc(_, nv)) if isNumericVal(bigStep(nv)) => bigStep(nv)
    case TmIsZero(_, t1) if isZero(bigStep(t1))       => TmTrue(DummyInfo)
    case TmIsZero(_, _: TmSucc)                       => TmFalse(DummyInfo)
    case _                                            => throw new NoRuleAppliesException
  }
}

object bigStepEval {
  def apply(t: Term): Term = {
    try { bigStep(t) } catch {
      case _: NoRuleAppliesException => t
    }
  }
}
