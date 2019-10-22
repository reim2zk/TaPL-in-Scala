package ch07

sealed trait Term
sealed trait Info
final case class TmVar(info: Info, index: Int, contextLength: Int) extends Term
final case class TmAbs(info: Info, v: String, t: Term) extends Term
final case class TmApp(info: Info, t1: Term, t2: Term) extends Term

sealed trait Binding
final case object NameBind extends Binding

final case class NoRuleAppliesException(term: Term) extends RuntimeException

case class Context(l: List[(String, Binding)]) {
  def pickFreshName(s: String): (Context, String) = {
    if (isNameBound(s)) {
      pickFreshName(s + "'")
    } else {
      (Context((s, NameBind) :: l), s)
    }
  }

  def index2Name(i: Int): String = get(i)._1

  private def isNameBound(x: String): Boolean = l.exists(_._1 == x)

  @throws
  private def get(i: Int): (String, Binding) = l(i)
}

object Eval {
  def rec(printtm: Info, ctx: Context, t: Term): String = t match {
    case TmAbs(fi, x, t1) => {
      val (ctx1, x1) = ctx.pickFreshName(x)
      s"(lambda $x1. ${rec(fi, ctx, t1)})"
    }
    case TmApp(fi, t1, t2) => s"(${rec(fi, ctx, t1)} ${rec(fi, ctx, t2)})"
    case TmVar(fi, x, n) => {
      if (ctx.l.length == n) { ctx.index2Name(x) } else { "[bad index]" }
    }
  }
}

object Util {
  def termShift(d: Int, t: Term): Term = {
    def walk(c: Int, t: Term): Term = {
      t match {
        case TmVar(fi, x, n) =>
          if (x >= c) TmVar(fi, x + d, n + d) else TmVar(fi, x, n + d)
        case TmAbs(fi, x, t1)  => TmAbs(fi, x, walk(c + 1, t1))
        case TmApp(fi, t1, t2) => TmApp(fi, walk(c, t1), walk(c, t2))
      }
    }

    walk(0, t)
  }

  def termSubst(j: Int, s: Term, t: Term): Term = {
    def walk(c: Int, t: Term): Term = {
      t match {
        case TmVar(fi, x, n) =>
          if (x == j + c) termShift(c, s) else TmVar(fi, x, n)
        case TmAbs(fi, x, t1)  => TmAbs(fi, x, walk(c + 1, t))
        case TmApp(fi, t1, t2) => TmApp(fi, walk(c, t1), walk(c, t2))
      }
    }
    walk(0, t)
  }

  def termSubstTop(s: Term, t: Term): Term =
    termShift(-1, termSubst(0, termShift(1, s), t))

  def isVal(ctx: Context, t: Term): Boolean = t match {
    case TmAbs(_, _, _) => true
    case _              => false
  }

  def eval1(info: Info, ctx: Context, t: Term): Term = {
    t match {
      case TmApp(fi, TmAbs(fi2, x, t12), v2) if isVal(ctx, v2) =>
        termSubstTop(v2, t12)
      case TmApp(fi, v1, t2) if isVal(ctx, v1) =>
        TmApp(fi, v1, eval1(fi, ctx, t2))
      case TmApp(fi, t1, t2) =>
        TmApp(fi, eval1(fi, ctx, t1), t2)
      case t => throw new NoRuleAppliesException(t)
    }
  }
}
