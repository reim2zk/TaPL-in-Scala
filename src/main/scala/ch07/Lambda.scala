package ch07

sealed trait Term
sealed trait Info
case object Info0 extends Info
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
      s"(λ $x1. ${rec(fi, ctx1, t1)})"
    }
    case TmApp(fi, t1, t2) => s"(${rec(fi, ctx, t1)} ${rec(fi, ctx, t2)})"
    case TmVar(_, x, _) => {
      if (ctx.l.length > x) { ctx.index2Name(x) } else { "[bad index]" }
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
        case TmAbs(fi, x, t1)  => TmAbs(fi, x, walk(c + 1, t1))
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

  def eval(info: Info, ctx: Context, t: Term): Term = {
    try {
      val t1 = eval1(info, ctx, t)
      eval(info, ctx, t1)
    } catch {
      case _: NoRuleAppliesException => t
    }
  }


  def lazyEval1(info: Info, ctx: Context, t: Term): Term = {
    t match {
      case TmApp(_, TmAbs(_, _, t12), t2) =>
        termSubstTop(t2, t12)
      case TmApp(fi, t1, t2) =>
        TmApp(fi, lazyEval1(fi, ctx, t1), t2)
      case t => throw new NoRuleAppliesException(t)
    }
  }

  def lazyEval(info: Info, ctx: Context, t: Term): Term = {
    try {
      val t1 = lazyEval1(info, ctx, t)
      lazyEval(info, ctx, t1)
    } catch {
      case _: NoRuleAppliesException => t
    }
  }

  def vari(index: Int): Term = TmVar(Info0, index, index)
  def abs(xs0: String*)(t: Term): Term = {
    val xs = xs0.reverse
    xs.tail.foldLeft(TmAbs(Info0, xs.head, t))((t1, x) => TmAbs(Info0, x, t1))
  }
  def app(ts: Term*): Term = {
    ts.tail.foldLeft(ts.head)((t1, t2) => TmApp(Info0, t1, t2))
  }

  // λx. x
  val id = abs("x")(vari(0))

  // λt.λf. t
  val tru = abs("t", "f")(vari(1))
  // λt.λf. f
  val fls = abs("t", "f")(vari(0))
  // λl.λm.λn. l m n
  val test = abs("l", "m", "n")(app(vari(2), vari(1), vari(0)))
  // λb.λc. b c fls
  val and = abs("b", "c")(app(vari(0), vari(1), fls))
  // λb.λc. b tru c
  val or = abs("b", "c")(app(vari(0), tru, vari(1)))

  // λs.λt.λb. b s t
  val pair = abs("s", "t", "b")(app(vari(0), vari(2), vari(1)))
  // λp. p tru
  val fst = abs("p")(app(vari(0), tru))
  // λp. p fls
  val snd = abs("p")(app(vari(0), fls))

  // λs.λz. z
  val c0 = abs("s", "z")(vari(0))
  // λs.λz. s z
  val c1 = abs("s", "z")(app(vari(1), vari(0)))
  // λs.λz. s (s z)
  val c2 = abs("s", "z")(app(vari(1), app(vari(1), vari(0))))
  // λs.λz. s ( s(s z))
  val c3 = abs("s", "z")(app(vari(1), app(vari(1), app(vari(1), vari(0)))))
  // λn.λs.λz. s (n s z)
  val scc = abs("n", "s", "z")(app(vari(1), app(vari(2), vari(1), vari(0))))
  // λn.λm. n scc m
  val plus = abs("n", "m")(app(vari(0), scc, vari(1)))
  // λn.λm. m (plus n) c0
  val times = abs("n", "m")(app(vari(0), app(plus, vari(1)), c0))
  // λm. m (λx. fls) tru
  val iszero = abs("m")(app(vari(0), abs("x")(fls), tru))
  // zz = pair c0 c0
  // ss = λp. pair (snd p) (scc (snd p))
  // pred = λn. fst (n ss zz)
  val zz = app(pair, c0, c0)
  val ss = abs("p")(app(pair, app(snd, vari(0)), app(scc, app(snd, vari(0)))))
  val pred = abs("n")(app(fst, app(vari(0), ss, zz)))
  // λn.λm. m pred n
  val minus = abs("n", "m")(app(vari(0), pred, vari(1)))
  // λn.λm. and (iszero (minus n m)) (iszero (minus m n))
  val equalNumber = abs("n", "m")(
    app(
      and,
      app(iszero, app(minus, vari(0), vari(1))),
      app(iszero, app(minus, vari(1), vari(0))),
    )
  )
  // fix = λf. (λx. f (λy. x x y)) (λx. f (λy. x x y))
  val yxx = abs("x")(app(vari(1), abs("y")(app(vari(1), vari(1), vari(0)))))
  val fix = abs("f")(app(yxx, yxx))
  val g = abs("fct", "n")(
    app(
      test,
      app(equalNumber, vari(0), c0),
      c1,
      app(times, vari(0), app(vari(1), app(pred, vari(0))))
    )
  )
  val factorial = app(fix, g)
}
