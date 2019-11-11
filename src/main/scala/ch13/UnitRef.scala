package ch13

object UnitRef {
  sealed trait Info
  object Info {
    case object Info0 extends Info
    def apply(): Info = Info0
  }
  sealed trait ITerm

  final case class TmVar(info: Info, index: Int, contextLength: Int)
      extends ITerm
  final case class TmAbs(info: Info, v: String, ty: Type, t: ITerm)
      extends ITerm
  final case class TmApp(info: Info, t1: ITerm, t2: ITerm) extends ITerm
  final case class TmRef(info: Info, t: ITerm) extends ITerm
  final case class TmDeRef(info: Info, t: ITerm) extends ITerm
  final case class TmAssign(info: Info, t1: ITerm, t2: ITerm) extends ITerm
  final case class TmLocation(info: Info, index: Int) extends ITerm
  final case class TmTrue(info: Info) extends ITerm
  final case class TmFalse(info: Info) extends ITerm
  final case class TmIf(info: Info, t1: ITerm, t2: ITerm, t3: ITerm)
      extends ITerm
  final case class TmUnit(info: Info) extends ITerm

  sealed trait Type
  final case class TyArr(ty1: Type, ty2: Type) extends Type
  case class TyRef(tyT: Type) extends Type
  case object TyBool extends Type
  case object TyUnit extends Type

  sealed trait Binding

  case object NameBind extends Binding

  final case class VarBind(ty: Type) extends Binding

  final case class NoRuleAppliesException(term: ITerm) extends RuntimeException

  case class Store(map: Map[Int, ITerm]) {
    def unboundedLocation(info: Info): TmLocation =
      TmLocation(info, map.keys.max)
    def addBinding(i: Int, t: ITerm): Store = Store(map.+((i, t)))
    def substitute(i: Int, t: ITerm): Store = Store(map.-(i).+((i, t)))
    def inDom(l: TmLocation): Boolean = map.contains(l.index)
    def getTerm(i: Int): Option[ITerm] = map.get(i)
  }
  object Store {
    def apply(): Store = Store(Map.empty)
  }

  case class TypeStore(map: Map[Int, Type]) {
    def addBinding(i: Int, ty: Type): TypeStore = TypeStore(map.+((i, ty)))
    def getType(i: Int): Option[Type] = map.get(i)
  }
  object TypeStore {
    def apply(): TypeStore = TypeStore(Map.empty)
  }

  case class Context(l: List[(String, Binding)]) {
    def pickFreshName(s: String): (Context, String) =
      if (isNameBound(s)) pickFreshName(s + "'")
      else (Context((s, NameBind) :: l), s)

    def index2Name(i: Int): String = get(i)._1

    def getBinding(i: Int): Binding = get(i)._2

    def addBinding(x: String, bind: Binding): Context = Context((x, bind) :: l)

    def getTypeFromContext(fi: Info, i: Int): Type = getBinding(i) match {
      case VarBind(tyT: Type) => tyT
      case _ =>
        error(fi, s"Wrong kind of binding for variable ${index2Name(i)}")
    }

    def isNameBound(x: String): Boolean = l.exists(_._1 == x)

    @throws
    private def get(i: Int): (String, Binding) = l(i)

    private def error(fi: Info, msg: String): Nothing = {
      println(msg)
      sys.exit(1) // Scala の sys.exit() は Nothing を返すので任意の型として扱える！
    }
  }
  object Context {
    def apply(): Context = Context(List.empty)
  }

  def applyAll(t: ITerm, f: ITerm => ITerm): ITerm = {
    t match {
      case TmVar(fi, x, n)         => TmVar(fi, x, n)
      case TmAbs(fi, x, ty, t1)    => TmAbs(fi, x, ty, f(t1))
      case TmApp(fi, t1, t2)       => TmApp(fi, f(t1), f(t2))
      case TmRef(info, t1)         => TmRef(info, f(t1))
      case TmDeRef(info, t2)       => TmDeRef(info, f(t2))
      case TmAssign(info, t1, t2)  => TmAssign(info, f(t1), f(t2))
      case TmLocation(info, index) => TmLocation(info, index)
      case TmTrue(_)               => t
      case TmFalse(_)              => t
      case TmIf(fi, t1, t2, t3)    => TmIf(fi, f(t1), f(t2), f(t3))
      case TmUnit(_)               => t
    }
  }

  def termShift(d: Int, t: ITerm): ITerm = {
    def walk(c: Int, t: ITerm): ITerm = t match {
      case TmVar(fi, x, n) =>
        if (x >= c) TmVar(fi, x + d, n + d) else TmVar(fi, x, n + d)
      case TmAbs(fi, x, ty, t1) => TmAbs(fi, x, ty, walk(c + 1, t1))
      case t                    => applyAll(t, walk(c, _))
    }
    walk(0, t)
  }

  def termSubst(j: Int, s: ITerm, t: ITerm): ITerm = {
    def walk(c: Int, t: ITerm): ITerm = {
      t match {
        case TmVar(fi, x, n) =>
          if (x == j + c) termShift(c, s) else TmVar(fi, x, n)
        case TmAbs(fi, x, ty, t1) => TmAbs(fi, x, ty, walk(c + 1, t1))
        case _                    => applyAll(t, walk(c, _))
      }
    }
    walk(0, t)
  }

  def termSubstTop(s: ITerm, t: ITerm): ITerm =
    termShift(-1, termSubst(0, termShift(1, s), t))

  def isVal(t: ITerm): Boolean = t match {
    case TmAbs(_, _, _, _) => true
    case TmTrue(_)         => true
    case TmFalse(_)        => true
    case TmUnit(_)         => true
    case _                 => false
  }

  def eval1(info: Info, store: Store, t: ITerm): Option[(Store, ITerm)] =
    t match {
      case TmApp(_, TmAbs(_, _, _, t12), v2) if isVal(v2) =>
        Some((store, termSubstTop(v2, t12)))
      case TmApp(fi, v1, t2) if isVal(v1) =>
        for {
          (storePrime, t2prime) <- eval1(fi, store, t2)
        } yield (storePrime, TmApp(fi, v1, t2prime))
      case TmApp(fi, t1, t2) =>
        for {
          (storePrime, t1prime) <- eval1(fi, store, t1)
        } yield (storePrime, TmApp(fi, t1prime, t2))
      case TmRef(_, v1) if isVal(v1) => {
        val location = store.unboundedLocation(info)
        Some(store.addBinding(location.index, v1), location)
      }
      case TmRef(fi, t1) => for {
        (storePrime, t1prime) <- eval1(info, store, t1)
      } yield (storePrime, TmRef(fi, t1prime))
      case TmDeRef(_, l: TmLocation) => for {
        v <- store.getTerm(l.index)
      } yield (store, v)
      case TmDeRef(fi, t1) => for {
        (storePrime, t1Prime) <- eval1(fi, store, t1)
      } yield (storePrime, t1Prime)
      case TmAssign(fi, l: TmLocation, v2) if isVal(v2) =>
        Some((store.substitute(l.index, v2), TmUnit(fi)))
      case TmAssign(fi, t1, t2) => for {
        (storePrime, t1Prime) <- eval1(fi, store, t1)
      } yield (storePrime, TmAssign(fi, t1Prime, t2))
      case TmAssign(fi, v1, t2) if isVal(v1) => for {
        (storePrime, t2Prime) <- eval1(fi, store, t2)
      } yield (storePrime, TmAssign(fi, v1, t2Prime))
      case TmIf(_, TmTrue(_), t1, _)  => Some((store, t1))
      case TmIf(_, TmFalse(_), _, t2) => Some((store, t2))
      case TmIf(fi, t1, t2, t3) =>
        for {
          (storePrime, t1Prime) <- eval1(info, store, t1)
        } yield (storePrime, TmIf(fi, t1Prime, t2, t3))
      case _ => None
    }

  def eval(info: Info, store: Store, t: ITerm): ITerm =
    eval1(info, store, t) match {
      case Some((storePrime, tPrime)) => eval(info, storePrime, tPrime)
      case None                       => t
    }

  def typeOf(ctx: Context, store: TypeStore, t: ITerm): Option[Type] = t match {
    case TmVar(fi, i, _) => Some(ctx.getTypeFromContext(fi, i))
    case TmAbs(_, x, tyT1, t2) =>
      val ctx_ = ctx.addBinding(x, VarBind(tyT1))
      for {
        tyT2 <- typeOf(ctx_, store, t2)
      } yield TyArr(tyT1, tyT2)
    case TmApp(_, t1, t2) =>
      for {
        tyT1 <- typeOf(ctx, store, t1)
        tyT2 <- typeOf(ctx, store, t2)
        tyT12 <- tyT1 match {
          case TyArr(tyT11, tyT12) if tyT2 == tyT11 => Some(tyT12)
          case _                                    => None
        }
      } yield tyT12
    case l: TmLocation => for {
      tyT1 <- store.getType(l.index)
    } yield TyRef(tyT1)
    case TmRef(_, t1) => for {
      tyT1 <- typeOf(ctx, store, t1)
    } yield tyT1
    case TmDeRef(_, t1) => for {
      tyT1 <- typeOf(ctx, store, t1)
      tyT11 <- tyT1 match {
        case TyRef(tyT1) => Some(tyT1)
        case _           => None
      }
    } yield tyT11
    case TmAssign(_, t1, t2)  => for {
      tyT1 <- typeOf(ctx, store, t1)
      tyT11 <- typeOf(ctx, store, t2)
      tyUnit <- if(tyT1 == TyRef(tyT11)) Some(TyUnit) else None
    } yield tyUnit
    case TmTrue(_)               => Some(TyBool)
    case TmFalse(_)              => Some(TyBool)
    case TmIf(_, t1, t2, t3) if typeOf(ctx, store, t1).contains(TyBool) =>
      for {
        tyT2 <- typeOf(ctx, store, t2)
        tyT3 <- typeOf(ctx, store, t3)
        tyT <- if (tyT2 == tyT3) Some(tyT2) else None
      } yield tyT
    case TmIf(_, _, _, _) => None
    case TmUnit(_)        => Some(TyUnit)
  }

  def equalTerm(t1: ITerm, t2: ITerm): Boolean = {
    (t1, t2) match {
      case (TmVar(_, i1, _), TmVar(_, i2, _)) => i1 == i2
      case (TmAbs(_, v1, _, t1), TmAbs(_, v2, _, t2)) =>
        v1 == v2 && equalTerm(t1, t2)
      case (TmApp(_, t11, t12), TmApp(_, t21, t22)) =>
        equalTerm(t11, t21) && equalTerm(t12, t22)
      case (TmRef(_, t1), TmRef(_, t2))     => equalTerm(t1, t2)
      case (TmDeRef(_, t1), TmDeRef(_, t2)) => equalTerm(t1, t2)
      case (TmAssign(_, t1, t2), TmAssign(_, s1, s2)) =>
        equalTerm(t1, s1) && equalTerm(t2, s2)
      case (TmLocation(_, i), TmLocation(_, j)) => i == j
      case (TmTrue(_), TmTrue(_))               => true
      case (TmFalse(_), TmFalse(_))             => true
      case (TmIf(_, t11, t12, t13), TmIf(_, t21, t22, t23)) =>
        equalTerm(t11, t21) && equalTerm(t12, t22) && equalTerm(t13, t23)
      case (TmUnit(_), TmUnit(_)) => true
      case _                      => false
    }
  }
}
