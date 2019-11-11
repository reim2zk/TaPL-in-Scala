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
    def addBinding(l: TmLocation, t: ITerm): Store = Store(map.+((l.index, t)))
    def substitute(l: TmLocation, t: ITerm): Store = {
      val i = l.index
      Store(map.-(i).+((i, t)))
    }
    def inDom(l: TmLocation): Boolean = map.contains(l.index)
    def getTerm(l: TmLocation): Option[ITerm] = map.get(l.index)
  }
  object Store {
    def apply(): Store = Store(Map.empty)
  }

  case class TypeStore(map: Map[Int, Type]) {
    def addBinding(l: TmLocation, ty: Type): TypeStore = TypeStore(map.+((l.index, ty)))
    def getType(l: TmLocation): Option[Type] = map.get(l.index)
  }
  object TypeStore {
    def apply(): TypeStore = TypeStore(Map.empty)
  }

  case class Context(l: List[(String, Binding)]) {
    def pickFreshName(s: String): (Context, String) =
      if (isNameBound(s)) pickFreshName(s + "'")
      else (Context((s, NameBind) :: l), s)

    def index2Name(x: TmVar): String = get(x.index)._1

    def getBinding(x: TmVar): Binding = get(x.index)._2

    def addBinding(x: String, bind: Binding): Context = Context((x, bind) :: l)

    def getTypeFromContext(fi: Info, x: TmVar): Option[Type] = getBinding(x) match {
      case VarBind(tyT: Type) => Some(tyT)
      case _ => None
    }

    def isNameBound(x: String): Boolean = l.exists(_._1 == x)

    private def get(i: Int): (String, Binding) = l(i)
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
    case _: TmAbs   => true
    case _: TmTrue  => true
    case _: TmFalse => true
    case _: TmUnit  => true
    case _          => false
  }

  def eval1(info: Info, store: Store, t: ITerm): Option[(ITerm, Store)] =
    t match {
      case TmApp(_, TmAbs(_, _, _, t12), v2) if isVal(v2) =>
        Some((termSubstTop(v2, t12), store))
      case TmApp(fi, v1, t2) if isVal(v1) =>
        for {
          (t2prime, storePrime) <- eval1(fi, store, t2)
        } yield (TmApp(fi, v1, t2prime), storePrime)
      case TmApp(fi, t1, t2) =>
        for {
          (t1prime, storePrime) <- eval1(fi, store, t1)
        } yield (TmApp(fi, t1prime, t2), storePrime)
      case TmRef(_, v1) if isVal(v1) => {
        val location = store.unboundedLocation(info)
        Some(location, store.addBinding(location, v1))
      }
      case TmRef(fi, t1) => for {
        (t1prime, storePrime) <- eval1(info, store, t1)
      } yield (TmRef(fi, t1prime), storePrime)
      case TmDeRef(_, l: TmLocation) => for {
        v <- store.getTerm(l)
      } yield (v, store)
      case TmDeRef(fi, t1) => for {
        (t1Prime, storePrime) <- eval1(fi, store, t1)
      } yield (t1Prime, storePrime)
      case TmAssign(fi, l: TmLocation, v2) if isVal(v2) =>
        Some((TmUnit(fi), store.substitute(l, v2)))
      case TmAssign(fi, v1, t2) if isVal(v1) => for {
        (t2Prime, storePrime) <- eval1(fi, store, t2)
      } yield (TmAssign(fi, v1, t2Prime), storePrime)
      case TmAssign(fi, t1, t2) => for {
        (t1Prime, storePrime) <- eval1(fi, store, t1)
      } yield (TmAssign(fi, t1Prime, t2), storePrime)
      case TmIf(_, TmTrue(_), t1, _)  => Some((t1, store))
      case TmIf(_, TmFalse(_), _, t2) => Some((t2, store))
      case TmIf(fi, t1, t2, t3) =>
        for {
          (t1Prime, storePrime) <- eval1(info, store, t1)
        } yield (TmIf(fi, t1Prime, t2, t3), storePrime)
      case _ => None
    }

  def eval(info: Info, store: Store, t: ITerm): ITerm =
    eval1(info, store, t) match {
      case Some((tPrime, storePrime)) => eval(info, storePrime, tPrime)
      case None                       => t
    }

  def typeOf(ctx: Context, store: TypeStore, t: ITerm): Option[Type] = t match {
    case x: TmVar => ctx.getTypeFromContext(x.info, x)
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
      tyT1 <- store.getType(l)
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
