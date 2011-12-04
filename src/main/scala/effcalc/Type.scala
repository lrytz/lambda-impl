package effcalc

import scala.util.parsing.input.Positional

/** Abstract Syntax Trees for types. */
abstract class Type extends Positional {
  def isFun = false
  def effStr(eff: Effect, default: Effect) =
    if (eff == default) " "
    else "["+ eff +"] "
}

case object TypeBool extends Type {
  override def toString() = "Bool"
}

case object TypeNat extends Type {
  override def toString() = "Nat"
}

case class TypeFunM(t1: Type, t2: Type, eff: Effect) extends Type {
  override def isFun = true
  override def toString() = {
    (if (t1.isFun) "(" + t1 + ")" // right-associative
     else t1.toString) + " =>" + effStr(eff, EffectTop) + t2
  }
}
case class TypeFunMTag(t1: Type, t2: Type, eff: Effect, tag: String) extends Type {
  override def isFun = true
  override def toString() = {
    (if (t1.isFun) "(" + t1 + ")" // right-associative
     else t1.toString) + " ='" + tag + "'" + "=>" + effStr(eff, EffectTop) + t2
  }
}
case class TypeFunP(t1: Type, t2: Type, eff: Effect) extends Type {
  override def isFun = true
  override def toString() = {
    (if (t1.isFun) "(" + t1 + ")" // right-associative
     else t1.toString) + " ->" + effStr(eff, EffectBot) + t2
  }
}
case class TypeFunPTag(t1: Type, t2: Type, eff: Effect, tag: String) extends Type {
  override def isFun = true
  override def toString() = {
    (if (t1.isFun) "(" + t1 + ")" // right-associative
     else t1.toString) + " -'" + tag + "'->" + effStr(eff, EffectBot) + t2
  }
}


case class TypePaar(t1: Type, t2: Type) extends Type {
  override def toString() = "(" + t1 + " * " + t2 + ")"
}


// effects

abstract class Effect extends Positional {
  def join(other: Effect) = (this, other) match {
    case (EffectBot, _) => other
    case (_, EffectBot) => this
    case (EffectTop, _) | (_, EffectTop) => EffectTop
    case (EffectSet(s1), EffectSet(s2)) => EffectSet(s1 union s2)
  }
}

case object EffectBot extends Effect {
  override def toString() = "bot"
}
case object EffectTop extends Effect {
  override def toString() = "top"
}
case class EffectSet(set: Set[EffectAtom]) extends Effect {
  override def toString() = set.map(_.name).mkString("{", ",", "}")
}
case class EffectAtom(name: String) {
  override def toString() = name
}
