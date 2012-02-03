package effcalc

import scala.util.parsing.input.Positional

/** Abstract Syntax Trees for terms. */
abstract class Term extends Positional {
//  def tpStr(tp: Type) = if (false && tp.isFun) "("+ tp +")" else tp
}

case object True extends Term {
  override def toString() = "true"
}

case object False extends Term {
  override def toString() = "false"
}
case object Zero extends Term {
  override def toString() = "0"
}
///-
case class Succ(t: Term) extends Term {
  override def toString() = "succ " + t
}
case class Pred(t: Term) extends Term {
  override def toString() = "pred " + t
}
case class IsZero(t: Term) extends Term {
  override def toString() = "iszero " + t
}
case class If(cond: Term, t1: Term, t2: Term) extends Term {
  override def toString() = "if " + cond + " then " + t1 + " else " + t2
}

case class Var(name: String) extends Term {
  override def toString() = name
}
case class Let(v: String, tp: Type, t1: Term, t2: Term) extends Term {
  override def toString() = "let "+ v +":"+ tp +" = "+ t1 +" in\n"+ t2
}
case class Abs(x: String, tp: Type, poly: List[String], t: Term) extends Term {
  override def toString() = {
    val polyString = if (poly.isEmpty) "" else poly.mkString("[", ",", "]")
    "(" + x + ":" + tp + ") ->" + polyString + " " + t
  }
}
case class App(t1: Term, t2: Term) extends Term {
  override def toString() = t1.toString + (t2 match {
    case App(_, _) => " (" + t2.toString + ")" // left-associative
    case _         => " " + t2.toString
  })
}
case class Paar(t1: Term, t2: Term) extends Term {
  override def toString() = "{" + t1 + "," + t2 + "}"
}

case class First(t: Term) extends Term {
  override def toString() = "fst " + t
}

case class Second(t: Term) extends Term {
  override def toString() = "snd " + t
}
