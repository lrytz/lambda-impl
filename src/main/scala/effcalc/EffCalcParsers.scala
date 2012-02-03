package effcalc

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.syntax._

object EffCalcParsers extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")",  "\\", ":", "=", "->", "[", "]", "{", "}", ",", "*", "!")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd", "bot", "top")

  /**
   * Term ::= SimpleTerm { SimpleTerm }
   */
  def Term: Parser[Term] = positioned(
      SimpleTerm ~ rep(SimpleTerm)    ^^ { case t ~ ts => (t :: ts).reduceLeft[Term](App) }
    | failure("illegal start of term"))

  /**
   * SimpleTerm ::= "true"
   *              | "false"
   *              | number
   *              | "succ" Term
   *              | "pred" Term
   *              | "iszero" Term
   *              | "if" Term "then" Term "else" Term
   *              | ident
   *              | "(" ident ":" Type) "->" [ "[" {ident} "]" ] Term
   *              | "(" Term ")"
   *              | "let" ident ":" Type "=" Term "in" Term
   *              | "{" Term "," Term "}"
   *              | "fst" Term
   *              | "snd" Term
   */
  def SimpleTerm: Parser[Term] = positioned(
      "true"          ^^^ True
    | "false"         ^^^ False
    | numericLit      ^^ { case chars => lit2Num(chars.toInt) }
    | "succ" ~ Term   ^^ { case "succ" ~ t => Succ(t) }
    | "pred" ~ Term   ^^ { case "pred" ~ t => Pred(t) }
    | "iszero" ~ Term ^^ { case "iszero" ~ t => IsZero(t) }
    | "if" ~ Term ~ "then" ~ Term ~ "else" ~ Term ^^ {
        case "if" ~ t1 ~ "then" ~ t2 ~ "else" ~ t3 => If(t1, t2, t3) 
      }
    | ident ^^ { case id => Var(id) }
    | "(" ~ ident ~ ":" ~ Type ~ ")" ~ "->" ~ opt("[" ~ rep(ident) ~ "]") ~ Term ^^ {
        case "(" ~ x ~ ":" ~ tp ~ ")" ~ "->" ~ Some("[" ~ poly ~ "]") ~ t => Abs(x, tp, poly, t)
        case "(" ~ x ~ ":" ~ tp ~ ")" ~ "->" ~ None ~ t => Abs(x, tp, Nil, t)
      }
    | "(" ~> Term <~ ")"  ^^ { case t => t } 
    | "let" ~ ident ~ ":" ~ Type ~ "=" ~ Term ~ "in" ~ Term ^^ {
        case "let" ~ id ~ ":" ~ tp ~ "=" ~ t1 ~ "in" ~ t2 => Let(id, tp, t1, t2)
      }
    | "{" ~ Term ~ "," ~ Term ~ "}" ^^ { case "{" ~ t1 ~ "," ~ t2 ~ "}" => Paar(t1, t2) }
    | "fst" ~ Term                  ^^ { case "fst" ~ t => First(t) }
    | "snd" ~ Term                  ^^ { case "snd" ~ t => Second(t) }
    | failure("illegal start of simple term"))

    

  private var paramCounter = 0
  private def paramName(): String = {
    paramCounter += 1
    "p$"+ paramCounter
  }

  /**
   * Type ::= "(" ident ":" Type) "->" [ "[" {ident} "]" ] [ "!" Effect ] Type
   *        | SimpleType "->" [ "[" {ident} "]" ] [ "!" Effect ] Type
   *        | SimpleType
   */
  def Type: Parser[Type] = positioned(
      "(" ~ ident ~ ":" ~ Type ~ ")" ~ "->" ~ opt("[" ~ rep(ident) ~ "]") ~ opt("!" ~ opt(Effect) ~ "!") ~ Type ^^ {
        case "(" ~ param ~ ":" ~ t1 ~ ")" ~ "->" ~ Some("[" ~ poly ~ "]") ~ Some("!" ~ eff ~ "!") ~ t2 =>
          TypeFun(param, t1, poly, eff.getOrElse(EffectBot), t2)
        case "(" ~ param ~ ":" ~ t1 ~ ")" ~ "->" ~ Some("[" ~ poly ~ "]") ~ None ~ t2 =>
          val eff = if (poly.isEmpty) EffectTop else EffectBot
          TypeFun(param, t1, poly, eff, t2)
        case "(" ~ param ~ ":" ~ t1 ~ ")" ~ "->" ~ None ~ Some("!" ~ eff ~ "!") ~ t2 =>
          TypeFun(param, t1, Nil, eff.getOrElse(EffectBot), t2)
        case "(" ~ param ~ ":" ~ t1 ~ ")" ~ "->" ~ None ~ None ~ t2 =>
          TypeFun(param, t1, Nil, EffectTop, t2)
      }
    | SimpleType ~ "->" ~ opt("[" ~ rep(ident) ~ "]") ~ opt("!" ~ opt(Effect) ~ "!") ~ Type ^^ {
        case t1 ~ "->" ~ Some("[" ~ poly ~ "]") ~ Some("!" ~ eff ~ "!") ~ t2 =>
          TypeFun(paramName(), t1, poly, eff.getOrElse(EffectBot), t2)
        case t1 ~ "->" ~ Some("[" ~ poly ~ "]") ~ None ~ t2 =>
          val eff = if (poly.isEmpty) EffectTop else EffectBot
          TypeFun(paramName(), t1, poly, eff, t2)
        case t1 ~ "->" ~ None ~ Some("!" ~ eff ~ "!") ~ t2 =>
          TypeFun(paramName(), t1, Nil, eff.getOrElse(EffectBot), t2)
        case t1 ~ "->" ~ None ~ None ~ t2 =>
          TypeFun(paramName(), t1, Nil, EffectTop, t2)
    }
    | SimpleType
    | failure("illegal start of type"))

  /**
   * SimpleType ::= BaseType [ "*" SimpleType ]
   */
  def SimpleType: Parser[Type] = positioned(
      BaseType ~ opt("*" ~ SimpleType) ^^ {
        case bt ~ Some("*" ~ st) => TypePaar(bt, st)
        case bt ~ None => bt
      }
    | failure("illegal start of simple type"))
    
  /**
   * BaseType ::= "Bool" | "Nat" | "(" Type ")"
   */
  def BaseType: Parser[Type] = positioned(
      "Bool" ^^^ TypeBool
    | "Nat"  ^^^ TypeNat
    | "(" ~> Type <~ ")" ^^ { case t => t }
  )
  
  /**
   * Effect ::= "bot" | "top" | ident { "," ident }
   */
  def Effect: Parser[Effect] = positioned(
      "bot" ^^^ EffectBot
    | "top" ^^^ EffectTop
    | ident ~ rep("," ~ ident) ^^ { case eff ~ effs => EffectSet((eff :: effs.map({case "," ~ id => id})).toSet.map(EffectAtom)) }
  )
  
  def lit2Num(n: Int): Term = 
    if (n == 0) Zero else Succ(lit2Num(n - 1))
}
