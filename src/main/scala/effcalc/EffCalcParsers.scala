package effcalc

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.syntax._

object EffCalcParsers extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")",  "\\", ":", "=", "=>", "->", "[", "]", "{", "}", ",", "*")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd", "bot", "top")

  /** Term     ::= SimpleTerm { SimpleTerm }
   */
  def Term: Parser[Term] = positioned(
      SimpleTerm ~ rep(SimpleTerm)    ^^ { case t ~ ts => (t :: ts).reduceLeft[Term](App) }
    | failure("illegal start of term"))

  /** SimpleTerm ::= "true"
   *               | "false"
   *               | number
   *               | "succ" Term
   *               | "pred" Term
   *               | "iszero" Term
   *               | "if" Term "then" Term "else" Term
   *               | ident
   *               | "\" ident ":" Type "=>" Term
   *               | "\" ident ":" Type "->" Term
   *               | "(" Term ")"
   *               | "let" ident ":" Type "=" Term "in" Term
   *               | "{" Term "," Term "}"
   *               | "fst" Term
   *               | "snd" Term
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
    | "(" ~ ident ~ ":" ~ Type ~ ")" ~ "=>" ~ Term ^^ { case "(" ~ x ~ ":" ~ tp ~ ")" ~ "=>" ~ t => AbsM(x, tp, t) }
    | "(" ~ ident ~ ":" ~ Type ~ ")" ~ "->" ~ Term ^^ { case "(" ~ x ~ ":" ~ tp ~ ")" ~ "->" ~ t => AbsP(x, tp, t) }
    | "(" ~> Term <~ ")"  ^^ { case t => t } 
    | "let" ~ ident ~ ":" ~ Type ~ "=" ~ Term ~ "in" ~ Term ^^ {
        case "let" ~ id ~ ":" ~ tp ~ "=" ~ t1 ~ "in" ~ t2 => Let(id, tp, t1, t2)
      }
    | "{" ~ Term ~ "," ~ Term ~ "}" ^^ { case "{" ~ t1 ~ "," ~ t2 ~ "}" => Paar(t1, t2) }
    | "fst" ~ Term                  ^^ { case "fst" ~ t => First(t) }
    | "snd" ~ Term                  ^^ { case "snd" ~ t => Second(t) }
    | failure("illegal start of simple term"))

  /** Type       ::= SimpleType [ "->" Type ]
   */
  def Type: Parser[Type] = positioned(
      SimpleType ~ "=>" ~ opt("[" ~ Effect ~ "]") ~ Type ^^ {
        case t1 ~ "=>" ~ Some("[" ~ eff ~ "]") ~ t2 => TypeFunM(t1, t2, eff)
        case t1 ~ "=>" ~ None ~ t2 => TypeFunM(t1, t2, EffectTop)
      }
    | SimpleType ~ "->" ~ opt("[" ~ Effect ~ "]") ~ Type ^^ {
        case t1 ~ "->" ~ Some("[" ~ eff ~ "]") ~ t2 => TypeFunP(t1, t2, eff)
        case t1 ~ "->" ~ None ~ t2 => TypeFunP(t1, t2, EffectBot)
      }
    | SimpleType
    | failure("illegal start of type"))

  /** SimpleType ::= BaseType [ "*" SimpleType ]
   */
  def SimpleType: Parser[Type] = positioned(
      BaseType ~ opt("*" ~ SimpleType) ^^ {
        case bt ~ Some("*" ~ st) => TypePaar(bt, st)
        case bt ~ None => bt
      }
    | failure("illegal start of simple type"))
    
  /** BaseType ::= "Bool" | "Nat" | "(" Type ")"
   */
  def BaseType: Parser[Type] = positioned(
      "Bool" ^^^ TypeBool
    | "Nat"  ^^^ TypeNat
    | "(" ~> Type <~ ")" ^^ { case t => t }
  )
  
  def Effect: Parser[Effect] = positioned(
      "bot" ^^^ EffectBot
    | "top" ^^^ EffectTop
    | ident ~ rep("," ~ ident) ^^ { case eff ~ effs => EffectSet((eff :: effs.map({case "," ~ id => id})).toSet.map(EffectAtom)) }
  )
  
  def lit2Num(n: Int): Term = 
    if (n == 0) Zero else Succ(lit2Num(n - 1))
}