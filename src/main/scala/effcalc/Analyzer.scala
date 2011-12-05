package effcalc

import scala.util.parsing.input.Position

object Analyzer {
  /** Print an error message, together with the position where it occured. */
  case class TypeError(pos: Position, msg: String) extends Exception(msg) {
    override def toString() =
      msg + "\n" + pos.longString
  }

  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term)(logger: Logger): (Type, Effect) = t match {
    case True | False =>
      (TypeBool, EffectBot)
    case Zero =>
      (TypeNat, EffectBot)
    case Succ(nv) =>
      val (tp, eff) = typeof(ctx, nv)(logger.indent)
      if (TypeNat == tp) (TypeNat, eff)
      else throw TypeError(t.pos, "numeric type expected")
    case Pred(nv) =>
      val (tp, eff) = typeof(ctx, nv)(logger.indent)
      if (TypeNat == tp) (TypeNat, eff)
      else throw TypeError(t.pos, "numeric type expected")
    case IsZero(nv) =>
      val (tp, eff) = typeof(ctx, nv)(logger.indent)
      if (TypeNat == tp) (TypeBool, eff)
      else throw TypeError(t.pos, "numeric type expected")
    case If(cond, t1, t2) =>
      val (ctp, ceff) = typeof(ctx, cond)(logger.indent)
      if (TypeBool == ctp) {
        val (ttp, teff) = typeof(ctx, t1)(logger.indent)
        val (etp, eeff) = typeof(ctx, t2)(logger.indent)
        if (ttp == etp) (ttp, teff.join(eeff).join(ceff))
        else throw TypeError(t.pos, "type mismatch between if branches")
      }
      else throw TypeError(t.pos, "boolean type expected")
    // lambda terms
    case Var(y) =>
      ctx.vals.get(y) match {
        case Some(tp) =>
          val res = (tp, EffectBot)
//          logger.log(ctx, t, res)
          res
        case None =>
          throw TypeError(t.pos, "undefined variable \'" + y + "'")
      }

    case Let(x, tp, t1, t2) =>
      val (tp1, eff1) = typeof(ctx, t1)(logger.indent)
      logger.indent.logCustom(tp1 +"  <:  "+ tp)
      if (isSub(tp1, tp)) {
        val ctx1 = Context(ctx.vals + (x -> tp), ctx.delayed)
        logger.logCustom("let "+ x +" = ...")
        typeof(ctx1, t2)(logger.indent)
      } else throw TypeError(t.pos, 
             "let type mismatch: expected " + tp + ", found " + tp1)
      
    case AbsM(x, tp, t1) =>
      val ctx1 = Context(ctx.vals + (x -> tp), ctx.delayed + (x -> tag(tp, x)))
      val (tp2, eff) = typeof(ctx1, t1)(logger.indent)
      val res = (TypeFunM(tp, tp2, eff), EffectBot)
      logger.logCustom("-- typing rule: mono abs --")
      logger.log(ctx, t, res)
      res
    case AbsP(x, tp, t1) =>
      val ctx1 = Context(ctx.vals ++ (ctx.delayed + (x -> tag(tp, x))), Map())
      val (tp2, eff) = typeof(ctx1, t1)(logger.indent)
      val res = (TypeFunP(tp, untagAll(tp2, ctx.delayed.keySet + x), eff), EffectBot)
      logger.logCustom("-- typing rule: poly abs --")
      logger.log(ctx, t, res)
      res

    case App(t1, t2) =>
      typeof(ctx, t1)(logger.indent) match {
        case (TypeFunM(tp11, tp12, eff), eff1) =>
          val (tp2, eff2) = typeof(ctx, t2)(logger.indent)
          logger.indent.logCustom(tp2 +"  <:  "+ tp11)
          if (isSub(tp2, tp11)) {
            val res = (push(latent(tp2), tp12), eff1.join(eff2).join(eff))
            logger.indent.logCustom("pushing latent("+ tp2 +") = "+ latent(tp2) +"   >> into: "+ tp12 )
            logger.logCustom("-- typing rule: mono app --")
            logger.log(ctx, t, res)
            res
          } else throw TypeError(t.pos, 
                 "parameter type mismatch: expected " + tp11 + ", found " + tp2)

        case (TypeFunP(tp11, tp12, eff), eff1) =>
          val (tp2, eff2) = typeof(ctx, t2)(logger.indent)
          logger.indent.logCustom(tp2 +"  <:  "+ tp11)
          if (isSub(tp2, tp11)) {
           val res = (tp12, eff1.join(eff2).join(eff).join(latent(tp2)))
           logger.indent.logCustom("latent("+ tp2 +") = "+ latent(tp2))
           logger.logCustom("-- typing rule: poly app --")
           logger.log(ctx, t, res)
           res
          } else throw TypeError(t.pos, 
                 "parameter type mismatch: expected " + tp11 + ", found " + tp2)
        
        case (TypeFunMTag(tp11, tp12, eff, tag), eff1) =>
          val (tp2, eff2) = typeof(ctx, t2)(logger.indent)
          logger.indent.logCustom(tp2 +"  <:  "+ tp11)
          if (isSub(tp2, tp11)) {
            val res = (push(latent(tp2), tp12), eff1.join(eff2))
            logger.logCustom("-- typing rule: tagged mono app --")
            logger.log(ctx, t, res)
            res
          } else throw TypeError(t.pos, 
                 "parameter type mismatch: expected " + tp11 + ", found " + tp2)
        
        case (TypeFunPTag(tp11, tp12, eff, tag), eff1) =>
          val (tp2, eff2) = typeof(ctx, t2)(logger.indent)
          logger.indent.logCustom(tp2 +"  <:  "+ tp11)
          if (isSub(tp2, tp11)) {
            val res = (tp12, eff1.join(eff2))
            logger.logCustom("-- typing rule: tagged poly app --")
            logger.log(ctx, t, res)
            res
          } else throw TypeError(t.pos, 
                 "parameter type mismatch: expected " + tp11 + ", found " + tp2)
        
        case tp =>
          throw TypeError(t.pos, "expected: function type\nfound: " + tp)
      }
    case Paar(t1, t2) =>
      val (tp1, eff1) = typeof(ctx, t1)(logger.indent)
      val (tp2, eff2) = typeof(ctx, t2)(logger.indent)
      (TypePaar(tp1, tp2), eff1.join(eff2))
    case First(t) =>
      val (tp, eff) = typeof(ctx, t)(logger.indent)
      tp match {
        case TypePaar(tp1, tp2) =>
          (tp1, eff)
        case _ =>
          throw TypeError(t.pos, "pair type expected but " + tp + " found")
      }
    case Second(t) =>
      val (tp, eff) = typeof(ctx, t)(logger.indent)
      tp match {
        case TypePaar(tp1, tp2) =>
          (tp2, eff)
        case _ =>
          throw TypeError(t.pos, "pair type expected but " + tp + " found")
      }
  }
  
  
  def tag(tp: Type, v: String): Type = tp match {
    case TypeFunM(t1, t2, eff) => TypeFunMTag(t1, tag(t2, v), eff, v)
    case TypeFunP(t1, t2, eff) => TypeFunPTag(t1, tag(t2, v), eff, v)
    case t => t
  }
  
  def untagAll(tp: Type, vs: Set[String]): Type = (tp /: vs)(untag)
  
  def untag(tp: Type, v: String): Type = tp match {
    case TypeFunMTag(t1, t2, eff, `v`) => TypeFunM(untag(t1, v), untag(t2, v), eff)
    case TypeFunPTag(t1, t2, eff, `v`) => TypeFunP(untag(t1, v), untag(t2, v), eff)
    case TypeFunMTag(t1, t2, eff, t) => TypeFunMTag(untag(t1, v), untag(t2, v), eff, t)
    case TypeFunPTag(t1, t2, eff, t) => TypeFunPTag(untag(t1, v), untag(t2, v), eff, t)
    case TypePaar(t1, t2) => TypePaar(untag(t1, v), untag(t2, v))
    case t => t
  }

  def push(eff: Effect, tp: Type): Type = tp match {
    case TypeFunM(t1, t2, e) => TypeFunM(t1, push(eff, t2), e)
    case TypeFunP(t1, t2, e) => TypeFunP(t1, t2, e.join(eff))
    case TypeFunMTag(t1, t2, e, t) => TypeFunMTag(t1, push(eff, t2), e, t)
    case TypeFunPTag(t1, t2, e, t) => TypeFunPTag(t1, t2, e.join(eff), t)
    case t => t
  }
  
  def latent(tp: Type): Effect = tp match {
    case TypeFunM(t1, t2, e) => e.join(latent(t2))
    case TypeFunP(t1, t2, e) => e.join(latent(t1))
    case TypeFunMTag(t1, t2, e, t) => e
    case TypeFunPTag(t1, t2, e, t) => e.join(latent(t1))
    case t => EffectBot
  }
  
  def isSub(tpa: Type, tpb: Type): Boolean = (tpa, tpb) match {
    case (TypeBool, TypeBool) => true
    case (TypeNat, TypeNat) => true

    case (TypePaar(at1, at2), TypePaar(bt1, bt2)) =>
      isSub(at1, bt1) && isSub(at2, bt2)

    case (TypeFunMTag(at1, at2, ae, av), tpb) => isSub(TypeFunM(at1, at2, ae), tpb)
    case (TypeFunPTag(at1, at2, ae, av), tpb) => isSub(TypeFunP(at1, at2, ae), tpb)
    case (tpa, TypeFunMTag(bt1, bt2, be, bv)) => isSub(tpa, TypeFunM(bt1, bt2, be))
    case (tpa, TypeFunPTag(bt1, bt2, be, bv)) => isSub(tpa, TypeFunP(bt1, bt2, be))

    case (TypeFunM(at1, at2, ae), TypeFunM(bt1, bt2, be)) =>
      isSub(bt1, at1) && isSub(push(latent(at1), at2), push(latent(bt1), bt2)) && subEff(ae, be)

    case (TypeFunM(at1, at2, ae), TypeFunP(bt1, bt2, be)) =>
      isSub(bt1, at1) && isSub(push(latent(at1), at2), bt2) && subEff(ae, be.join(latent(bt1)))
    case (TypeFunP(at1, at2, ae), TypeFunM(bt1, bt2, be)) =>
      isSub(bt1, at1) && isSub(at2, push(latent(bt1), bt2)) && subEff(ae.join(latent(at1)), be)

    case (TypeFunP(at1, at2, ae), TypeFunP(bt1, bt2, be)) =>
      isSub(bt1, at1) && isSub(at2, bt2) && subEff(ae.join(latent(at1)), be.join(latent(bt1)))
      
    case _ => false
  }
  
  def subEff(e1: Effect, e2: Effect): Boolean = (e1, e2) match {
    case (EffectBot, _) | (_, EffectTop) => true
    case (EffectTop, _) | (_, EffectBot) => false
    case (EffectSet(s1), EffectSet(s2)) => s1.subsetOf(s2)
  }
}

case class Context(vals: Map[String, Type], delayed: Map[String, Type]) {
  override def toString() = {
    vals.map(kv => kv._1 +":"+ kv._2).mkString("{",", ","}") + " ; " + delayed.map(kv => kv._1 +":"+ kv._2).mkString("{", ", ", "}")
  }
}

object Context {
  def empty = apply(Map(), Map())
}
