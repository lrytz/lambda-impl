package effcalc

import scala.util.parsing.input.Position

object Analyzer {
  /** Print an error message, together with the position where it occured. */
  case class TypeError(pos: Position, msg: String) extends Exception(msg) {
    override def toString() =
      msg + "\n" + pos.longString
  }

  /**
   * Returns the type of the given term <code>t</code>.
   *
   * @param ctx the initial context
   * @param t   the given term
   * @return    the computed type
   */
  def typeof(ctx: Context, t: Term)(logger: Logger): (Type, Effect) = t match {
    case True | False =>
      logger.logCustom("T-Bool")
      (TypeBool, EffectBot)
    case Zero =>
      logger.logCustom("T-Zero")
      (TypeNat, EffectBot)
    case Succ(nv) =>
      logger.logCustom("T-Succ")
      val (tp, eff) = typeof(ctx, nv)(logger.indent)
      if (TypeNat == tp) (TypeNat, eff)
      else throw TypeError(t.pos, "numeric type expected")
    case Pred(nv) =>
      logger.logCustom("T-Pred")
      val (tp, eff) = typeof(ctx, nv)(logger.indent)
      if (TypeNat == tp) (TypeNat, eff)
      else throw TypeError(t.pos, "numeric type expected")
    case IsZero(nv) =>
      logger.logCustom("T-IsZero")
      val (tp, eff) = typeof(ctx, nv)(logger.indent)
      if (TypeNat == tp) (TypeBool, eff)
      else throw TypeError(t.pos, "numeric type expected")
    case If(cond, t1, t2) =>
      logger.logCustom("T-If")
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
      logger.logCustom("T-Var ("+ y +")")
      ctx.vals.get(y) match {
        case Some(tp) =>
          val res = (tp, EffectBot)
//          logger.log(ctx, t, res)
          res
        case None =>
          throw TypeError(t.pos, "undefined variable \'" + y + "'")
      }

    case Let(x, tp, t1, t2) =>
      checkType(ctx, tp)
      val (tp1, eff1) = typeof(ctx, t1)(logger.indent)
      logger.indent.logCustom(tp1 +"  <:  "+ tp)
      if (isSub(ctx, tp1, tp)) {
        val ctx1 = Context(ctx.vals + (x -> tp), ctx.delayed)
        logger.logCustom("let "+ x +" = ...")
        typeof(ctx1, t2)(logger.indent)
      } else throw TypeError(t.pos, 
             "let type mismatch: expected " + tp + ", found " + tp1)
      
    case Abs(x, tp, poly, t1) =>
      checkType(ctx, tp)
      val ctx1 = Context(ctx.vals + (x -> tp), ctx.delayed ++ poly)
      for (f <- poly) {
        checkFunType(ctx1, f, t.pos)
      }
      val (tp2, eff) = typeof(ctx1, t1)(logger.indent)
      val res = (TypeFun(x, tp, poly, eff, tp2), EffectBot)
      logger.logCustom("-- typing rule: mono abs --")
      logger.log(ctx, t, res)
      res
      
    case App(Var(x), t) if ctx.delayed(x) =>
      typeof(ctx, Var(x))(logger.indent) match {
        case (TypeFun(y, tp1, poly, eff, tp), EffectBot) =>
          val (tp2, eff2) = typeof(ctx, t)(logger.indent)
          logger.indent.logCustom(tp2 +"  <:  "+ tp1)
          if (isSub(ctx, tp2, tp1)) {
            (substX(tp, y, tp2), eff2)
          } else throw TypeError(t.pos, 
                 "parameter type mismatch: expected " + tp1 + ", found " + tp2)

        case tp =>
          throw TypeError(t.pos, "expected: function type\nfound: " + tp)
      }

    case App(t1, t2) =>
      typeof(ctx, t1)(logger.indent) match {
        case (TypeFun(x, tp1, poly, eff, tp), eff1) =>
          val (tp2, eff2) = typeof(ctx, t2)(logger.indent)
          logger.indent.logCustom(tp2 +"  <:  "+ tp1)
          if (isSub(ctx, tp2, tp1)) {
            val resTp = substX(tp, x, tp2)

            val t2Var = t2 match {
              case Var(y) => Some(y)
              case _ => None
            }
            val effp = poly.map(f => {
              if (ctx.delayed(f)) EffectBot
              else if (f == x && t2Var.isDefined && ctx.delayed(t2Var.get)) EffectBot
              else if (f == x) latent(tp2, ctx)
              else ctx.vals.get(f) match {
                case Some(tpf) => latent(tpf, ctx)
                case None => throw new TypeError(t.pos, "undefined parameter name "+ f +
                             " when expanding polymorphic effect of type "+ tp1)
              }
            }).foldRight(EffectBot: Effect)((e1, e2) => e1.join(e2))
            
            val res = (resTp, eff1.join(eff2).join(eff).join(effp))
            logger.logCustom("-- typing rule: app --")
            logger.log(ctx, t, res)
            res
          } else throw TypeError(t.pos, 
                 "parameter type mismatch: expected " + tp1 + ", found " + tp2)

        case tp =>
          throw TypeError(t.pos, "expected: function type\nfound: " + tp)
      }
    case Paar(t1, t2) =>
      logger.logCustom("T-Paar")
      val (tp1, eff1) = typeof(ctx, t1)(logger.indent)
      val (tp2, eff2) = typeof(ctx, t2)(logger.indent)
      (TypePaar(tp1, tp2), eff1.join(eff2))
    case First(t) =>
      logger.logCustom("T-Fst")
      val (tp, eff) = typeof(ctx, t)(logger.indent)
      tp match {
        case TypePaar(tp1, tp2) =>
          (tp1, eff)
        case _ =>
          throw TypeError(t.pos, "pair type expected but " + tp + " found")
      }
    case Second(t) =>
      logger.logCustom("T-Snd")
      val (tp, eff) = typeof(ctx, t)(logger.indent)
      tp match {
        case TypePaar(tp1, tp2) =>
          (tp2, eff)
        case _ =>
          throw TypeError(t.pos, "pair type expected but " + tp + " found")
      }
  }
  
  def checkType(ctx: Context, tp: Type): Unit = tp match {
    case TypeFun(x, t1, poly, eff, t2) =>
      val ctx1 = Context(ctx.vals + (x -> tp), ctx.delayed ++ poly)
      for (f <- poly) {
        checkFunType(ctx1, f, tp.pos)
      }
      checkType(ctx, t1)
      checkType(ctx1, t2)
      
    case TypePaar(t1, t2) =>
      checkType(ctx, t1)
      checkType(ctx, t2)
      
    case _ =>
      ()
  }
  
  def checkFunType(ctx: Context, f: String, pos: Position) = ctx.vals.get(f) match {
    case Some(tp) => tp match {
      case TypeFun(_, _, _, _, _) => ()
      case _ => throw new TypeError(pos,
                "Parameter "+ f +" does not have a function type, but"+ tp)
     }
    case None =>
      throw TypeError(pos, "undefined variable \'" + f + "'")
  }




  def substX(tp: Type, x: String, tpx: Type): Type = {
    def doSubst(tp: Type, x: String, polyx: List[String], effx: Effect): Type = tp match {
      case TypeFun(y, t1, poly, eff, t2) if (y == x) =>
        TypeFun(y, doSubst(t1, x, polyx, effx), poly, eff, t2)
      
      case TypeFun(y, t1, poly, eff, t2) if (y != x) =>
        val resPoly = if (poly.contains(x)) (poly.filterNot(_ == x) ::: polyx).distinct else poly
        val resEff  = if (poly.contains(x)) eff.join(effx) else eff
        TypeFun(y, doSubst(t1, x, polyx, effx), resPoly, resEff, doSubst(t2, x, polyx, effx))
        
      case TypePaar(tp1, tp2) =>
        TypePaar(doSubst(tp1, x, polyx, effx), doSubst(tp2, x, polyx, effx))
        
      case tp => tp
    }

    tpx match {
      case TypeFun(y, ta, poly, eff, tb) =>
        doSubst(tp, x, poly, eff)
      case _ =>
        tp
    }
  } 

  def substX(tp: Type, x: String, x1: String): Type = tp match {
    case TypeFun(y, t1, poly, eff, t2) if (y == x) =>
      TypeFun(y, substX(t1, x, x1), poly, eff, t2)

    case TypeFun(y, t1, poly, eff, t2) if (y != x) =>
      val resPoly = poly map {
        case f if f == x => x1
        case f => f
      }
      TypeFun(y, substX(t1, x, x1), resPoly, eff, substX(t2, x, x1))
        
    case TypePaar(tp1, tp2) =>
      TypePaar(substX(tp1, x, x1), substX(tp2, x, x1))
        
    case tp => tp
  }
  
  def latent(tp: Type, ctx: Context): Effect = tp match {
    case TypeFun(x, t1, poly, eff, t2) =>
      val effp = poly.map(f => {
        if (ctx.delayed(f)) EffectBot
        else latent((ctx.vals + (x -> t1))(f), ctx)
      }).foldRight(EffectBot: Effect)((e1, e2) => e1.join(e2))
      eff.join(effp)
      
    case _ =>
      throw new TypeError(tp.pos, "function type expected but " + tp + " found")
  }


  // subtyping
  
  def isSub(ctx: Context, tpa: Type, tpb: Type): Boolean = (tpa, tpb) match {
    case (TypeBool, TypeBool) => true
    case (TypeNat, TypeNat) => true

    case (TypePaar(at1, at2), TypePaar(bt1, bt2)) =>
      isSub(ctx, at1, bt1) && isSub(ctx, at2, bt2)

    case (TypeFun(ax, at1, apoly, aeff, at2), TypeFun(bx, bt1, bpoly, beff, bt2)) =>
      def mapAPoly(f: String) = if (f == ax) bx else f
      val mappedBT2 = substX(bt2, bx, ax)
      
      isSub(ctx, bt1, at1) &&
      subEff(aeff, beff) &&
      // apoly.map(mapAPoly).toSet.subsetOf(bpoly.toSet) &&
      apoly.forall(f => bpoly.contains(mapAPoly(f)) ||
                        subEff(latent((ctx.vals + (ax -> at1))(f), ctx.copy(delayed = Set())), beff)) &&
      isSub(ctx.copy(vals = ctx.vals + (ax -> at1)), at2, mappedBT2)

    case _ =>
      false
  }
  
  def subEff(e1: Effect, e2: Effect): Boolean = (e1, e2) match {
    case (EffectBot, _) | (_, EffectTop) => true
    case (EffectTop, _) | (_, EffectBot) => false
    case (EffectSet(s1), EffectSet(s2)) => s1.subsetOf(s2)
  }
}

case class Context(vals: Map[String, Type], delayed: Set[String]) {
  override def toString() = {
    vals.map(kv => kv._1 +":"+ kv._2).mkString("{",", ","}") + " ; " + delayed.mkString("{", ", ", "}")
  }
}

object Context {
  def empty = apply(Map(), Set())
}
