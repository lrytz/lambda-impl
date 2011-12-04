package effcalc

object Interpreter {
  import scala.collection.immutable.{Set, ListSet}
  private val emptySet = ListSet.empty[String]

  /** Computes free variables of term <code>t</code>
   *  (see definition 5.3.2 in TAPL book).
   *
   *  @param t ...
   *  @return  the set of free variables present in term <code>t</code>.
   */
  def freeVars(t: Term): Set[String] = t match {
    case True | False => emptySet
    case Zero => emptySet
    case Succ(t) => freeVars(t)
    case Pred(t) => freeVars(t)
    case IsZero(t) => freeVars(t)
    case If(c, t1, t2) => freeVars(c) ++ freeVars(t1) ++ freeVars(t2)
    // lambda terms
    case Var(n) => emptySet + n
    case Let(x, _, t1, t2) => freeVars(t1) ++ (freeVars(t2) - x)
    case AbsM(x, _, t1) => freeVars(t1) - x
    case AbsP(x, _, t1) => freeVars(t1) - x
    case App(t1, t2) => freeVars(t1) ++ freeVars(t2)
    // pairs
    case Paar(t1, t2) => freeVars(t1) ++ freeVars(t2)
    case First(t1) => freeVars(t1)
    case Second(t2) => freeVars(t2)
  }

  /** <p>
   *    Alpha conversion: term <code>t</code> should be a lambda abstraction
   *    <code>\x. t</code>.
   *  </p>
   *  <p>
   *    All free occurences of <code>x</code> inside term <code>t/code>
   *    will be renamed to a unique name.
   *  </p>
   *
   *  @param t the given lambda abstraction.
   *  @return  the transformed term with bound variables renamed.
   */
  def alpha(t: Term): Term = {
    val (x, tp, t1, cons) = t match {
      case AbsM(x, tp, t1) => (x, tp, t1, AbsM(_, _, _))
      case AbsP(x, tp, t1) => (x, tp, t1, AbsP(_, _, _))
      case Let(x, tp, t1, t2) => (x, tp, t2, (x: String, tp: Type, t2: Term) => Let(x, tp, t1, t2))
    }
    val x1 = fresh(x)

    def alphaconv(t: Term): Term = t match {
      case Var(n) if (x == n) => Var(x1)
      case App(t1, t2) => App(alphaconv(t1), alphaconv(t2))
      case AbsM(v, tp, t1) if (v != x) => AbsM(v, tp, alphaconv(t1))
      case AbsP(v, tp, t1) if (v != x) => AbsP(v, tp, alphaconv(t1))
      case Let(v, tp, t1, t2) => {
        if (v != x) Let(v, tp, t1, alphaconv(t2))
        else Let(v, tp, t1, t2)
      }
      case _ => t
    }

    cons(x1, tp, alphaconv(t1))
  }

  import scala.collection.mutable.HashMap
  val freshNames = new HashMap[String, Int]

  /** Returns a unique name with the given prefix.
   *
   *  @param s the given name prefix
   *  @return  the unique name
   */
  private def fresh(s: String): String = freshNames.get(s) match {
    case Some(n) => freshNames(s) = n + 1; s + n
    case None    => freshNames(s) = 1; s + "1"
  }

  /** Straight forward substitution method
   *  (see definition 5.3.5 in TAPL book).
   *  [x -> s]t
   *
   *  @param t the term in which we perform substitution
   *  @param x the variable name
   *  @param s the term we replace x with
   *  @return  ...
   */
  def subst(t: Term, x: String, s: Term): Term = t match {
    case True | False =>
      t
    case Zero =>
      t
    case Succ(t1) =>
      Succ(subst(t1, x, s))
    case Pred(t1) =>
      Pred(subst(t1, x, s))
    case IsZero(t1) =>
      IsZero(subst(t1, x, s))
    case If(c, t1, t2) =>
      If(subst(c, x, s), subst(t1, x, s), subst(t2, x, s))
    // lambda terms
    case Var(y) =>
      if (y == x) s else t
    
    case Let(y, tp, t1, t2) =>
      if (y == x)
        Let(y, tp, subst(t1, x, s), t2)
      else if (freeVars(s)(y))
        subst(alpha(t), x, s)
      else
        Let(y, tp, subst(t1, x, s), subst(t2, x, s))
      
    case AbsM(y, tp, t1) =>
      if (y == x)
        t
      else if (freeVars(s)(y))
        subst(alpha(t), x, s)
      else
        AbsM(y, tp, subst(t1, x, s))
    case AbsP(y, tp, t1) =>
      if (y == x)
        t
      else if (freeVars(s)(y))
        subst(alpha(t), x, s)
      else
        AbsP(y, tp, subst(t1, x, s))
    case App(t1, t2) =>
      App(subst(t1, x, s), subst(t2, x, s))
    // pairs
    case Paar(t1, t2) =>
      Paar(subst(t1, x, s), subst(t2, x, s))
    case First(t1) =>
      First(subst(t1, x, s))
    case Second(t1) =>
      Second(subst(t1, x, s))
  }

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  
  /** Is the given term a numeric value? */
  def isNumericVal(t: Term): Boolean = t match {
    case Zero => true
    case Succ(t) => isNumericVal(t)
    case _ => false
  }

  /** Is the given term a value? */
  def isValue(t: Term): Boolean = t match {
    case True | False => true
    case t if isNumericVal(t) => true
    case AbsM(_, _, _) => true
    case AbsP(_, _, _) => true
    case Paar(t1, t2) => isValue(t1) & isValue(t2)
    case _ => false
  }

  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
    case Succ(t) => Succ(reduce(t))
    case Pred(Zero) => Zero
    case Pred(Succ(nv)) if isNumericVal(nv) => nv
    case Pred(t) => Pred(reduce(t))
    case IsZero(Zero) => True
    case IsZero(Succ(nv)) if isNumericVal(nv) => False
    case IsZero(t) => IsZero(reduce(t))
    case If(True, t1, _)  => t1
    case If(False, _, t2) => t2
    case If(cond, t1, t2) =>
      If(reduce(cond), t1, t2)
      
    case Let(x, tp, v1, t2) if isValue(v1) =>
      subst(t2, x, v1)
    case Let(x, tp, t1, t2) =>
      Let(x, tp, reduce(t1), t2)
      
    // lambda terms
    case App(AbsM(x, _, t1), v2) if isValue(v2) =>
      subst(t1, x, v2)
    case App(AbsP(x, _, t1), v2) if isValue(v2) =>
      subst(t1, x, v2)
    case App(v1, t2) if isValue(v1) =>
      App(v1, reduce(t2))
    case App(t1, t2) =>
      App(reduce(t1), t2)
    // pairs
    case Paar(v1, t2) if isValue(v1) =>
      Paar(v1, reduce(t2))
    case Paar(t1, t2) =>
      Paar(reduce(t1), t2)
    case First(Paar(v1, v2)) if isValue(v1) && isValue(v2) =>
      v1
    case Second(Paar(v1, v2)) if isValue(v1) && isValue(v2) =>
      v2
    case First(t) => First(reduce(t))
    case Second(t) => Second(reduce(t))
    case _ =>
      throw NoRuleApplies(t)
  }


  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoRuleApplies(_) =>
        Stream.cons(t, Stream.empty)
    }
}