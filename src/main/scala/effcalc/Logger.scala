package effcalc

trait Logger {
  def logCustom(msg: String) = ()
  def log(ctx: Context, t: Term, tpEff: (Type, Effect)) = ()
  def indent: Logger
}
  
case object NoLogger extends Logger {
  def indent = this
}
  
case class ConsoleLogger(ind: Int) extends Logger {
  override def logCustom(msg: String) = println(msg)
  override def log(ctx: Context, t: Term, tpEff: (Type, Effect)) {
    print((1 to ind) map (_ => " ") mkString)
    print(ctx)
    print(" ⊢ ")
    print(t)
    print(" : ")
    print(tpEff._1)
    print(" ! ")
    println(tpEff._2)
  }
  def indent = ConsoleLogger(ind + 2)
}
 
class Node {
  private var text: List[String] = Nil
  def addText(l: String) {
    text ::= l
  }
  def label = text.reverse.mkString("\\l")
    
  private var children: List[Node] = Nil
  def newChild: Node = {
    val n = new Node
    children ::= n
    n
  }
  def childs = children
}
  
case class DotFileLogger(graph: Node) extends Logger {
  
  def escape(str: String) =
    str.replaceAllLiterally("\\", "\\\\").replaceAllLiterally("\n", "\\l")
  
  def indent = new DotFileLogger(graph.newChild)

  override def logCustom(msg: String) = graph.addText(escape(msg))
  override def log(ctx: Context, t: Term, tpEff: (Type, Effect)) {
    val txt = ctx +"\n   ⊢ "+ t +"\n   : "+ tpEff._1 +" ! "+ tpEff._2 +"\n"
    graph.addText(escape(txt))
  }
    
  def writeDot(filename: String) {
    val writer = new java.io.FileWriter(filename)
    var nodeCount = 0
    def write(n: Node): Int = {
      nodeCount += 1
      val num = nodeCount
      writer.write("  n"+ num +" [label=\""+ n.label +"\"]\n")
      for (child <- n.childs) {
        val cNum = write(child)
        writer.write("  n"+ num +" -> n"+ cNum +"\n")
      }
      num
    }
    writer.write("digraph G {\n  node [fontname=Courier,shape=plaintext,style=filled,color=\"0 0 0.9\"]\n")
    write(graph)
    writer.write("}\n")
    writer.close()
  }
}
