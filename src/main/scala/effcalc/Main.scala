package effcalc

import scala.util.parsing.input._

import EffCalcParsers._
import Analyzer._
import Interpreter._


object Main extends scala.App {
  val tokens = new lexical.Scanner(StreamReader(new java.io.FileReader("examples/nestNotPrecise2.txt")))
    
  val logger = new DotFileLogger(new Node)

  phrase(Term)(tokens) match {
    case Success(trees, _) =>
      try {
        println("typed: " + typeof(Context.empty, trees)(logger))
        println()
        logger.writeDot("out.dot")
        for (t <- path(trees, reduce))
          println(t)
      } catch {
        case tperror => println(tperror.toString)
        tperror.printStackTrace()
      }
    case e =>
      println(e)
  }
}
