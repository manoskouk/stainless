/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasm

trait Printer extends stainless.ast.Printer {
  protected val trees: Trees
  import trees._
  override protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case Record(tpe, fields) => p"new struct[$tpe]($fields)"

    case FunctionPointer(id) => p"$id"

    case CastDown(e, tp) => p"$e.asInstanceOf[$tp]"

    case CastUp(e, tp) => p"$e.asInstanceOf[$tp]"

    case _ => super.ppBody(tree)
  }
}