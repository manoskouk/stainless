/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasm

trait Printer extends stainless.ast.Printer {
  protected val trees: Trees
  import trees._
  override protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case Hole(tpe) => p"???[$tpe]" // FIXME: We may want to print path to anvil library hole
    case Guide(e) => p"⊙{$e}"
    case Terminating(fi) => p"↓$fi"
    case Hint(e) => p"hint($e)"
    case Inactive(i) => p"inactive($i)"
    case _ => super.ppBody(tree)
  }
}