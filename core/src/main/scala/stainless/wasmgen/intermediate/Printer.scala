/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.intermediate

trait Printer extends stainless.ast.Printer {
  protected val trees: Trees
  import trees._
  override protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case Record(tpe, fields) => p"new $tpe($fields)"

    case RecordSelector(record, selector) => p"$record.$selector"

    case FunctionPointer(id) => p"$id"

    case CastDown(e, tp) => p"$e.asInstanceOf[$tp]"

    case CastUp(e, tp) => p"$e.asInstanceOf[$tp]"

    case Output(msg) => p"println($msg)"

    case NewArray(length, base, init) => p"new Array[$base]($length){ ${init.getOrElse("")} }"

    case ArrayCopy(from, to, start, end) =>
      p"Array.copy($from, $to, $start, $end)"

    case RecordType(id, tps) =>
      p"$id${nary(tps, ", ", "[", "]")}"

    case _ => super.ppBody(tree)
  }
}