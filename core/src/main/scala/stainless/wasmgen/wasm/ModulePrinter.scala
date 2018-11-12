package stainless.wasmgen.wasm

import scala.language.implicitConversions
import Expressions._

// Printer for Wasm modules
object ModulePrinter {
  private implicit def s2d(s: String) = Raw(s)

  private def mkMod(mod: Module): Document = Stacked(
    "(module ",
    Indented(Stacked(mod.imports map mkImport)),
    Indented("(global (mut i32) i32.const 0) " * mod.globals),
    Indented(Stacked(mod.functions map mkFun)),
    ")"
  )

  private def mkImport(s: String): Document =
    Lined(List("(import ", s, ")"))

  private def mkFun(fh: Function): Document = {
    val Function(name, args, returnType, locals, body) = fh
    val exportDoc: Document = s"""(export "$name" (func $$$name))"""
    val paramsDoc: Document = if (args.isEmpty) "" else {
      Lined(List(
        "(param ",
        Lined(args.toList map (arg => Raw(arg.toString)), " "),
        ") "
      ))
    }
    val resultDoc: Document = s"(result $returnType) "
    val localsDoc: Document =
      if (locals.nonEmpty)
        "(local " <:> Lined(locals.toList map (l => Raw(l.toString)), " ") <:> ")"
      else
        ""

    Stacked(
      exportDoc,
      Lined(List(s"(func $$$name ", paramsDoc, resultDoc, localsDoc)),
      Indented(Stacked(mkExpr(body))),
      ")"
    )
  }


  private def mkExpr(expr: Expr): Document = {
    expr match {
      case Binary(op, tpe, lhs, rhs) =>
        Stacked(
          s"($tpe.$op",
          Indented(mkExpr(lhs)),
          Indented(mkExpr(rhs)),
          ")"
        )
      case Unary(op, tpe, e) =>
        Stacked(
          s"($tpe.$op",
          Indented(mkExpr(e)),
          ")"
        )
      case I32Const(value) => s"(i32.const $value)"
      case I64Const(value) => s"(i64.const $value)"
      case F32Const(value) => s"(f32.const $value)"
      case F64Const(value) => s"(f64.const $value)"
      case If(label, tpe, cond, thenn, elze) =>
        Stacked(
          s"(if $label $tpe",
          Indented(mkExpr(cond)),
          Indented(mkExpr(thenn)),
          Indented(mkExpr(elze)),
          ")"
        )
      case Loop(label, tpe, body) =>
        Stacked(
          s"(loop $label $tpe",
          Indented(mkExpr(body)),
          ")"
        )
      case Branch(label, tpe, body) =>
        Stacked(
          s"(branch $label $tpe",
          Indented(mkExpr(body)),
          ")"
        )
      case Br(label) => s"(br $label)"
      case Call(name, args) =>
        Stacked(
          s"(call $name",
          Indented(Stacked(args map mkExpr: _*)),
          ")"
        )
      case Return => "return"
      case Unreachable => "unreachable"
      case GetLocal(index)  => s"(get_local $index)"
      case GetGlobal(index) => s"(get_global $index)"
      case Extend(to, from, sign, e) =>
        Stacked(
          s"($to.extend_$sign/$from",
          Indented(mkExpr(e)),
          ")"
        )
      case Wrap(to, from, e) =>
        Stacked(
          s"($to.wrap/$from",
          Indented(mkExpr(e)),
          ")"
        )
      case Sequence(es) =>
        Stacked(
          "(",
          Indented(Stacked(es map mkExpr : _*)),
          ")"
        )
    }

  }

  def apply(mod: Module) = mkMod(mod).print
  def apply(fh: Function) = mkFun(fh).print
  def apply(expr: Expr) = mkExpr(expr).print

}
