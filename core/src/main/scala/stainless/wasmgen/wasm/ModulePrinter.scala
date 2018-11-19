package stainless.wasmgen.wasm

import scala.language.implicitConversions
import Expressions._
import Definitions._

// Printer for Wasm modules
object ModulePrinter {
  private implicit def s2d(s: String) = Raw(s)

  private def mkMod(mod: Module): Document = ??? /*Stacked(
    "(module ",
    Indented(Stacked(mod.imports map mkImport)),
    Indented("(global (mut i32) i32.const 0) " * mod.globals),
    Indented(Stacked(mod.functions map mkFun)),
    ")"
  )*/

  private def mkImport(s: String): Document =
    Lined(List("(import ", s, ")"))

  private def mkFun(fh: FunDef): Document = {
    val FunDef(name, args, returnType, locals, body) = fh
    val exportDoc: Document = s"""(export "$name" (func $$$name))"""
    val paramsDoc: Document =
      Lined(args.toList map { case ValDef(name, tpe) =>
        Raw(s"(param $$$name $tpe) ")
      })
    val resultDoc: Document = s"(result $returnType) "
    val localsDoc: Document = 
      Lined(locals.toList map { case ValDef(name, tpe) =>
        Raw(s"(local $$$name $tpe) ")
      })

    Stacked(
      exportDoc,
      Lined(List(s"(func $$$name ", paramsDoc, resultDoc, localsDoc)),
      Indented(Stacked(mkExpr(body))),
      ")"
    )
  }


  private def mkExpr(expr: Expr): Document = {
    expr match {
      case Binary(op, lhs, rhs) =>
        Stacked(
          s"(${expr.getType}.$op",
          Indented(mkExpr(lhs)),
          Indented(mkExpr(rhs)),
          ")"
        )
      case Unary(op, e) =>
        Stacked(
          s"(${expr.getType}.$op",
          Indented(mkExpr(e)),
          ")"
        )
      case I32Const(value) => s"(i32.const $value)"
      case I64Const(value) => s"(i64.const $value)"
      case F32Const(value) => s"(f32.const $value)"
      case F64Const(value) => s"(f64.const $value)"
      case If(label, cond, thenn, elze) =>
        Stacked(
          s"(if $$$label ${expr.getType}",
          Indented(mkExpr(cond)),
          Indented(mkExpr(thenn)),
          Indented(mkExpr(elze)),
          ")"
        )
      case Loop(label, body) =>
        Stacked(
          s"(loop $$$label ${expr.getType}",
          Indented(mkExpr(body)),
          ")"
        )
      case Branch(label, body) =>
        Stacked(
          s"(branch $$$label ${expr.getType}",
          Indented(mkExpr(body)),
          ")"
        )
      case Br(label) => s"(br $$$label)"
      case Br_If(label, cond) =>
        Stacked(
          s"(br_if $$$label",
          Indented(mkExpr(cond)),
          ")"
        )
      case Call(name, _, args) =>
        Stacked(
          s"(call $$$name",
          Indented(Stacked(args map mkExpr: _*)),
          ")"
        )
      case Call_Indirect(_, fun, args) =>
        Stacked(
          "(call_indirect",
          Indented(Stacked( (fun +: args) map mkExpr: _*)),
          ")"
        )
      case Load(tpe, truncate, expr) =>
        val ts = truncate match {
          case Some((tpe, sign)) => s"${tpe}_$sign"
          case None => ""
        }
        Stacked(
          s"($tpe.load$ts",
          Indented(mkExpr(expr)),
          ")"
        )
      case Store(truncate, address, value) =>
        val ts = truncate.map(_.bitSize.toString).getOrElse("")
        Stacked(
          s"(${expr.getType}.store$ts",
          Indented(mkExpr(address)),
          Indented(mkExpr(value))
        )
      case Return => "return"
      case Unreachable => "unreachable"
      case Drop => "drop"
      case GetLocal(label)  => s"(get_local $$$label)"
      case SetLocal(label, value) =>
        Stacked(
          s"(set_local $$$label",
          Indented(mkExpr(value)),
          s")"
        )
      case GetGlobal(label) => s"(get_global $$$label)"
      case SetGlobal(label, value) =>
        Stacked(
          s"(set_global $$$label",
          Indented(mkExpr(value)),
          s")"
        )
      case Extend(to, sign, e) =>
        Stacked(
          s"($to.extend_$sign/${expr.getType}",
          Indented(mkExpr(e)),
          ")"
        )
      case Wrap(to, e) =>
        Stacked(
          s"($to.wrap/${expr.getType}",
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
  def apply(fh: FunDef) = mkFun(fh).print
  def apply(expr: Expr) = mkExpr(expr).print

}
