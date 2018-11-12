package stainless
package wasmgen
package codegen

import intermediate.{trees => t}
import stainless.wasmgen.wasm.LocalsHandler
import wasm.Expressions._
import wasm.Types._

trait CodeGeneration {
  def mkRecord(recordType: t.RecordType, exprs: Seq[t.Expr]): Expr
  def mkRecordSelector(expr: t.Expr, id: Identifier): Expr
  def mkFunctionPointer(id: Identifier): Expr
  def mkCastDown(expr: t.Expr, subType: t.RecordType): Expr
  def mkCastUp(expr: t.Expr, superType: t.RecordType): Expr
  def mkNewArray(length: t.Expr, base: t.Type, init: Option[t.Expr]): Expr
  def mkUnbox0(e: Expr, tpe: Type): Expr
  final def mkUnbox(from: t.Type, to: t.Type, expr: Expr): Expr = {
    if (from.isInstanceOf[t.TypeParameter] && !to.isInstanceOf[t.TypeParameter]) mkUnbox0(expr, transform(to))
    else expr
  }
  final def mkBox(from: t.Type, to: t.Type, expr: Expr): Expr = {
    if (!from.isInstanceOf[t.TypeParameter] && to.isInstanceOf[t.TypeParameter]) mkBox0(expr, transform(from))
    else expr
  }
  def mkBox0(expr: Expr, tpe: Type): Expr

  def transform(tpe: t.Type)(implicit s: t.Symbols): Type

  def typeToSign(tpe: t.Typed)(implicit s: t.Symbols): Sign = {
    tpe.getType match {
      case t.BVType(false, _) => Unsigned
      case _ => Signed
    }
  }

  def typeToOp(tpe: t.Typed, intOp: Sign => BinOp, floatOp: BinOp)(implicit s: t.Symbols): BinOp = {
    tpe.getType match {
      case t.RealType() => floatOp
      case t.BVType(false, _) => intOp(Unsigned)
      case _ => intOp(Signed)
    }
  }

  def typeToZero(tpe: Type): Expr = tpe match {
    case i32 => I32Const(0)
    case i64 => I64Const(0)
    case f32 => F32Const(0)
    case f64 => F64Const(0)
  }

  final def mkBin(op: BinOp, lhs: t.Expr, rhs: t.Expr): Expr = {
    Binary(op, transform(lhs.getType), transform(lhs), transform(rhs))
  }

  final def mkBin(op: UnOp, e: t.Expr): Expr = {
    Unary(op, transform(e.getType), transform(e))
  }

  def transform(expr: t.Expr)(implicit s: t.Symbols, lh: LocalsHandler[Identifier]): Expr = expr match {
    case t.NoTree(tpe) =>
      Unreachable
    case t.Variable(id, tpe, flags) =>
      GetLocal(lh.getLocal(id))
    case t.Let(vd, value, body) =>
      val local = lh.getFreshLocal(vd.id, transform(vd.getType))
      Sequence(Seq(Unary(SetLocal(local), transform(vd.getType), transform(value)), transform(body)))
    case t.Output(msg) => ???
    case fi@t.FunctionInvocation(id, tps, args) =>
      val trArgs = args.zip(s.lookupFunction(id).get.params) map { case (arg, formal) =>
        mkBox(arg.getType, formal.getType, transform(arg))
      }
      mkUnbox(
        s.lookupFunction(id).get.returnType,
        fi.getType,
        Call(id.uniqueName, trArgs)
      )
    case t.IfExpr(cond, thenn, elze) =>
      If(
        FreshIdentifier("label").uniqueName,
        transform(thenn.getType),
        transform(cond),
        transform(thenn),
        transform(elze)
      )
    case t.Equals(lhs, rhs) => ???

    case t.Record(tpe, fields) =>
      mkRecord(tpe, fields)
    case t.RecordSelector(record, selector) =>
      mkRecordSelector(record, selector)

    case t.FunctionPointer(id) =>
      mkFunctionPointer(id)
    case t.Application(callee, args) =>
      mkBox
      mkApplication(callee, args)

    case t.CastDown(e, subtype) =>
      mkCastDown(e, subtype)
    case t.CastUp(e, supertype) =>
      mkCastUp(e, supertype)

    case t.NewArray(length, base, init) =>
      mkNewArray(length, base, init)

    case t.ArrayGet(array, index) =>
    case t.ArraySet(array, index, value) =>
    case t.ArrayLength32(array) =>
    case t.ArrayCopy(from, to, start, end) =>

    case t.Plus(lhs, rhs) =>
      mkBin(add, lhs, rhs)
    case t.Minus(lhs, rhs) =>
      mkBin(sub, lhs, rhs)
    case t.Times(lhs, rhs) =>
      mkBin(mul, lhs, rhs)
    case t.Division(lhs, rhs) =>
      mkBin(typeToOp(lhs, div(_), div), lhs, rhs)
    case t.Remainder(lhs, rhs) =>
      mkBin(rem(typeToSign(lhs)), lhs, rhs) // FIXME
    case t.Modulo(lhs, rhs) =>
      mkBin(rem(typeToSign(lhs)), lhs, rhs) // FIXME
    case t.UMinus(e) =>
      e.getType match {
        case t.RealType() => Unary(neg, f64, transform(e))
        case tpe =>
          Binary(sub, transform(tpe), typeToZero(transform(tpe)), transform(e))
      }
    case t.LessThan(lhs, rhs) =>
      mkBin(typeToOp(lhs, lt(_), lt), lhs, rhs)
    case t.GreaterThan(lhs, rhs) =>
      mkBin(typeToOp(lhs, gt(_), gt), lhs, rhs)
    case t.LessEquals(lhs, rhs) =>
      mkBin(typeToOp(lhs, le(_), le), lhs, rhs)
    case t.GreaterEquals(lhs, rhs) =>
      mkBin(typeToOp(lhs, ge(_), ge), lhs, rhs)

    case t.BVNot(e) =>
      val tpe = transform(e.getType)
      Binary(xor, tpe, typeToZero(tpe), transform(e))
    case t.BVAnd(lhs, rhs) =>
      mkBin(and, lhs, rhs)
    case t.BVOr(lhs, rhs) =>
      mkBin(or, lhs, rhs)
    case t.BVXor(lhs, rhs) =>
      mkBin(xor, lhs, rhs)
    case t.BVShiftLeft(lhs, rhs) =>
      mkBin(shl, lhs, rhs)
    case t.BVAShiftRight(lhs, rhs) =>
      mkBin(shr(Signed), lhs, rhs)
    case t.BVLShiftRight(lhs, rhs) =>
      mkBin(shr(Unsigned), lhs, rhs)
    case t.BVNarrowingCast(expr, newType) =>
      Wrap(transform(newType), transform(expr.getType), transform(expr))
    case t.BVWideningCast(expr, newType) =>
      Extend(transform(newType), transform(expr.getType), typeToSign(expr.getType), transform(expr))
  }

}
