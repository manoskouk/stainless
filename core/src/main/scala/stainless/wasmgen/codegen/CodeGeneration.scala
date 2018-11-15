package stainless
package wasmgen
package codegen

import intermediate.{trees => t}
import wasm.{LocalsHandler, GlobalsHandler}
import wasm.Expressions.{eq => EQ, _}
import wasm.Types._ 

trait CodeGeneration {
  protected type LH = LocalsHandler
  protected type S  = t.Symbols

  protected val gh: GlobalsHandler

  protected def mkRecord(recordType: t.RecordType, exprs: Seq[Expr])(implicit s: S, lh: LH): Expr
  protected def mkRecordSelector(expr: Expr, rt: t.RecordType, id: Identifier)(implicit s: S, lh: LH): Expr
  protected def mkFunctionPointer(id: Identifier)(implicit s: S, lh: LH): Expr
  protected def mkCastDown(expr: Expr, subType: t.RecordType)(implicit s: S, lh: LH): Expr
  protected def mkCastUp(expr: Expr, superType: t.RecordType)(implicit s: S, lh: LH): Expr
  protected def mkNewArray(length: Expr, base: Type, init: Option[Expr])(implicit s: S, lh: LH): Expr
  protected def mkArrayGet(expr: Expr, expr1: Expr)(implicit s: S, lh: LH): Expr
  protected def mkArraySet(expr: Expr, expr1: Expr, expr2: Expr)(implicit s: S, lh: LH): Expr
  protected def mkArrayLength(expr: Expr)(implicit s: S, lh: LH): Expr
  protected def mkArrayCopy(expr: Expr, expr1: Expr, expr2: Expr, expr3: Expr)(implicit s: S, lh: LH): Expr
  protected def mkApplication(expr: Expr, exprs: Seq[Expr])(implicit s: S, lh: LH): Expr
  protected def mkUnbox0(e: Expr, tpe: Type)(implicit s: S, lh: LH): Expr
  protected def mkBox0(expr: Expr, tpe: Type)(implicit s: S, lh: LH): Expr
  final protected def mkUnbox(from: t.Type, to: t.Type, expr: Expr)(implicit s: S, lh: LH): Expr = {
    if (from.isInstanceOf[t.TypeParameter] && !to.isInstanceOf[t.TypeParameter]) mkUnbox0(expr, transform(to))
    else expr
  }
  final protected def mkBox(from: t.Type, to: t.Type, expr: Expr)(implicit s: S, lh: LH): Expr = {
    if (!from.isInstanceOf[t.TypeParameter] && to.isInstanceOf[t.TypeParameter]) mkBox0(expr, transform(from))
    else expr
  }

  final protected def typeToSign(tpe: t.Typed)(implicit s: t.Symbols): Sign = {
    tpe.getType match {
      case t.BVType(false, _) => Unsigned
      case _ => Signed
    }
  }

  final protected def typeToOp(tpe: t.Typed, intOp: Sign => BinOp, floatOp: BinOp)(implicit s: t.Symbols): BinOp = {
    tpe.getType match {
      case t.RealType() => floatOp
      case t.BVType(false, _) => intOp(Unsigned)
      case _ => intOp(Signed)
    }
  }

  final protected def typeToZero(tpe: Type): Expr = tpe match {
    case `i32` => I32Const(0)
    case `i64` => I64Const(0)
    case `f32` => F32Const(0)
    case `f64` => F64Const(0)
  }

  final protected def mkBin(op: BinOp, lhs: t.Expr, rhs: t.Expr)(implicit s: S, lh: LH): Expr = {
    Binary(op, transform(lhs.getType), transform(lhs), transform(rhs))
  }

  def transform(tpe: t.Type)(implicit s: t.Symbols): Type

  final def transform(expr: t.Expr)(implicit s: S, lh: LH): Expr = expr match {
    case t.NoTree(tpe) =>
      Unreachable
    case t.Variable(id, tpe, flags) =>
      GetLocal(id.uniqueName)
    case t.Let(vd, value, body) =>
      lh.getFreshLocal(vd.id.uniqueName, transform(vd.getType))
      Sequence(Seq(
        SetLocal(vd.id.uniqueName, transform(value)),
        transform(body)
      ))
    case t.Output(msg) => ???
    case fi@t.FunctionInvocation(id, tps, args) =>
      val trArgs = args.zip(s.lookupFunction(id).get.params) map { case (arg, formal) =>
        mkBox(arg.getType, formal.getType, transform(arg))
      }
      mkUnbox(
        s.lookupFunction(id).get.returnType,
        fi.getType,
        Call(id.uniqueName, transform(fi.getType), trArgs)
      )
    case t.IfExpr(cond, thenn, elze) =>
      If(
        FreshIdentifier("label").uniqueName,
        transform(thenn.getType),
        transform(cond),
        transform(thenn),
        transform(elze)
      )
    case t.Equals(lhs, rhs) =>
      mkBin(EQ, lhs, rhs)
      // FIXME This is only ref. equality

    case t.Record(tpe, fields) =>
      val formals = tpe.getRecord.definition.flattenFields
      mkRecord(tpe, fields.zip(formals) map { case (fd, formal) =>
        mkBox(fd.getType, formal.getType, transform(fd))
      })
    case rs@t.RecordSelector(record, selector) =>
      val rt = record.getType.asInstanceOf[t.RecordType]
      val realType = rs.getType
      val formalType = rt
        .getRecord.definition
        .flattenFields.find(_.id == selector).get
        .getType
      mkUnbox(formalType, realType,
        mkRecordSelector(transform(record), rt, selector)
      )
    case t.FunctionPointer(id) =>
      mkFunctionPointer(id)
    case t.Application(callee, args) =>
      mkApplication(transform(callee), args map transform)

    case t.CastDown(e, subtype) =>
      mkCastDown(transform(e), subtype)
    case t.CastUp(e, supertype) =>
      mkCastUp(transform(e), supertype)

    case t.NewArray(length, base, init) =>
      mkNewArray(transform(length), transform(base), init map transform)
    case t.ArrayGet(array, index) =>
      mkArrayGet(transform(array), transform(index))
    case t.ArraySet(array, index, value) =>
      mkArraySet(transform(array), transform(index), transform(value))
    case t.ArrayLength32(array) =>
      mkArrayLength(transform(array))
    case t.ArrayCopy(from, to, start, end) =>
      mkArrayCopy(transform(from), transform(to), transform(start), transform(end))

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
