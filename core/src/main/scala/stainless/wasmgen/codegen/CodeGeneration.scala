/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package wasmgen
package codegen

import intermediate.{trees => t}
import wasm._
import Expressions.{eq => EQ, _}
import Types._
import Definitions._

trait CodeGeneration {
  protected type LH = LocalsHandler
  protected type S  = t.Symbols
  protected case class FunEnv(
    s: t.Symbols,
    gh: GlobalsHandler,
    tab: Table
  ) {
    def env(lh: LocalsHandler): Env = Env(s, lh, gh, tab)
  }
  protected case class Env(
    s: t.Symbols,
    lh: LocalsHandler,
    gh: GlobalsHandler,
    tab: Table
  ) {
    def fEnv = FunEnv(s, gh, tab)
  }

  protected def freshLabel(s: String): String = FreshIdentifier(s).uniqueName

  protected def mkImports(symbols: t.Symbols): Seq[Import] = {
    Seq(Import("system", "printString", FunSig("_printString_", Seq(i32), i32)))
  }
  protected def mkGlobals(s: t.Symbols): Seq[ValDef]
  protected def mkTable(s: t.Symbols): Table
  /** Built-in functions */
  protected val refEqualityName = "_ref_eq_"
  protected val refInequalityName = "_ref_ineq_"
  protected def arrayCopyName(tpe: Type) = s"_array_copy_${tpe}_"
  protected def mkEquality(s: t.Symbols): FunDef
  protected def mkInequality(s: t.Symbols): FunDef
  protected def mkArrayCopy(s: t.Symbols, tpe: Type): FunDef
  protected def mkBuiltins(s: t.Symbols): Seq[FunDef] = {
    Seq(mkEquality(s), mkInequality(s)) ++
    Seq(i32, i64, f32, f64).map(mkArrayCopy(s, _))
  }

  protected def mkRecord(recordType: t.RecordType, exprs: Seq[Expr])(implicit env: Env): Expr
  protected def mkRecordSelector(expr: Expr, rt: t.RecordType, id: Identifier)(implicit env: Env): Expr
  protected def mkFunctionPointer(id: Identifier)(implicit env: Env): Expr
  protected def mkCastDown(expr: Expr, subType: t.RecordType)(implicit env: Env): Expr
  protected def mkCastUp(expr: Expr, superType: t.RecordType)(implicit env: Env): Expr
  protected def mkNewArray(length: Expr, base: Type, init: Option[Expr])(implicit env: Env): Expr
  protected def mkArrayGet(array: Expr, base: Type, index: Expr)(implicit env: Env): Expr
  protected def mkArraySet(array: Expr, index: Expr, value: Expr)(implicit env: Env): Expr
  protected def mkArrayLength(expr: Expr)(implicit env: Env): Expr

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

  final protected def mkBin(op: BinOp, lhs: t.Expr, rhs: t.Expr)(implicit env: Env): Expr = {
    op(transform(lhs), transform(rhs))
  }

  protected def isRefType(tpe: t.Type): Boolean = tpe match {
    case t.BVType(_, _) | t.RealType() | t.BooleanType() =>
      false
    case t.RecordType(_) | t.ArrayType(_) =>
      true
  }

  def transform(tpe: t.Type)(implicit s: t.Symbols): Type = tpe match {
    case t.BooleanType() => i32
    case t.RealType() => f64
    case t.BVType(_, size) => if (size == 64) i64 else i32
    case t.ArrayType(_) | t.RecordType(_) =>
      sys.error("Reference types are left abstract " +
        "and have to be implemented in a subclass of wasm CodeGeneration")
  }

  final def transform(s: t.Symbols): Module = {
    val imports = mkImports(s)
    val globals = mkGlobals(s)
    val tab = mkTable(s)
    val funs = mkBuiltins(s) ++ s.functions.values.toList.map(transform(_)(FunEnv(s, GlobalsHandler(globals), tab)))
    Module("program", imports, globals, tab, funs)
  }

  final def transform(fd: t.FunDef)(implicit env: FunEnv): FunDef = {
    implicit val s = env.s
    FunDef(
      fd.id.uniqueName,
      fd.params.map(arg => ValDef(arg.id.uniqueName, transform(arg.tpe))),
      transform(fd.returnType)
    ) { lh =>
      transform(fd.fullBody)(env.env(lh))
    }
  }

  final def transform(expr: t.Expr)(implicit env: Env): Expr = {
    implicit val lh = env.lh
    implicit val s  = env.s
    expr match {
      case t.NoTree(tpe) =>
        Unreachable
      case t.Variable(id, tpe, flags) =>
        val toLook = id.uniqueName
        GetLocal(toLook)
      case t.Let(vd, value, body) =>
        lh.getFreshLocal(vd.id.uniqueName, transform(vd.getType))
        Sequence(Seq(
          SetLocal(vd.id.uniqueName, transform(value)),
          transform(body)
        ))
      case t.Output(msg) =>
        Call("_printString_", i32, Seq(transform(msg)))
      case fi@t.FunctionInvocation(id, tps, Seq(lhs, rhs)) if id.name == "_compare_" =>
        // This is hard-coded inequality and not a normal function.
        if (isRefType(lhs.getType))
          Call(refInequalityName, i32, Seq(transform(lhs), transform(rhs)))
        else
          mkBin(sub, lhs, rhs)
      case fi@t.FunctionInvocation(id, tps, args) =>
        Call(id.uniqueName, transform(fi.getType), args map transform)
      case t.Sequence(es) =>
        Sequence ( es.init.map(e => Drop(transform(e))) :+ transform(es.last) )

      case t.IfExpr(cond, thenn, elze) =>
        If(
          freshLabel("label"),
          transform(cond),
          transform(thenn),
          transform(elze)
        )
      case t.Equals(lhs, rhs) =>
        // Equality is value equality for non-reference types,
        // but we have to invoke the reference equaliry implementation for ref. types
        if (isRefType(lhs.getType))
          Call(refEqualityName, i32, Seq(transform(lhs), transform(rhs)))
        else
          mkBin(EQ, lhs, rhs)

      case bvl@t.BVLiteral(signed, value, size) =>
        if (size <= 32) I32Const(bvl.toBigInt.toInt)
        else I64Const(bvl.toBigInt.toLong)
      case t.BooleanLiteral(value) =>
        I32Const(if (value) 1 else 0)

      case t.Record(tpe, fields) =>
        mkRecord(tpe, fields map transform)
      case rs@t.RecordSelector(record, selector) =>
        val rt = record.getType.asInstanceOf[t.RecordType]
        mkRecordSelector(transform(record), rt, selector)

      case t.FunctionPointer(id) =>
        mkFunctionPointer(id)
      case t.Application(callee, args) =>
        Call_Indirect(
          transform(callee.getType.asInstanceOf[t.FunctionType].to),
          transform(callee),
          args map transform
        )

      case t.CastDown(e, subtype) =>
        mkCastDown(transform(e), subtype)
      case t.CastUp(e, supertype) =>
        mkCastUp(transform(e), supertype)

      case t.NewArray(length, base, init) =>
        mkNewArray(transform(length), transform(base), init map transform)
      case ag@t.ArraySelect(array, index) =>
        mkArrayGet(transform(array), transform(ag.getType), transform(index))
      case t.ArraySet(array, index, value) =>
        mkArraySet(transform(array), transform(index), transform(value))
      case t.ArrayLength(array) =>
        mkArrayLength(transform(array))
      case t.ArrayCopy(from, to, startFrom, startTo, length) =>
        val t.ArrayType(tpe) = from.getType
        val trTpe = transform(tpe)
        Call(arrayCopyName(trTpe), i32, Seq(from, to, startFrom, startTo, length) map transform)

      case t.Plus(lhs, rhs) =>
        mkBin(add, lhs, rhs)
      case t.Minus(lhs, rhs) =>
        mkBin(sub, lhs, rhs)
      case t.Times(lhs, rhs) =>
        mkBin(mul, lhs, rhs)
      case t.Division(lhs, rhs) =>
        mkBin(typeToOp(lhs, div(_), div), lhs, rhs)
      case t.Remainder(lhs, rhs) =>
        mkBin(rem(typeToSign(lhs)), lhs, rhs)
      case t.Modulo(lhs, rhs) =>
        mkBin(rem(Unsigned), lhs, rhs)
      case t.UMinus(e) =>
        e.getType match {
          case t.RealType() => Unary(neg, transform(e))
          case tpe =>
            Binary(sub, typeToZero(transform(tpe)), transform(e))
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
        xor(typeToZero(transform(e.getType)), transform(e))
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
        Wrap(transform(newType), transform(expr))
      case t.BVWideningCast(expr, newType) =>
        Extend(transform(newType), typeToSign(expr.getType), transform(expr))

      case t.And(exprs) =>
        exprs map transform reduceRight[Expr] { case (e1, e2) =>
          If(freshLabel("label"), e1, e2, I32Const(0))
        }
      case t.Or(exprs) =>
        exprs map transform reduceRight[Expr] { case (e1, e2) =>
          If(freshLabel("label"), e1, I32Const(1), e2)
        }
      case t.Not(expr) =>
        sub(I32Const(1), transform(expr))
    }
  }
}
