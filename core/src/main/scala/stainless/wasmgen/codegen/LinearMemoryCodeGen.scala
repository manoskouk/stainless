package stainless.wasmgen
package codegen

import stainless.{Identifier, FreshIdentifier}
import intermediate.{trees => t}
import wasm.Expressions._
import wasm.Types._
import wasm.GlobalsHandler

/** Assumes global variable 0 points to the free linear memory boundary
  * 
  */
class LinearMemoryCodeGen extends CodeGeneration {
  protected implicit val gh = new GlobalsHandler()

  private val memB = "memB"

  private def freshLabel(s: String) = FreshIdentifier(s).uniqueName
  
  protected def mkRecord(recordType: t.RecordType, exprs: Seq[Expr])(implicit s: S, lh: LH): Expr = {
    // offsets for fields, with last element being the new memory boundary
    val offsets = exprs.scanLeft(0)(_ + _.getType.size)
    Sequence(
      exprs
        .zip(offsets)
        .map { case (e, off) =>
          Store(e.getType, None, add(GetGlobal(memB), I32Const(off)), e)
        } :+
      SetGlobal(memB, add(GetGlobal(memB), I32Const(offsets.last)))
    )
  }

  protected def mkRecordSelector(expr: Expr, rt: t.RecordType, id: Identifier)(implicit s: S, lh: LH): Expr = {
    val fields = rt.getRecord.definition.flattenFields
    val sizeBefore = fields
      .takeWhile(_.id != id)
      .map(fd => transform(fd.getType).size)
      .sum
    Load(
      expr.getType, None,
      add(expr, add(I32Const(4), I32Const(sizeBefore)))
    )
  }
  protected def mkFunctionPointer(id: Identifier)(implicit s: S, lh: LH): Expr = ???

  protected def mkCastDown(expr: Expr, subType: t.RecordType)(implicit s: S, lh: LH): Expr = expr
  protected def mkCastUp(expr: Expr, superType: t.RecordType)(implicit s: S, lh: LH): Expr = expr

  protected def mkNewArray(length: Expr, base: Type, init: Option[Expr])(implicit s: S, lh: LH): Expr = {
    val len  = lh.getFreshLocal(freshLabel("length"), i32)
    val ind  = lh.getFreshLocal(freshLabel("index"), i32)
    val loop = freshLabel("loop")
    def indToPtr(e: Expr) = add(GetGlobal(memB), add(I32Const(4), mul(I32Const(base.size), e)))
    Sequence( Seq(
      SetLocal(len, length),
      Store(i32, None, GetGlobal(memB), GetLocal(len)),
      SetLocal(ind, I32Const(0))
    ) ++ (init match {
      case Some(elem) =>
        val initL = lh.getFreshLocal(freshLabel("init"), base)
        Seq(
          SetLocal(initL, elem),
          Branch(loop, void, Sequence(Seq(
            Br_If(loop, ge(GetLocal(ind), GetLocal(len))),
            Store(base, None, indToPtr(GetLocal(ind)), GetLocal(initL)),
            SetLocal(ind, add(GetLocal(ind), I32Const(1)))
          )))
        )
      case None =>
        Seq()
    }) ++ Seq(
      SetGlobal(memB, indToPtr(GetLocal(len)) )
    ))
  }

  protected def mkArrayGet(array: Expr, base: Type, index: Expr)(implicit s: S, lh: LH): Expr = {
    Load(
      base, None,
      add(array, add(I32Const(4), mul(index, I32Const(base.size))))
    )
  }

  protected def mkArraySet(array: Expr, index: Expr, value: Expr)(implicit s: S, lh: LH): Expr = {
    Store(
      value.getType, None,
      add(array, add(I32Const(4), mul(index, I32Const(value.getType.size)))),
      value
    )
  }

  protected def mkArrayLength(expr: Expr)(implicit s: S, lh: LH): Expr = Load(i32, None, expr)

  protected def mkArrayCopy(expr: Expr, expr1: Expr, expr2: Expr, expr3: Expr)(implicit s: S, lh: LH): Expr = ???

  protected def mkApplication(expr: Expr, exprs: Seq[Expr])(implicit s: S, lh: LH): Expr = ???

  protected def mkUnbox0(e: Expr, tpe: Type)(implicit s: S, lh: LH): Expr = Load(tpe, None, e)

  protected def mkBox0(expr: Expr, tpe: Type)(implicit s: S, lh: LH): Expr = {
    Sequence( Seq(
      GetGlobal(memB),
      Store(expr.getType, None, GetGlobal(memB), expr),
      SetGlobal(memB, add(GetGlobal(memB), I32Const(expr.getType.size)))
    ))
  }


  def transform(tpe: t.Type)(implicit s: t.Symbols) = tpe match {
    case t.IntegerType() => i64
    case t.RealType() => f64
    case t.BVType(_, size) => if (size == 64) i64 else i32
    case t.ArrayType(_) => i32
    case t.RecordType(_, _) => i32
    case t.TypeParameter(_, _) => i32
  }
}
