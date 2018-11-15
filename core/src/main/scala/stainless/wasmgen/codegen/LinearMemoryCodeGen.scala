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
    val l = lh.getFreshLocal(freshLabel("temp"), i32)
 //   Sequence(
   //   SetLocal(l, GetGlobal(memB)),
      
  //  )
		???
  }
  protected def mkRecordSelector(expr: Expr, rt: t.RecordType, id: Identifier)(implicit s: S, lh: LH): Expr = ???
  protected def mkFunctionPointer(id: Identifier)(implicit s: S, lh: LH): Expr = ???

  protected def mkCastDown(expr: Expr, subType: t.RecordType)(implicit s: S, lh: LH): Expr = expr
  protected def mkCastUp(expr: Expr, superType: t.RecordType)(implicit s: S, lh: LH): Expr = expr

  protected def mkNewArray(length: Expr, base: Type, init: Option[Expr])(implicit s: S, lh: LH): Expr = ???

  protected def mkArrayGet(expr: Expr, expr1: Expr)(implicit s: S, lh: LH): Expr = ???

  protected def mkArraySet(expr: Expr, expr1: Expr, expr2: Expr)(implicit s: S, lh: LH): Expr = ???

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
    case t.ArrayType(_) => i32
    case t.RecordType(_, _) => i32
    case t.RealType() => f64
    case t.BVType(_, size) => if (size == 64) i64 else i32
  }
}
