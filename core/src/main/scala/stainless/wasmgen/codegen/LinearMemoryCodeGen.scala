package stainless.wasmgen
package codegen

import stainless.Identifier
import intermediate.{trees => t}
import wasm.Expressions._
import wasm.Types._

/** Assumes global variable 0 points to the free linear memory boundary
  * 
  */
class LinearMemoryCodeGen extends CodeGeneration {
  
  def mkRecord(recordType: t.RecordType, exprs: Seq[Expr]): Expr = {
    
  }

  def mkRecordSelector(expr: Expr, id: Identifier) = ???

  def mkFunctionPointer(id: Identifier) = ???

  // Casts are trivial, since pointers are i32 l.m. indexes
  def mkCastDown(expr: Expr, subType: t.RecordType) = expr
  def mkCastUp(expr: Expr, superType: t.RecordType) = expr

  def mkNewArray(length: Expr, base: Type, init: Option[Expr]) = ???

  def mkArrayGet(expr: Expr, expr1: Expr) = ???

  def mkArraySet(expr: Expr, expr1: Expr, expr2: Expr) = ???

  def mkArrayLength(expr: Expr) = ???

  def mkArrayCopy(expr: Expr, expr1: Expr, expr2: Expr, expr3: Expr) = ???

  def mkApplication(expr: Expr, exprs: Seq[Expr]) = ???

  def mkUnbox0(e: Expr, tpe: Type) = ???

  def mkBox0(expr: Expr, tpe: Type) = ???

  def transform(tpe: t.Type)(implicit s: t.Symbols) = tpe match {
    case t.IntegerType() => i64
    case t.ArrayType(_) => i32
    case t.RecordType(_, _) => i32
    case t.RealType() => f64
    case t.BVType(_, size) => if (size == 64) i64 else i32
  }
}
