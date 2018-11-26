/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen
package codegen

import stainless.{Identifier, FreshIdentifier}
import intermediate.{trees => t}
import wasm.Expressions._
import wasm.Types._
import wasm.Definitions._

/** Implements memory allocations in linear memory
  *
  * Global variable 0 points to the free linear memory boundary
  * 
  */
object LinearMemoryCodeGen extends CodeGeneration {
  private val memB = "memB"

  private def freshLabel(s: String) = FreshIdentifier(s).uniqueName

  protected def mkImports(s: t.Symbols) = Seq(
    Import("system", "mem", Memory(100))
  )
  protected def mkGlobals(s: t.Symbols) = Seq(ValDef(memB, i32))
  protected def mkTable(s: t.Symbols) = Table(
    s.functions.values.toList.filter(_.flags.contains(t.Dynamic)).map(_.id.uniqueName)
  )

  protected def mkRecord(recordType: t.RecordType, exprs: Seq[Expr])(implicit env: Env): Expr = {
    implicit val gh = env.gh
    implicit val lh = env.lh
    // offsets for fields, with last element being the new memory boundary
    val offsets = exprs.scanLeft(0)(_ + _.getType.size)
    val memCache = lh.getFreshLocal(freshLabel("mem"), i32)
    Sequence(
      SetLocal(memCache, GetGlobal(memB)) +:
      // Already set new memB because fields may also need new memory
      SetGlobal(memB, add(GetLocal(memCache), I32Const(offsets.last))) +:
      exprs
        .zip(offsets)
        .map { case (e, off) =>
          Store(None, add(GetLocal(memCache), I32Const(off)), e)
        } :+
      GetLocal(memCache)
    )
  }

  protected def mkRecordSelector(expr: Expr, rt: t.RecordType, id: Identifier)(implicit env: Env): Expr = {
    implicit val s = env.s
    val fields = rt.getRecord.flattenFields
    val sizeBefore = fields
      .takeWhile(_.id != id)
      .map(fd => transform(fd.getType).size)
      .sum
    Load(
      expr.getType, None,
      add(expr, I32Const(sizeBefore))
    )
  }

  protected def mkFunctionPointer(id: Identifier)(implicit env: Env): Expr = {
    I32Const(env.tab.indexOf(id.uniqueName))
  }

  // Type casts are trivial
  protected def mkCastDown(expr: Expr, subType: t.RecordType)(implicit env: Env): Expr = expr
  protected def mkCastUp(expr: Expr, superType: t.RecordType)(implicit env: Env): Expr = expr

  protected def mkNewArray(length: Expr, base: Type, init: Option[Expr])(implicit env: Env): Expr = {
    implicit val lh = env.lh
    implicit val gh = env.gh
    val memCache = lh.getFreshLocal(freshLabel("mem"), i32)
    val len  = lh.getFreshLocal(freshLabel("length"), i32)
    val ind  = lh.getFreshLocal(freshLabel("index"),  i32)
    val loop = freshLabel("loop")
    def indToPtr(e: Expr) = add(GetLocal(memCache), add(I32Const(4), mul(I32Const(base.size), e)))
    Sequence( Seq(
      SetLocal(memCache, GetGlobal(memB)),
      SetGlobal(memB, indToPtr(GetLocal(len))),
      SetLocal(len, length),
      Store(None, GetLocal(memCache), GetLocal(len)),
      SetLocal(ind, I32Const(0))
    ) ++ (init match {
      case Some(elem) =>
        val initL = lh.getFreshLocal(freshLabel("init"), base)
        Seq(
          SetLocal(initL, elem),
          Branch(loop, Sequence(Seq(
            Br_If(loop, ge(GetLocal(ind), GetLocal(len))),
            Store(None, indToPtr(GetLocal(ind)), GetLocal(initL)),
            SetLocal(ind, add(GetLocal(ind), I32Const(1)))
          )))
        )
      case None =>
        Seq()
    }) ++ Seq(
      GetLocal(memCache)
    ))
  }

  protected def mkArrayGet(array: Expr, base: Type, index: Expr)(implicit env: Env): Expr = {
    Load(
      base, None,
      add(array, add(I32Const(4), mul(index, I32Const(base.size))))
    )
  }

  protected def mkArraySet(array: Expr, index: Expr, value: Expr)(implicit env: Env): Expr = {
    Store(
      None,
      add(array, add(I32Const(4), mul(index, I32Const(value.getType.size)))),
      value
    )
  }

  protected def mkArrayLength(expr: Expr)(implicit env: Env): Expr = Load(i32, None, expr)

  protected def mkArrayCopy(base: Type, from: Expr, to: Expr, start: Expr, finish: Expr)(implicit env: Env): Expr = { ??? /*
    implicit val lh = env.lh
    implicit val gh = env.gh
    val f = lh.getFreshLocal(freshLabel("from"), i32)
    val t = lh.getFreshLocal(freshLabel("to"), i32)
    val ind  = lh.getFreshLocal(freshLabel("index"),  i32)
    val loop = freshLabel("loop")
    def indToPtr(arr: Label, e: Expr) = add(GetLocal(arr), add(I32Const(4), mul(I32Const(base.size), e)))
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
    }*/
  }

  def transform(tpe: t.Type)(implicit s: t.Symbols): Type = tpe match {
    case t.BooleanType() => i32
    case t.RealType() => f64
    case t.BVType(_, size) => if (size == 64) i64 else i32
    case t.ArrayType(_) => i32
    case t.RecordType(_) => i32
  }
}
