/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen
package codegen

import stainless.Identifier
import intermediate.{trees => t}
import wasm.Expressions.{ eq => EQ, _ }
import wasm.Types._
import wasm.Definitions._

/** Implements memory allocations in linear memory
  *
  * Global variable 0 points to the free linear memory boundary
  * 
  */
object LinearMemoryCodeGen extends CodeGeneration {
  private val memB = "memB"

  override protected def mkImports(s: t.Symbols) = Seq(
    Import("system", "mem", Memory(100))
  ) ++ super.mkImports(s)

  protected def mkGlobals(s: t.Symbols) = Seq(ValDef(memB, i32))
  protected def mkTable(s: t.Symbols) = Table(
    s.functions.values.toList.filter(_.flags.contains(t.Dynamic)).map(_.id.uniqueName)
  )

  protected def mkBuiltins(s: t.Symbols): Seq[FunDef] = Seq(mkEquality(s))

  private def mkEquality(s: t.Symbols): FunDef = {
    implicit val impS = s
    type BinContext = (Expr, Expr) => (Expr, String)
    def boxedEq(tpe: Type)(name: String = tpe.toString): BinContext = (lhs, rhs) =>
      (EQ(Load(tpe, None, add(lhs, I32Const(4))), Load(tpe, None, add(rhs, I32Const(4)))), name)

    def recordEq(rec: t.RecordSort): BinContext = (lhs, rhs) => {
      // We get offsets of all fields except first (typeTag) which we know is equal already
      val offsets = rec.flattenFields.scanLeft(0)((off, fld) => off + transform(fld.getType).size).tail
      val fieldEqs = rec.flattenFields.tail.zip(offsets).map { case (fld, off) =>
        val wasmTpe = transform(fld.getType)
        val l = Load(wasmTpe, None, add(lhs, I32Const(off)))
        val r = Load(wasmTpe, None, add(rhs, I32Const(off)))
        if(isRefType(fld.getType)) {
          Call(refEqualityName, i32, Seq(l, r))
        } else {
          EQ(l, r)
        }
      }
      (fieldEqs.foldRight(I32Const(1): Expr){ case (e, rest) =>
        If(freshLabel("label"), e, rest, I32Const(0))
      }, rec.id.uniqueName)
    }

    val allEqs: (Expr, Expr) => Seq[(Expr, String)] = (lhs, rhs) => {
      boxedEq(i32)()(lhs, rhs) +: boxedEq(i64)()(lhs, rhs) +: boxedEq(f32)()(lhs, rhs) +: boxedEq(f64)()(lhs, rhs) +:
      boxedEq(i32)("function")(lhs, rhs) /* Function reference equality */ +: {
        val sorts = s.records.values.toSeq.collect{ case c: t.ConstructorSort => c }.sortBy(_.typeTag)
        //sorts.foreach(s => println(s"${s.id.uniqueName} -> ${s.typeTag}"))
        assert(sorts.head.typeTag == 5)
        sorts map (s => recordEq(s)(lhs, rhs))
      }
    }

    FunDef("_ref_eq_", Seq(ValDef("lhs", i32), ValDef("rhs", i32)), i32) { implicit lh =>
      Sequence(Seq(
        If(
          freshLabel("label"),
          EQ(Load(i32, None, GetLocal("lhs")), Load(i32, None, GetLocal("rhs"))),
          {
            val eqs = allEqs(GetLocal("lhs"), GetLocal("rhs"))
            // We use i32 as default, whatever, should not happen
            val jump = Br_Table(eqs.map(_._2), eqs.head._2, Load(i32, None, GetLocal("lhs")), None)
            eqs.foldLeft(jump: Expr){ case (first, (eq, label)) =>
              Sequence(Seq(Block(label, first), Return(eq)))
            }
          },
          Return(I32Const(0))
        ),
        I32Const(0)
      ))
    }
  }

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
    val tpe = transform(fields.find(_.id == id).get.getType)
    val sizeBefore = fields
      .takeWhile(_.id != id)
      .map(fd => transform(fd.getType).size)
      .sum
    Load(
      tpe, None,
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
          Block(loop, Sequence(Seq(
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

  override def transform(tpe: t.Type)(implicit s: t.Symbols): Type = tpe match {
    case t.ArrayType(_) => i32
    case t.RecordType(_) => i32
    case _ => super.transform(tpe)
  }
}
