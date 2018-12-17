/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen
package codegen

import stainless.Identifier
import intermediate.{trees => t}
import wasm.LocalsHandler
import wasm.Expressions.{eq => EQ, _}
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

  protected def updateGlobals(funEnv: FunEnv): Unit = {
    funEnv.gh.update(memB, I32Const(funEnv.dh.nextFree))
  }

  protected def mkTable(s: t.Symbols) = Table(
    s.functions.values.toList.filter(_.flags.contains(t.Dynamic)).map(_.id.uniqueName)
  )

  protected def mkEquality(s: t.Symbols): FunDef = {
    implicit val impS = s
    type BinContext = (Expr, Expr) => (Expr, String)

    def boxedEq(tpe: Type)(name: String = tpe.toString): BinContext = (lhs, rhs) =>
      (EQ(Load(tpe, None, add(lhs, I32Const(4))), Load(tpe, None, add(rhs, I32Const(4)))), name)

    def recordEq(rec: t.RecordSort): BinContext = (lhs, rhs) => {
      // We get offsets of all fields except first (typeTag) which we know is equal already
      val offsets = rec.allFields.scanLeft(0)((off, fld) => off + transform(fld.getType).size).tail
      val fieldEqs = rec.allFields.tail.zip(offsets).map { case (fld, off) =>
        val wasmTpe = transform(fld.getType)
        val l = Load(wasmTpe, None, add(lhs, I32Const(off)))
        val r = Load(wasmTpe, None, add(rhs, I32Const(off)))
        surfaceEq(l, r, fld.getType)
      }
      (fieldEqs.foldRight(I32Const(1): Expr) { case (e, rest) =>
        If(freshLabel("label"), e, rest, I32Const(0))
      }, rec.id.uniqueName)
    }

    val allEqs: (Expr, Expr) => Seq[(Expr, String)] = (lhs, rhs) => {
      boxedEq(i32)()(lhs, rhs) +: boxedEq(i64)()(lhs, rhs) +: boxedEq(f32)()(lhs, rhs) +: boxedEq(f64)()(lhs, rhs) +:
        boxedEq(i32)("array")(lhs, rhs) /* Array reference equality */ +:
        boxedEq(i32)("function")(lhs, rhs) /* Function reference equality */ +: {
        val sorts = s.records.values.toSeq.collect { case c: t.ConstructorSort => c }.sortBy(_.typeTag)
        //assert(sorts.head.typeTag == 6)
        sorts map (s => recordEq(s)(lhs, rhs))
      }
    }

    FunDef(refEqualityName, Seq(ValDef("lhs", i32), ValDef("rhs", i32)), i32) { implicit lh =>
      Sequence(Seq(
        If(
          freshLabel("label"),
          EQ(Load(i32, None, GetLocal("lhs")), Load(i32, None, GetLocal("rhs"))), {
            val eqs = allEqs(GetLocal("lhs"), GetLocal("rhs"))
            // We use i32 as default, whatever, should not happen
            val jump = Br_Table(eqs.map(_._2), eqs.head._2, Load(i32, None, GetLocal("lhs")), None)
            eqs.foldLeft(jump: Expr) { case (first, (equality, label)) =>
              Sequence(Seq(Block(label, first), Return(equality)))
            }
          },
          Return(I32Const(0))
        ),
        I32Const(0)
      ))
    }
  }

  protected def mkInequality(s: t.Symbols): FunDef = {
    implicit val impS = s
    type BinContext = (Expr, Expr) => (Expr, String)

    def mkComp(l: Expr, r: Expr)(implicit lh: LocalsHandler): Expr = l.getType match {
      case `i32` => sub(l, r)
      case `i64` => Wrap(i32, sub(l, r))
      case `f32` => Sequence(Seq(
        SetLocal("tempf32", sub(l, r)),
        If(
          freshLabel("label"),
          gt(GetLocal("tempf32"), F32Const(0)),
          I32Const(1),
          If(
            freshLabel("label"),
            lt(GetLocal("tempf32"), F32Const(0)),
            I32Const(-1),
            I32Const(0)
          )
        )
      ))
      case `f64` => Sequence(Seq(
        SetLocal("tempf64", sub(l, r)),
        If(
          freshLabel("label"),
          gt(GetLocal("tempf64"), F64Const(0)),
          I32Const(1),
          If(
            freshLabel("label"),
            lt(GetLocal("tempf64"), F64Const(0)),
            I32Const(-1),
            I32Const(0)
          )
        )
      ))
    }

    def boxedIneq(tpe: Type, lhs: Expr, rhs: Expr)(name: String = tpe.toString)(implicit lh: LocalsHandler): (Expr, String) =
      (mkComp(Load(tpe, None, add(lhs, I32Const(4))), Load(tpe, None, add(rhs, I32Const(4)))), name)

    def recordIneq(rec: t.RecordSort, lhs: Expr, rhs: Expr, temp: String)(implicit lh: LocalsHandler): (Expr, String) = {
      // We get offsets of all fields except first (typeTag) which we know is equal already
      val offsets = rec.allFields.scanLeft(0)((off, fld) => off + transform(fld.getType).size).tail
      val fieldIneqs = rec.allFields.tail.zip(offsets).map { case (fld, off) =>
        val wasmTpe = transform(fld.getType)
        val l = Load(wasmTpe, None, add(lhs, I32Const(off)))
        val r = Load(wasmTpe, None, add(rhs, I32Const(off)))
        surfaceIneq(l, r, fld.getType)
      }
      (fieldIneqs.foldRight(I32Const(0): Expr) { case (e, rest) =>
        Sequence(Seq(
          SetLocal(temp, e),
          If(freshLabel("label"), eqz(GetLocal(temp)), rest, GetLocal(temp))
        ))
      }, rec.id.uniqueName)
    }

    def allIneqs(lhs: Expr, rhs: Expr, temp: String)(implicit lh: LocalsHandler): Seq[(Expr, String)] = {
      boxedIneq(i32, lhs, rhs)() +: boxedIneq(i64, lhs, rhs)() +: boxedIneq(f32, lhs, rhs)() +: boxedIneq(f64, lhs, rhs)() +:
        boxedIneq(i32, lhs, rhs)("array") /* Array reference equality */ +:
        boxedIneq(i32, lhs, rhs)("function") /* Function reference equality */ +: {
        val sorts = s.records.values.toSeq.collect { case c: t.ConstructorSort => c }.sortBy(_.typeTag)
        //assert(sorts.head.typeTag == 6)
        sorts map (s => recordIneq(s, lhs, rhs, temp))
      }
    }

    FunDef(refInequalityName, Seq(ValDef("lhs", i32), ValDef("rhs", i32)), i32) { implicit lh =>
      val temp = lh.getFreshLocal("temp", i32)
      lh.getFreshLocal("tempf32", f32)
      lh.getFreshLocal("tempf64", f64)
      Sequence(Seq(
        SetLocal(temp, sub(Load(i32, None, GetLocal("lhs")), Load(i32, None, GetLocal("rhs")))),
        If(
          freshLabel("label"),
          eqz(GetLocal(temp)), {
            val ineqs = allIneqs(GetLocal("lhs"), GetLocal("rhs"), temp)
            // We use i32 as default, whatever, should not happen
            val jump = Br_Table(ineqs.map(_._2), ineqs.head._2, Load(i32, None, GetLocal("lhs")), None)
            ineqs.foldLeft(jump: Expr) { case (first, (ineq, label)) =>
              Sequence(Seq(Block(label, first), Return(ineq)))
            }
          },
          Return(GetLocal(temp))
        ),
        I32Const(0) // Should never happen
      ))
    }
  }


  protected def mkToString(s: t.Symbols)(implicit funEnv: FunEnv): FunDef = {
    implicit val impS = s

    def boxedToString(tpe: Type, arg: Expr): (Expr, String) =
      (Call(toStringName(tpe.toString), i32, Seq(Load(tpe, None, add(arg, I32Const(4))))), tpe.toString)

    def recordToString(rec: t.ConstructorSort, arg: Expr): (Expr, String) = {
      (Call(toStringName(rec.id.uniqueName), i32, Seq(arg)), rec.id.uniqueName)
    }

    val allToStrings: Expr => Seq[(Expr, String)] = arg => {
      boxedToString(i32, arg) +: boxedToString(i64, arg) +: boxedToString(f32, arg) +: boxedToString(f64, arg) +:
        (Call(toStringName("array"), i32, Seq()), "array") +:
        (Call(toStringName("fun"), i32, Seq()), "function") +: {
        val sorts = s.records.values.toSeq.collect { case c: t.ConstructorSort => c }.sortBy(_.typeTag)
        sorts map (s => recordToString(s, arg))
      }
    }

    FunDef(refToStringName, Seq(ValDef("arg", i32)), i32) { implicit lh =>
      val toStrings = allToStrings(GetLocal("arg"))
      // We use i32 as default, whatever, should not happen
      val jump = Br_Table(toStrings.map(_._2), toStrings.head._2, Load(i32, None, GetLocal("arg")), None)
      toStrings.foldLeft(jump: Expr) { case (first, (toS, label)) =>
        Sequence(Seq(Block(label, first), Return(toS)))
      }
    }
  }

  private def elemAddr(array: Expr, offset: Expr, tpe: Type) = add(array, mul(add(offset, I32Const(1)), I32Const(tpe.size)))

  protected def mkSubstring(implicit funEnv: FunEnv): FunDef = {
    implicit val gh = funEnv.gh
    FunDef(substringName, Seq("string", "from", "to").map(ValDef(_, i32)), i32) { implicit lh =>
      val str = GetLocal("string")
      val from = GetLocal("from")
      val to = GetLocal("to")
      val index = lh.getFreshLocal("index", i32)
      val loop = freshLabel("loop")
      Sequence(Seq(
        GetGlobal(memB), // Leave substring addr on the stack
        Store(None, GetGlobal(memB), sub(to, from)), // substring length
        SetLocal(index, I32Const(0)),
        Loop(loop,
          If(
            freshLabel("label"),
            lt(Signed)(GetLocal(index), sub(to, from)), // index < length
            Sequence(Seq(
              Store(None,
                elemAddr(GetGlobal(memB), GetLocal(index), i32),
                Load(i32, None, elemAddr(str, add(from, GetLocal(index)), i32))
              ),
              SetLocal(index, add(GetLocal(index), I32Const(1))),
              Br(loop)
            )),
            Nop
          )
        ),
        SetGlobal(memB, add(GetGlobal(memB), add(sub(to, from), I32Const(4))))
      ))
    }
  }

  protected def mkStringConcat(implicit funEnv: FunEnv): FunDef = {
    implicit val gh = funEnv.gh
    FunDef(stringConcatName, Seq("lhs", "rhs").map(ValDef(_, i32)), i32) { implicit lh =>
      val lhs = GetLocal("lhs")
      val rhs = GetLocal("rhs")
      val len1 = Load(i32, None, lhs)
      val len2 = Load(i32, None, rhs)
      val index = lh.getFreshLocal("index", i32)
      val loop = freshLabel("loop")
      Sequence(Seq(
        GetGlobal(memB), // Leave concat addr on the stack
        Store(None, GetGlobal(memB), add(len1, len2)), // concat length
        SetLocal(index, I32Const(0)),
        Loop(loop,
          If(
            freshLabel("label"),
            lt(Signed)(GetLocal(index), len1), // index < length
            Sequence(Seq(
              Store(None,
                elemAddr(GetGlobal(memB), GetLocal(index), i32),
                Load(i32, None, elemAddr(lhs, GetLocal(index), i32))
              ),
              SetLocal(index, add(GetLocal(index), I32Const(1))),
              Br(loop)
            )),
            Nop
          )
        ),
        SetLocal(index, I32Const(0)),
        Loop(loop,
          If(
            freshLabel("label"),
            lt(Signed)(GetLocal(index), len2), // index < length
            Sequence(Seq(
              Store(None,
                elemAddr(GetGlobal(memB), add(len1, GetLocal(index)), i32),
                Load(i32, None, elemAddr(rhs, GetLocal(index), i32))
              ),
              SetLocal(index, add(GetLocal(index), I32Const(1))),
              Br(loop)
            )),
            Nop
          )
        ),
        SetGlobal(memB, elemAddr(GetGlobal(memB), add(len1, len2), i32))
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
    val fields = rt.getRecord.allFields
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


  protected def mkCastDown(expr: Expr, subType: t.RecordType)(implicit env: Env): Expr = {
    implicit val lh = env.lh
    implicit val s = env.s
    val temp = lh.getFreshLocal(freshLabel("cast"), i32)
    subType.getRecord match {
      case cs: t.ConstructorSort =>
        Sequence(Seq(
          SetLocal(temp, expr),
          If(
            freshLabel("label"),
            EQ(Load(i32, None, GetLocal(temp)), I32Const(cs.typeTag)),
            GetLocal(temp),
            Unreachable
          )
        ))
      /*case rs: t.RecordSort =>
        val tags = s.records.collect{ case (_, cs: t.ConstructorSort) if cs.parent contains id  => cs.typeTag }
        if (tags.isEmpty) I32Const(0)
        else {
          Sequence(Seq(
            SetLocal(temp, expr),
            If(
              freshLabel("label"),
              tags map (t => EQ(Load(i32, None, GetLocal(temp)), I32Const(t))) reduceRight or.apply,
              GetLocal(temp),
              Unreachable
            )
          ))

        }*/

      case _ => expr // Our translation ensures by construction that we cannot fail when casting anything else
    }
  }

  // Up-casts are trivial
  protected def mkCastUp(expr: Expr, superType: t.RecordType)(implicit env: Env): Expr = expr

  protected def mkNewArray(length: Expr, base: Type, init: Option[Expr])(implicit env: Env): Expr = {
    implicit val lh = env.lh
    implicit val gh = env.gh
    val memCache = lh.getFreshLocal(freshLabel("mem"), i32)
    val len = lh.getFreshLocal(freshLabel("length"), i32)
    val ind = lh.getFreshLocal(freshLabel("index"), i32)
    val loop = freshLabel("loop")

    def indToPtr(e: Expr) = add(GetLocal(memCache), add(I32Const(4), mul(I32Const(base.size), e)))

    Sequence(Seq(
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

  override def transform(tpe: t.Type)(implicit s: t.Symbols): Type = tpe match {
    case t.ArrayType(_) | t.RecordType(_) | t.StringType() => i32
    case _ => super.transform(tpe)
  }
}
