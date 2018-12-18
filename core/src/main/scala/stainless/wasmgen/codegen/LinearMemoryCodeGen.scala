/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen
package codegen

import stainless.Identifier
import intermediate.{trees => t}
import wasm.{GlobalsHandler, LocalsHandler}
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
  private def getMem(implicit gh: GlobalsHandler) = GetGlobal(memB)
  private def setMem(expr: Expr)(implicit gh: GlobalsHandler) =
    SetGlobal(memB, expr)

  override protected def mkImports(s: t.Symbols) =
    Import("system", "mem", Memory(100)) +: super.mkImports(s)

  protected def mkGlobals(s: t.Symbols) = Seq(ValDef(memB, i32))

  protected def updateGlobals(funEnv: FunEnv): Unit = {
    funEnv.gh.update(memB, I32Const(funEnv.dh.nextFree))
  }

  protected def mkTable(s: t.Symbols) = Table(
    s.functions.values.toList.filter(_.flags.contains(t.Dynamic)).map(_.id.uniqueName)
  )

  /* Helpers */
  // Compute the address of an element in an array from base and offset
  private def elemAddr(array: Expr, offset: Expr) = add(array, mul(add(offset, I32Const(1)), I32Const(4)))
  private def strCharAddr(string: Expr, offset: Expr) = add(string, add(offset, I32Const(4)))
  private def unbox(tpe: Type, ref: Expr) = Load(tpe, None, add(ref, I32Const(4)))

  protected def mkEquality(s: t.Symbols): FunDef = {
    implicit val impS = s

    def boxedEq(tpe: Type, lhs: Expr, rhs: Expr)(name: String = tpe.toString): (Expr, String) =
      (EQ(unbox(tpe, lhs), unbox(tpe, rhs)), name)

    def recordEq(rec: t.RecordSort, lhs: Expr, rhs: Expr): (Expr, String) = {
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

    def allEqs(lhs: Expr, rhs: Expr): Seq[(Expr, String)] = {
      Seq(
        boxedEq(i32, lhs, rhs)("boolean"),
        boxedEq(i32, lhs, rhs)("char"),
        boxedEq(i32, lhs, rhs)(),
        boxedEq(i64, lhs, rhs)(),
        boxedEq(i64, lhs, rhs)("BigInt"),
        boxedEq(f64, lhs, rhs)(),
        boxedEq(i32, lhs, rhs)("array"),
        boxedEq(i32, lhs, rhs)("string"),
        boxedEq(i32, lhs, rhs)("function")
      ) ++ {
        val sorts = s.records.values.toSeq.collect { case c: t.ConstructorSort => c }.sortBy(_.typeTag)
        sorts map (s => recordEq(s, lhs, rhs))
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

    def boxedIneq(tpe: Type, lhs: Expr, rhs: Expr)(name: String = tpe.toString): (Expr, String) =
      (baseTypeIneq(unbox(tpe, lhs), unbox(tpe, rhs)), name)

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
      Seq(
        boxedIneq(i32, lhs, rhs)("boolean"),
        boxedIneq(i32, lhs, rhs)("char"),
        boxedIneq(i32, lhs, rhs)(),
        boxedIneq(i64, lhs, rhs)(),
        boxedIneq(i64, lhs, rhs)("BigInt"),
        boxedIneq(f64, lhs, rhs)(),
        boxedIneq(i32, lhs, rhs)("array"),
        boxedIneq(i32, lhs, rhs)("string"),
        boxedIneq(i32, lhs, rhs)("function")
      ) ++ {
        val sorts = s.records.values.toSeq.collect { case c: t.ConstructorSort => c }.sortBy(_.typeTag)
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

    def boxedToString(tpe: Type, arg: Expr)(tpeName: String = tpe.toString): (Expr, String) =
      (Call(toStringName(tpeName), i32, Seq(unbox(tpe, arg))), tpeName)

    def recordToString(rec: t.ConstructorSort, arg: Expr): (Expr, String) = {
      (Call(toStringName(rec.id.uniqueName), i32, Seq(arg)), rec.id.uniqueName)
    }

    def allToStrings(arg: Expr): Seq[(Expr, String)] = {
      Seq(
        boxedToString(i32, arg)("boolean"),
        boxedToString(i32, arg)("char"),
        boxedToString(i32, arg)(),
        boxedToString(i64, arg)(),
        boxedToString(i64, arg)("BigInt"),
        boxedToString(f64, arg)(),
        boxedToString(i32, arg)("array"),
        (unbox(i32, arg), "string"),
        (Call(toStringName("fun"), i32, Seq()), "function")
      ) ++ {
        val sorts = s.records.values.toSeq.collect { case c: t.ConstructorSort => c }.sortBy(_.typeTag)
        sorts map (s => recordToString(s, arg))
      }
    }

    FunDef(refToStringName, Seq(ValDef("arg", i32)), i32) { implicit lh =>
      val toStrings = allToStrings(GetLocal("arg"))
      // We use i32 as default, whatever, should not happen
      val jump = Br_Table(toStrings.map(_._2), toStrings(2)._2, Load(i32, None, GetLocal("arg")), None)
      toStrings.foldLeft(jump: Expr) { case (first, (toS, label)) =>
        Sequence(Seq(Block(label, first), Return(toS)))
      }
    }
  }

  protected def mkCharToString(implicit funEnv: FunEnv): FunDef = {
    implicit val gh = funEnv.gh
    FunDef(toStringName("char"), Seq(ValDef("arg", i32)), i32){ implicit lh =>
      Sequence(Seq(
        getMem,
        Store(None, getMem, I32Const(1)),
        Store(None, add(getMem, I32Const(4)), GetLocal("arg")),
        setMem(add(getMem, I32Const(8)))
      ))
    }
  }

  protected def mkBigIntToString(implicit funEnv: FunEnv): FunDef = {
    FunDef(toStringName("BigInt"), Seq(ValDef("arg", i64)), i32){ implicit lh =>
      implicit val env = funEnv.env(lh)
      Call(stringConcatName, i32, Seq(
        Call(stringConcatName, i32, Seq(
          transform(t.StringLiteral("BigInt(")),
          Call(toStringName("i64"), i32, Seq(GetLocal("arg")))
        )),
        transform(t.StringLiteral(")"))
      ))
    }
  }

  protected def mkArrayToString(implicit funEnv: FunEnv): FunDef = {
    FunDef(toStringName("array"), Seq(ValDef("array", i32)), i32) { implicit lh =>
      implicit val env = funEnv.env(lh)
      val ind = lh.getFreshLocal(freshLabel("index"), i32)
      val curr = lh.getFreshLocal(freshLabel("current"), i32)
      val loop = freshLabel("loop")

      def indToPtr(e: Expr) = elemAddr(GetLocal("array"), e)

      Sequence(Seq(
        SetLocal(ind, I32Const(0)),
        SetLocal(curr, transform(t.StringLiteral(""))),
        Loop(loop,
          If(
            freshLabel("label"),
            lt(Unsigned)(GetLocal(ind), Load(i32, None, GetLocal("array"))),
            Sequence(Seq(
              SetLocal(curr,
                Call(stringConcatName, i32, Seq(
                  GetLocal(curr),
                  If(
                    freshLabel("label"),
                    eqz(GetLocal(ind)),
                    Call(refToStringName, i32, Seq(Load(i32, None, indToPtr(GetLocal(ind))))),
                    Call(stringConcatName, i32, Seq(
                      transform(t.StringLiteral(", ")),
                      Call(refToStringName, i32, Seq(Load(i32, None, indToPtr(GetLocal(ind)))))
                    ))
                  )
                ))
              ),
              SetLocal(ind, add(GetLocal(ind), I32Const(1))),
              Br(loop)
            )),
            Nop
          )
        ),
        Call(stringConcatName, i32, Seq(
          transform(t.StringLiteral("Array(")),
          Call(stringConcatName, i32, Seq(
            GetLocal(curr), transform(t.StringLiteral(")"))
          ))
        ))
      ))
    }
  }

  protected def mkStringLiteral(str: String)(implicit env: Env): Expr = {
    val length = str.length
    val mask = 0xFF
    val l0 = length & mask
    val l1 = (length >> 8) & mask
    val l2 = (length >> 16) & mask
    val l3 = (length >> 24) & mask
    val lbytes = Seq(l0, l1, l2, l3).map(_.toByte.r) // Little endian
    val content = str.map(_.toByte.f)
    I32Const(env.dh.addNext(lbytes ++ content))
  }

  protected def mkSubstring(implicit funEnv: FunEnv): FunDef = {
    implicit val gh = funEnv.gh
    FunDef(substringName, Seq("string", "from", "to").map(ValDef(_, i32)), i32) { implicit lh =>
      val str = GetLocal("string")
      val from = GetLocal("from")
      val to = GetLocal("to")
      val index = lh.getFreshLocal("index", i32)
      val length = lh.getFreshLocal("length", i32)
      val loop = freshLabel("loop")
      Sequence(Seq(
        SetLocal(length, sub(to, from)),
        Store(None, getMem, GetLocal(length)),
        SetLocal(index, I32Const(0)),
        Loop(loop,
          If(
            freshLabel("label"),
            lt(Unsigned)(GetLocal(index), GetLocal(length)), // index < length
            Sequence(Seq(
              Store(Some(i8),
                strCharAddr(getMem, GetLocal(index)),
                Load(i32, Some((i8, Unsigned)), strCharAddr(str, add(from, GetLocal(index))))
              ),
              SetLocal(index, add(GetLocal(index), I32Const(1))),
              Br(loop)
            )),
            Nop
          )
        ),
        getMem, // Leave substring addr on the stack
        setMem(strCharAddr(getMem, GetLocal(length)))
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
        Store(None, getMem, add(len1, len2)), // concat length
        SetLocal(index, I32Const(0)),
        Loop(loop,
          If(
            freshLabel("label"),
            lt(Signed)(GetLocal(index), len1), // index < length
            Sequence(Seq(
              Store(Some(i8),
                strCharAddr(getMem, GetLocal(index)),
                Load(i32, Some((i8, Unsigned)), strCharAddr(lhs, GetLocal(index)))
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
              Store(Some(i8),
                strCharAddr(getMem, add(len1, GetLocal(index))),
                Load(i32, Some((i8, Unsigned)), strCharAddr(rhs, GetLocal(index)))
              ),
              SetLocal(index, add(GetLocal(index), I32Const(1))),
              Br(loop)
            )),
            Nop
          )
        ),
        getMem, // Leave concat addr on the stack
        setMem(strCharAddr(getMem, add(len1, len2)))
      ))
    }
  }

  protected def mkRecord(recordType: t.RecordType, fields: Seq[Expr])(implicit env: Env): Expr = {
    implicit val gh = env.gh
    implicit val lh = env.lh
    // offsets for fields, with last element being the new memory boundary
    val offsets = fields.scanLeft(0)(_ + _.getType.size)
    val memCache = lh.getFreshLocal(freshLabel("mem"), i32)
    Sequence(
      SetLocal(memCache, getMem) +:
      // Already set new memB because fields may also need new memory
      setMem(add(GetLocal(memCache), I32Const(offsets.last))) +:
      fields.zip(offsets).map { case (e, off) =>
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
    Load(tpe, None, add(expr, I32Const(sizeBefore)))
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
      // Our translation ensures by construction that we cannot fail when casting anything else
      case _ => expr
    }
  }

  // Up-casts are trivial
  protected def mkCastUp(expr: Expr, superType: t.RecordType)(implicit env: Env): Expr = expr

  protected def mkNewArray(length: Expr, init: Option[Expr])(implicit env: Env): Expr = {
    implicit val lh = env.lh
    implicit val gh = env.gh
    val evLength = lh.getFreshLocal(freshLabel("length"), i32)

    Sequence(
      Seq(
        SetLocal(evLength, length),
        Store(None, getMem, GetLocal(evLength))
      ) ++ (init match {
        case Some(elem) =>
          val evInit = lh.getFreshLocal(freshLabel("init"), i32)
          val ind = lh.getFreshLocal(freshLabel("index"), i32)
          val loop = freshLabel("loop")
          Seq(
            SetLocal(ind, I32Const(0)),
            SetLocal(evInit, elem),
            Loop(loop, Sequence(Seq(
              If(
                freshLabel("label"),
                lt(GetLocal(ind), GetLocal(evLength)),
                Sequence(Seq(
                  Store(None,
                    elemAddr(getMem, GetLocal(ind)),
                    GetLocal(evInit)
                  ),
                  SetLocal(ind, add(GetLocal(ind), I32Const(1))),
                  Br(loop)
                )),
                Nop
              )
            )))
          )
        case None =>
          Seq()
      }) ++ Seq(
        getMem,
        setMem(elemAddr(getMem, GetLocal(evLength)))
      )
    )
  }

  protected def mkArrayGet(array: Expr, index: Expr)(implicit env: Env): Expr = {
    Load(i32, None, elemAddr(array, index))
  }

  protected def mkArraySet(array: Expr, index: Expr, value: Expr)(implicit env: Env): Expr = {
    Store(None, elemAddr(array, index), value)
  }

  protected def mkArrayLength(expr: Expr)(implicit env: Env): Expr = Load(i32, None, expr)

  override def transform(tpe: t.Type)(implicit s: t.Symbols): Type = tpe match {
    case t.ArrayType(_) | t.RecordType(_) | t.StringType() => i32
    case _ => super.transform(tpe)
  }
}
