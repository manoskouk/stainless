/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen
package intermediate

import stainless.ast.SymbolIdentifier
import stainless.{FreshIdentifier, Identifier}

trait Transformer extends stainless.transformers.Transformer {
  implicit protected lazy val printerOptions = t.PrinterOptions(printUniqueIds = true)

  val s = stainless.trees
  val t = trees

  type Env = (s.Symbols, SymbolsManager)

  override def transform(tp: s.Type, env: Env): t.Type = {
    implicit val impSyms = env._1
    import t._
    tp match {
      case s.Untyped => Untyped
      case s.UnitType() => Int32Type()
      case s.CharType() => Int32Type()
      case s.IntegerType() => Int64Type() // TODO: Implement big integers properly
      case s.StringType() => ArrayType(Int32Type())

      case s.ADTType(id, tps) =>
        RecordType(id)

      case s.FunctionType(from, to) =>
        RecordType(env._2.funPointerSort(
          FunctionType(Seq.fill(from.size)(AnyRefType), AnyRefType)
        ))

      case s.TupleType(bases) =>
        RecordType(env._1.lookup[s.ADTSort](s"Tuple${bases.size}").id)
      case s.SetType(base) => ???
      case s.BagType(base) => ???
      case s.MapType(from, to) => ???

      case s.PiType(params, to) =>
        transform(s.FunctionType(params.map(_.getType), to.getType), env)
      case s.SigmaType(params, to) =>
        transform(s.TupleType(params.map(_.getType) :+ to.getType), env)
      case s.RefinementType(vd, prop) =>
        transform(vd.getType, env)

      case s.TypeParameter(id, flags) => // Type erasure
        RecordType(AnyRefSort.id)

      // These remain the same
      // case s.RealType() => TODO: We will represent Reals as floats (?)
      // case s.ArrayType(base) =>
      // case s.BVType(signed, size) =>

      case _ => super.transform(tp, env)
    }
  }
}

private[wasmgen] class SymbolsManager {
  import trees._
  import scala.collection.mutable.{Map => MMap}

  private val newFunctions_ : MMap[Identifier, FunDef] = MMap()
  private val newRecords_ : MMap[Identifier, RecordSort] = MMap()
  private val boxedSorts: MMap[Type, Identifier] = MMap()
  private val funRecords: MMap[FunctionType, Identifier] = MMap()

  def addFunction(fd: FunDef): Unit = newFunctions_ += fd.id -> fd

  def funPointerSort(ft: FunctionType): Identifier =
    funRecords.getOrElseUpdate(ft, {
      val fr = new FunPointerSort(FreshIdentifier("`" + ft.asString(PrinterOptions()) + "`"), ft)
      newRecords_ += fr.id -> fr
      fr.id
    })

  def closureSort(funType: FunctionType, env: Seq[ValDef]): Identifier = {
    // Always make a new closure sort
    val cs = new ClosureSort(funPointerSort(funType), env)
    newRecords_ += cs.id -> cs
    cs.id
  }

  def boxedSort(tpe: Type): Identifier = boxedSorts.getOrElseUpdate(tpe, {
    val s = new BoxedSort(tpe)
    newRecords_ += s.id -> s
    s.id
  })

  def functions = newFunctions_
  def records = newRecords_
}


private [wasmgen] class ExprTransformer (
  manager: SymbolsManager,
  keepContracts: Boolean,
  sym0: stainless.trees.Symbols,
  initSorts: Map[Identifier, trees.RecordSort]
) extends Transformer {
  import t._
  private val StrType = ArrayType(Int32Type())
  def initEnv = (sym0, manager)

  private def isRecordType(tpe: t.Type) = tpe match {
    case t.RecordType(_) => true
    case _ => false
  }

  private def maybeBox(e: s.Expr, expected: t.Type, env: Env): t.Expr = {
    implicit val impSyms = env._1
    val manager = env._2
    val trType = transform(e.getType, env)
    val trE = transform(e, env)
    if (!isRecordType(trType) && expected == AnyRefType)
      CastUp(
        Record(
          RecordType(manager.boxedSort(trType)),
          Seq(Int32Literal(typeToTag(trType)), trE)),
        AnyRefType
      )
    else if (trType == expected) trE
    else CastUp(trE, AnyRefType)
  }
  private def maybeUnbox(e: t.Expr, real: t.Type, expected: t.Type, env: Env): t.Expr = {
    implicit val impSyms = env._1
    val mangage = env._2
    if (!isRecordType(expected) && real == AnyRefType)
      RecordSelector(
        CastDown(e, RecordType(manager.boxedSort(expected))),
        boxedValueId
      )
    else if (real == expected) e
    else CastDown(e, expected.asInstanceOf[RecordType])
  }

  def transform(fd: s.FunDef): t.FunDef = {
    new t.FunDef(
      transform(fd.id, initEnv),
      Seq(), //fd.tparams map (transform(_, initEnv)),
      fd.params map (transform(_, initEnv)),
      transform(fd.returnType, initEnv),
      transform(fd.fullBody, initEnv),
      fd.flags map (transform(_, initEnv))
    ).copiedFrom(fd)
  }

  override def transform(e: s.Expr, env: Env): Expr = {
    implicit val impSyms = env._1
    e match {
      // Literals
      case s.UnitLiteral() =>
        Int32Literal(0)
      case s.CharLiteral(value) =>
        Int32Literal(value)
      case s.IntegerLiteral(value) =>
        // TODO: Represent mathematical integers adequately
        t.Int64Literal(
          if (value.isValidLong) value.toLong
          else if (value > Int.MaxValue) Int.MaxValue
          else Int.MinValue
        )

      // Misc.
      case s.Annotated(body, flags) =>
        transform(body, env)
      case s.Error(tpe, description) =>
        Sequence(Seq(
          Output(transform(s.StringLiteral(description), env)),
          NoTree(transform(tpe, env))
        ))
      case me: s.MatchExpr => transform(impSyms.matchToIfThenElse(me), env)

      // Contracts
      case s.Assume(pred, body) =>
        if (keepContracts)
          IfExpr(transform(pred, env), transform(body, env), NoTree(transform(body.getType, env)))
        else
          transform(body, env)
      case s.Require(pred, body) =>
        transform(s.Assume(pred, body), env)
      case s.Ensuring(body, s.Lambda(Seq(vd), lbody)) =>
        if (keepContracts) {
          val trV = transform(vd, env)
          Let(trV, transform(body, env),
            IfExpr(transform(lbody, env), trV.toVariable, NoTree(trV.tpe))
          )
        } else {
          transform(body, env)
        }
      case s.Assert(pred, error, body) =>
        if (keepContracts)
          IfExpr(
            transform(pred, env),
            transform(body, env),
            transform(s.Error(body.getType, error getOrElse ""), env)
          )
        else transform(body, env)

      // Higher-order
      case s.Application(callee, args) =>
        val tCallee = transform(callee, env)
        val vCallee = Variable.fresh("fun", transform(callee.getType, env))
        // All arguments are passed to lambdas and result is returned as anyref
        Let(vCallee.toVal, tCallee,
          maybeUnbox(Application(
            RecordSelector(vCallee, funPointerId),
            vCallee +: args.map( arg => maybeBox(arg, AnyRefType, env))
          ), AnyRefType, transform(e.getType, env), env)
        )
      case lmd@s.Lambda(params, body) =>
        val boxedFunType = FunctionType(
          Seq.fill(params.size)(AnyRefType),
          AnyRefType
        )
        val fv = (s.exprOps.variablesOf(body).map(_.toVal) -- params).toSeq.map(transform(_, env))

        // Make/find a RecordSort for this function type, and one with the specific env.
        val funRecId = manager.funPointerSort(boxedFunType)

        val freshEnv = fv.map(_.freshen)
        val closureSortId = manager.closureSort(boxedFunType, freshEnv)

        val funRecordType = RecordType(funRecId)
        val closureType = RecordType(closureSortId)

        val function = {
          def extractEnv(env: Variable, body: Expr) = {
            val castEnv = ValDef.fresh("env", closureType)
            Let(
              castEnv,
              CastDown(env, closureType),
              fv.zip(freshEnv).foldRight(body) { case ((v, envId), rest) =>
                Let(v, RecordSelector(castEnv.toVariable, envId.id), rest)
              }
            )
          }

          def unboxParams(boxedParams: Seq[ValDef], body: Expr) = {
            boxedParams.zip(params).foldRight(body) { case ((boxed, unboxed), rest) =>
              Let(transform(unboxed, env),
                maybeUnbox(boxed.toVariable, AnyRefType, transform(unboxed.getType, env), env),
                rest
              )
            }
          }

          def boxResult(body: s.Expr) = maybeBox(body, AnyRefType, env)

          val fd = {
            val envParam  = ValDef.fresh("env", funRecordType)
            val boxedParams = params map (p => ValDef(p.id.freshen, AnyRefType))
            new FunDef(
              FreshIdentifier("lambda"), Seq(),
              envParam +: boxedParams,
              AnyRefType,
              extractEnv(
                envParam.toVariable,
                unboxParams(
                  boxedParams,
                  boxResult(body))),
              Seq(Dynamic)
            )
          }

          manager.addFunction(fd)
          fd
        }

        val closure = {
          CastUp(
            Record(
              closureType,
              Int32Literal(typeToTag(boxedFunType)) +: FunctionPointer(function.id) +: fv.map(_.toVariable)
            ),
            funRecordType
          )
        }

        closure

      // Booleans
      case s.Implies(lhs, rhs) => transform(s.Or(lhs, s.Not(rhs)), env)

      // ADTs
      case s.ADT(id, tps, args) =>
        // Except constructor fields, we also store the i32 tag corresponding to this constructor
        val typeTag = initSorts(id).asInstanceOf[ConstructorSort].typeTag
        val formals = sym0.constructors(id).fields.map(_.getType)
        val tpe = RecordType(id)
        CastUp(
          Record(tpe, Int32Literal(typeTag) +: args.zip(formals).map {
            case (arg, formal) => maybeBox(arg, transform(formal, env), env)
          }),
          RecordType(sym0.constructors(id).sort)
        )
      case s.IsConstructor(expr, id) =>
        // We need to compare the constructor code of given value
        // to the code corresponding to constructor 'id'
        Equals(
          RecordSelector(transform(expr, env), typeTagID),
          Int32Literal(initSorts(id).asInstanceOf[ConstructorSort].typeTag)
        )
      case as@s.ADTSelector(adt, selector) =>
        val s.ADTType(parent, tps) = adt.getType
        val (childId, formalType) = (for {
          ch <- initSorts.values
          if ch.parent.contains(parent)
          fd <- ch.fields
          if fd.id == selector
        } yield (ch.id, fd.tpe)).head
        maybeUnbox(
          RecordSelector(
            CastDown(transform(adt, env), RecordType(childId)),
            selector
          ),
          formalType,
          transform(as.getType, env),
          env
        )

      case s.FunctionInvocation(id, tps, args) =>
        val formals = sym0.functions(id).params.map(_.getType)
        maybeUnbox(
          t.FunctionInvocation(id, Seq(),
            args zip formals map { case (arg, formal) =>
              maybeBox(arg, transform(formal, env), env)
            }
          ),
          transform(sym0.functions(id).returnType, env),
          transform(e.getType, env),
          env
        )

      // Arrays
      case s.FiniteArray(elems, base) =>
        val trBase = transform(base, env)
        val arr = Variable.fresh("array", ArrayType(trBase))
        Let(arr.toVal,
          NewArray(Int32Literal(elems.length), transform(base, env), None),
          Sequence(elems.zipWithIndex.map { case (elem, index) =>
            ArraySet(arr, Int32Literal(index), maybeBox(elem, trBase, env))
          } :+ arr)
        )
      case s.LargeArray(elems, default, size, base) =>
        val trBase = transform(base, env)
        val arr = Variable.fresh("array", ArrayType(trBase))
        Let(arr.toVal,
          NewArray(transform(size, env), transform(base, env), Some( transform(default, env))),
          Sequence( elems.toSeq.sortBy(_._1).map { case (index, elem) =>
            ArraySet(arr, Int32Literal(index), maybeBox(elem, trBase, env))
          } :+ arr)
        )
      case s.ArrayUpdated(array, index, value) =>
        val ArrayType(trBase) = transform(array.getType, env)
        // TODO: Copy functional arrays or analyze when we don't need to do so
        val arr = Variable.fresh("array", ArrayType(trBase))
        Let(arr.toVal, transform(array, env),
          t.Sequence(Seq(
            t.ArraySet(arr, transform(index, env), maybeBox(value, trBase, env)),
            arr
          ) ) )
      case s.ArraySelect(array, index) =>
        val ArrayType(trBase) = transform(array.getType, env)
        maybeUnbox(
          t.ArraySelect(transform(array, env), transform(index, env)),
          trBase,
          transform(e.getType, env),
          env
        )

      // Strings
      case s.StringLiteral(str) =>
        val strV = Variable.fresh("strConst", StrType)
        Let(strV.toVal, NewArray(Int32Literal(str.length), Int32Type(), None),
          Sequence(str.zipWithIndex.map{
            case (ch, index) => ArraySet(strV, Int32Literal(index), Int32Literal(ch.toByte))
          } :+ strV)
        )
      case s.StringConcat(lhs, rhs) =>
        val l = Variable.fresh("lhs", StrType)
        val r = Variable.fresh("rhs", StrType)
        val newArray = Variable.fresh("arr", StrType)
        Let(l.toVal, transform(lhs, env),
          Let(r.toVal, transform(rhs, env),
            Let(
              newArray.toVal,
              NewArray(Plus(ArrayLength(l), ArrayLength(r)), Int32Type(), None),
              Sequence(Seq(
                ArrayCopy(l, newArray, Int32Literal(0), ArrayLength(l)),
                ArrayCopy(r, newArray, ArrayLength(l), Plus(ArrayLength(l), ArrayLength(r))),
                newArray
              ))
            )))
      case s.SubString(expr, start, end) =>
        val startV = Variable.fresh("start", Int32Type())
        val endV = Variable.fresh("end", Int32Type())
        Let(startV.toVal, transform(start, env),
          Let(endV.toVal, transform(end, env),
            ArrayCopy(
              transform(expr, env),
              NewArray(Minus(endV, startV), Int32Type(), None),
              startV,
              endV ) ))

      case s.StringLength(expr) =>
        ArrayLength(transform(expr, env))

      // Tuples
      case s.Tuple(exprs) =>
        transform(s.ADT(
          impSyms.lookup[s.ADTSort](s"Tuple${exprs.size}").constructors.head.id,
          exprs map (_.getType),
          exprs
        ), env)
      case s.TupleSelect(tuple, index) =>
        val size = tuple.getType.asInstanceOf[s.TupleType].bases.size
        val constr = impSyms.lookup[s.ADTSort](s"Tuple$size").constructors.head
        val selector = constr.fields(index - 1).id
        maybeUnbox(
          t.RecordSelector(t.CastDown(transform(tuple, env), RecordType(constr.id)), selector),
          AnyRefType,
          transform(e.getType, env),
          env
        )

      // Sets
      case s.FiniteSet(elements, base) => ???
      case s.SetAdd(set, elem) => ???
      case s.ElementOfSet(element, set) => ???
      case s.SubsetOf(lhs, rhs) => ???
      case s.SetIntersection(lhs, rhs) => ???
      case s.SetUnion(lhs, rhs) => ???
      case s.SetDifference(lhs, rhs) => ???

      // Bags
      case s.FiniteBag(elements, base) => ???
      case s.BagAdd(bag, elem) => ???
      case s.MultiplicityInBag(element, bag) => ???
      case s.BagIntersection(lhs, rhs) => ???
      case s.BagUnion(lhs, rhs) => ???
      case s.BagDifference(lhs, rhs) => ???

      // Maps
      case s.FiniteMap(pairs, default, keyType, valueType) => ???
      case s.MapApply(map, key) => ???
      case s.MapUpdated(map, key, value) => ???

      // We do not translate these for now
      case s.Forall(params, body) => ???
      case s.Choose(res, pred) => ???
      case s.GenericValue(tp, id) => ???

      // These should all be the same:
      // ** All other literals **
      // case s.Variable(id, tpe, flags) =>
      // case s.Let(vd, value, body) =>
      // case s.NoTree(tpe) =>
      // ** Arithmetic operators:
      // case s.Plus(lhs, rhs) =>
      // case s.Minus(lhs, rhs) =>
      // case s.UMinus(expr) =>
      // case s.Times(lhs, rhs) =>
      // case s.Division(lhs, rhs) =>
      // case s.Remainder(lhs, rhs) =>
      // case s.Modulo(lhs, rhs) =>
      // case s.LessThan(lhs, rhs) =>
      // case s.GreaterThan(lhs, rhs) =>
      // case s.LessEquals(lhs, rhs) =>
      // case s.GreaterEquals(lhs, rhs) =>
      // case s.BVNot(e) =>
      // case s.BVAnd(lhs, rhs) =>
      // case s.BVOr(lhs, rhs) =>
      // case s.BVXor(lhs, rhs) =>
      // case s.BVShiftLeft(lhs, rhs) =>
      // case s.BVAShiftRight(lhs, rhs) =>
      // case s.BVLShiftRight(lhs, rhs) =>
      // case s.BVNarrowingCast(expr, newType) =>
      // case s.BVWideningCast(expr, newType) =>
      case _ => super.transform(e, env)
    }
  }
}


/** This transformer transforms stainless trees into a variety of
  *
  * - Strings become arrays of chars
  * - Arrays become mutable
  * - Chars become i8
  * - Booleans and Unit become i32
  * - BigInts become i64 (Currently, will be fixed in the future) (this is done later in the pipeline)
  * - Reals become floats (this is done later in the pipeline)
  * - Composite types become records. Records are extensible structs in memory. See [[Definitions.RecordSort]]
  *
  * TODOs:
  * - We do not copy for ArrayUpdated, rather we do a destructive update
  * - Represent BigInts properly
  * - Implement type representations for composite types based on ADTs/ directly records
  */
class Lowering extends inox.transformers.SymbolTransformer with Transformer {
  private val sortCodes = new inox.utils.UniqueCounter[Unit]
  locally {
    // We want to reserve the first 6 codes for native types
    for {_ <- 0 to 5} sortCodes.nextGlobal
  }

  def transform(sort: s.ADTSort, env: Env): (t.RecordADTSort, Seq[t.ConstructorSort]) = {
    val eqId = FreshIdentifier(s"eq${sort.id.name}")

    val parent = new t.RecordADTSort(transform(sort.id, env)).copiedFrom(sort)

    val children = sort.constructors map { cons =>
      new t.ConstructorSort(
        transform(cons.id, env),
        parent.id,
        sortCodes.nextGlobal,
        cons.fields.map(transform(_, env))
      ).copiedFrom(cons)
    }

    (parent, children)
  }

  private def mkTupleSort(size: Int): s.ADTSort = {
    require(size >= 2)
    val dsl = new inox.ast.DSL { val trees: s.type = s }
    val sortName = SymbolIdentifier(s"Tuple$size")
    val constrName = FreshIdentifier(s"Tuple${size}C")
    dsl.mkSort(sortName)( (1 to size).map(ind => s"T$ind") : _* )( tps =>
      Seq((constrName,
        tps.zipWithIndex.map { case (tpe, ind) =>
          s.ValDef(FreshIdentifier(s"_${ind+1}"), tpe)
        }
      ))
    )
  }

  def transform(syms0: s.Symbols): t.Symbols = {

    // (0) Make tuple sorts
    val syms = syms0.withSorts((2 to 4).map(mkTupleSort))
    val manager = new SymbolsManager
    val env0 = (syms, manager)

    // (1.1) Transform sorts
    val sorts = syms.sorts.values.toSeq.map(transform(_, env0))
    val allSorts = sorts.flatMap(s => s._1 +: s._2).map(s => s.id -> s).toMap

    // (1.2) These are the program types (initial symbols)
    val initSymbols = t.Symbols(allSorts, Map())

    // (2) Transform functions in program
    val tr = new ExprTransformer(manager, keepContracts = true, syms, initSymbols.records)
    val funs = (syms.functions mapValues tr.transform).view.force

    // (3) Put it all together
    val ret = t.Symbols(
      initSymbols.records ++ manager.records + (t.AnyRefSort.id -> t.AnyRefSort),
      funs ++ manager.functions
    )

    //ret.records foreach (r => println(r._2.asString))
    //ret.functions foreach (r => println(r._2.asString))
    //ret.functions.foreach(fn => println(ret.explainTyping(fn._2.fullBody)))
    //println(ret)

    ret
  }
}

