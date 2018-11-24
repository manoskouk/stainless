/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen
package intermediate

import stainless.{FreshIdentifier, Identifier}

trait Transformer extends stainless.transformers.Transformer {
  implicit lazy val printerOptions = t.PrinterOptions(printUniqueIds = true)

  val s = stainless.trees
  val t = trees

  type Env = (s.Symbols, SymbolsManager)

  override def transform(tp: s.Type, env: Env): t.Type = {
    implicit val impSyms = env._1
    import t._
    tp match {
      case s.Untyped => Untyped
      case s.BooleanType() => Int32Type()
      case s.UnitType() => Int32Type()
      case s.CharType() => Int32Type()
      case s.IntegerType() => Int64Type() // FIXME: Implement big integers properly
      case s.StringType() => ArrayType(Int32Type())

      case s.ADTType(id, tps) =>
        RecordType(id)

      case s.FunctionType(from, to) =>
        RecordType(env._2.getFunTypeRecord(
          FunctionType(Seq.fill(from.size)(AnyRefType), AnyRefType)
          //FunctionType(from map (transform(_, env)), transform(to, env))
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

      case s.TypeParameter(id, flags) =>
        RecordType(AnyRefSort.id)

      // These remain as is
      // case s.RealType() =>  TODO: We will represent Reals as floats (?)
      // case s.FunctionType(from, to) =>
      // case s.ArrayType(base) =>
      // case s.BVType(signed, size) =>
      //

      case _ => super.transform(tp, env)
    }
  }
}

private[wasmgen] class SymbolsManager {
  implicit val printerOptions = trees.PrinterOptions(printUniqueIds = true)
  import trees._
  import scala.collection.mutable.{Map => MMap}
  val newFunctions: MMap[Identifier, FunDef] = MMap()
  val newRecords: MMap[Identifier, RecordSort] = MMap()

  private val funRecords = MMap[FunctionType, Identifier]()

  def getFunTypeRecord(ft: FunctionType) =
    funRecords.getOrElseUpdate(ft, {
      val fr = new FunPointerSort(FreshIdentifier("`" + ft.asString(PrinterOptions()) + "`"), ft)
      newRecords += fr.id -> fr
      fr.id
    })

  def getRecord(id: Identifier) = newRecords.get(id)
  def addRecord(r: RecordSort) = newRecords += r.id -> r

  def getFunction(id: Identifier) = newFunctions.get(id)
  def addFunction(fd: FunDef) = newFunctions += fd.id -> fd
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

  private def typeToTag(tpe: t.Type) = tpe match {
    case BVType(_, 32) => 0
    case BVType(_, 64) => 1
    case RealType() => 3
    case FunctionType(_, _) => 4
  }

  private def isElementaryType(tpe: t.Type) = tpe match {
    case t.BVType(_, _) | t.IntegerType() | t.RealType() => true
    case _ => false
  }

  private def maybeBox(e: s.Expr, expected: t.Type, env: Env): t.Expr = {
    implicit val impSyms = env._1
    val trType = transform(e.getType, env)
    val trE = transform(e, env)
    if (isElementaryType(trType) && expected == AnyRefType)
      CastUp(
        Record(
          RecordType(boxedSorts(trType).id),
          Seq(Int32Literal(typeToTag(trType)), trE)),
        AnyRefType
      )
    else if (trType == expected) trE
    else CastUp(trE, AnyRefType)
  }
  private def maybeUnbox(e: t.Expr, real: t.Type, expected: t.Type, env: Env): t.Expr = {
    implicit val impSyms = env._1
    if (isElementaryType(expected) && real == AnyRefType)
      RecordSelector(
        CastDown(e, RecordType(boxedSorts(expected).id)),
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
      case s.BooleanLiteral(value) =>
        Int32Literal(if (value) 1 else 0)
      case s.UnitLiteral() =>
        Int32Literal(0)
      case s.CharLiteral(value) =>
        Int32Literal(value)

      // Misc.
      case s.Annotated(body, flags) =>
        transform(body, env)
      case s.Error(tpe, description) =>
        Sequence(Output(transform(s.StringLiteral(description), env)), NoTree(transform(tpe, env)))
      case me: s.MatchExpr => transform(impSyms.matchToIfThenElse(me), env)
      case s.IfExpr(cond, thenn, elze) =>
        t.IfExprI32(transform(cond, env), transform(thenn, env), transform(elze, env))
      case s.Equals(lhs, rhs) =>
        // Equality is left abstract for now and is lowered later
        t.EqualsI32(transform(lhs, env), transform(rhs, env))

      // Contracts
      case s.Assume(pred, body) =>
        if (keepContracts)
          IfExprI32(transform(pred, env), transform(body, env), NoTree(transform(body.getType, env)))
        else
          transform(body, env)
      case s.Require(pred, body) =>
        transform(s.Assume(pred, body), env)
      case s.Ensuring(body, s.Lambda(Seq(vd), lbody)) =>
        if (keepContracts) {
          val trV = transform(vd, env)
          Let(trV, transform(body, env),
            IfExprI32(transform(lbody, env), trV.toVariable, NoTree(trv.))
          )
        } else {
          transform(body, env)
        }
      case s.Assert(pred, error, body) =>
        if (keepContracts)
          IfExprI32(
            transform(pred, env),
            transform(body, env),
            Error(transform(body.getType, env), error getOrElse "")
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
        val funRecId = manager.getFunTypeRecord(boxedFunType)

        val envIds = fv.map(_.freshen)
        val closureRecord = new ClosureSort(funRecId, envIds)
        manager.addRecord(closureRecord)

        val funRecordType = RecordType(funRecId)
        val closureType = RecordType(closureRecord.id)

        val function = {
          def extractEnv(env: Variable, body: Expr) = {
            val castEnv = ValDef.fresh("env", closureType)
            Let(
              castEnv,
              CastDown(env, closureType),
              fv.zip(envIds).foldRight(body) { case ((v, envId), rest) =>
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
              extractEnv(envParam.toVariable,
                unboxParams(boxedParams,
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
      case s.And(exprs) => exprs.map(transform(_, env)).reduceRight(BVAnd)
      case s.Or(exprs)  => exprs.map(transform(_, env)).reduceRight(BVOr)
      case s.Implies(lhs, rhs) => transform(s.Or(lhs, s.Not(rhs)), env)
      case s.Not(expr) => BVNot(transform(expr, env))

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
        EqualsI32(
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
        val arr = Variable.fresh("array", ArrayType(transform(base, env)))
        Let(arr.toVal,
          NewArray(Int32Literal(elems.length), transform(base, env), None),
          elems.zipWithIndex.map{
            case (elem, index) => ArraySet(arr, Int32Literal(index), transform(elem, env))
          }.reduceRight(Sequence)
        )
      case s.LargeArray(elems, default, size, base) =>
        val arr = Variable.fresh("array", ArrayType(transform(base, env)))
        Let(arr.toVal,
          NewArray(transform(size, env), transform(base, env), Some( transform(default, env))),
          elems.map{
            case (index, elem) => ArraySet(arr, Int32Literal(index), transform(elem, env))
          }.reduceRight(Sequence)
        )
      case s.ArrayUpdated(array, index, value) =>
        // TODO: Copy functional arrays or analyze when we don't need to do so
        t.ArraySet(transform(array, env), transform(index, env), transform(value, env))

      // Strings
      case s.StringLiteral(str) =>
        val strV = Variable.fresh(str, StrType)
        Let(strV.toVal, NewArray(Int32Literal(str.length), Int32Type(), None),
          str.zipWithIndex.map{
            case (ch, index) => ArraySet(strV, Int32Literal(index), Int32Literal(ch.toByte))
          }.reduceRight(Sequence)
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
              Sequence(
                ArrayCopy(l, newArray, Int32Literal(0), ArrayLength(l)),
                ArrayCopy(r, newArray, ArrayLength(l), Plus(ArrayLength(l), ArrayLength(r)))
              )
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
          impSyms.lookup[s.ADTSort](s"Tuple${exprs.size}").id,
          exprs map (_.getType), exprs
        ), env)
      case s.TupleSelect(tuple, index) =>
        val size = tuple.getType.asInstanceOf[s.TupleType].bases.size
        val id = impSyms.lookup[s.ADTSort](s"Tuple$size").constructors(index - 1).id
        transform(s.ADTSelector(tuple, id), env)

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

      // These should all be the same
      // ** All other literals **
      // case s.Variable(id, tpe, flags) =>
      // case s.Let(vd, value, body) =>
      // case s.NoTree(tpe) =>
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
class RecordAbstractor extends inox.transformers.SymbolTransformer with Transformer {

  def transform(sort: s.ADTSort, env: Env): (t.RecordADTSort, Seq[t.ConstructorSort]) = {
    val sortCodes = new inox.utils.UniqueCounter[Unit]
    locally {
      // We want to reserve the first 5 codes for native types
      sortCodes.nextGlobal // i32
      sortCodes.nextGlobal // i64
      sortCodes.nextGlobal // f32
      sortCodes.nextGlobal // f64
      sortCodes.nextGlobal // anyfun
    }

    val eqId = FreshIdentifier(s"eq${sort.id.name}")

    val parent = new t.RecordADTSort(
      transform(sort.id, env),
      eqId
    ).copiedFrom(sort)

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

  private def mkEquality(
    sort: t.ConstructorSort
  )(implicit syms: t.Symbols): t.FunDef = {
    val codeId = sort.fields.head.id
    import t._
    def genEq(e1: Expr, e2: Expr): Expr = {
      e1.getType match {
        case RecordType(id) => FunctionInvocation(id, Seq(), Seq(e1, e2))
        case _ => EqualsI32(e1, e2)
      }
    }

    val dsl = new inox.ast.DSL { val trees: t.type = t }
    dsl.mkFunDef(FreshIdentifier("__eq_" + sort.id.uniqueName))()( _ =>
      (
        Seq (
          ValDef(FreshIdentifier("v1"), AnyRefType),
          ValDef(FreshIdentifier("v2"), AnyRefType)
        ),
        Int32Type(),
        { case Seq(v1, v2) =>

          ( EqualsI32(RecordSelector(v1, typeTagID), RecordSelector(v2, typeTagID)) +:
            sort.fields.map( f =>
              genEq(
                RecordSelector(CastDown(v1, RecordType(sort.id)), f.id),
                RecordSelector(CastDown(v2, RecordType(sort.id)), f.id)
              )
            )).reduceLeft(IfExprI32(_, Int32Literal(1), _)
          )
        }
      )
    )
  }

  private def mkTupleSort(size: Int): s.ADTSort = {
    require(size >= 2)
    val dsl = new inox.ast.DSL { val trees: s.type = s }
    val sortName = FreshIdentifier(s"Tuple$size")
    val constrName = FreshIdentifier(s"Tuple${size}C")
    dsl.mkSort(sortName)( (1 to size).map(ind => s"T$ind") : _* )( tps =>
      Seq((constrName,
        tps.zipWithIndex.map { case (tpe, ind) =>
          s.ValDef(FreshIdentifier(s"_${ind+1}"), tpe)
        }
      ))
    )
  }

  //private def discoverFunSorts(fd: s.Expr)(implicit syms: s.Symbols): Map[s.FunctionType, t.ClosureSort] = {
  //  s.exprOps.collect( expr =>
  //    expr.getType match {
  //      case ft: s.FunctionType => Set(ft ->
  //        new t.FunPointerSort(FreshIdentifier(ft.asString(s.PrinterOptions())), ft)
  //      )
  //      case _ => Set()
  //    }
  //  )
  //  Map()
  //}

  def transform(syms0: s.Symbols): t.Symbols = {
    // (0) Make tuple sorts
    val syms = syms0.withSorts((2 to 8).map(mkTupleSort))
    val manager = new SymbolsManager
    val env0 = (syms, manager)

    // (1.1) Transform sorts
    val sorts = syms.sorts.values.toSeq.map(transform(_, env0))
    val allSorts = sorts.flatMap(s => s._1 +: s._2).map(s => s.id -> s).toMap

    // (1.2) Find function sorts
    val funSorts = Map() //syms.functions.values.toSeq
      //.map(fd => discoverFunSorts(fd.body.get))
      //.foldLeft(Map[s.FunctionType, t.ClosureSort]())(_ ++ _)

    // (1.2) These are the program types (initial symbols)
    val initSymbols = t.Symbols(allSorts ++ t.builtinSortsMap, Map())

    // (2.1) Make equalities for sorts
    //val eqsMap = sorts.map(s => s._1.id -> s._1.flags.collectFirst{ case t.HasADTEquality(id) => id }.get).toMap
    //val equalities = sorts
    //  .map { case (sort, constructors) => mkEquality(sort, constructors, eqsMap)(initSymbols)}
    //  .map(f => f.id -> f)
    //  .toMap

    // (2.2) Transform functions in program

    val tr = new ExprTransformer(manager, keepContracts = true, syms, initSymbols.records)
    val funs = (syms.functions mapValues tr.transform).view.force

    // (3.1) Put it all together
    val ret = t.Symbols(
      initSymbols.records ++ manager.newRecords,
      /*equalities ++*/ funs ++ manager.newFunctions
    )

    //println(ret.asString)
    //println("*** MANAGER ***")
    //manager.newRecords foreach (r => println(r._2.asString))
    //println("*** RECORDS ***")
    //ret.records foreach (r => println(r._2.asString))
    //ret.functions foreach (r => println(r._2.asString))
    //ret.functions.foreach(fn => println(ret.explainTyping(fn._2.fullBody)))
    //println(ret)

    ret
  }
}


