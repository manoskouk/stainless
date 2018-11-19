/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen
package intermediate

import stainless.{FreshIdentifier, Identifier}

trait Transformer extends stainless.transformers.Transformer {
  val s = stainless.trees
  val t = trees

  type Env = s.Symbols

  override def transform(tp: s.Type, env: s.Symbols): t.Type = {
    implicit val impEnv = env
    import t._
    tp match {
      case s.Untyped => Untyped
      case s.BooleanType() => IndexType()
      case s.UnitType() => IndexType()
      case s.CharType() => Int8Type()
      case s.IntegerType() => Int64Type() // FIXME: Implement big integers properly
      case s.StringType() => ArrayType(Int8Type())

      case s.ADTType(id, tps) =>
        RecordType(id, tps map (transform(_, env)))

      case s.TupleType(bases) =>
        RecordType(
          env.lookup[s.ADTSort](s"Tuple${bases.size}").id,
          bases map ( tp => transform(tp.getType, env))
        )
      case s.SetType(base) => ???
      case s.BagType(base) => ???
      case s.MapType(from, to) => ???

      case s.PiType(params, to) =>
        FunctionType(
          params.map(p => transform(p.getType, env)),
          transform(to.getType, env)
        )
      case s.SigmaType(params, to) =>
        transform(s.TupleType(params.map(_.getType) :+ to.getType(env)), env)
      case s.RefinementType(vd, prop) =>
        transform(vd.getType, env)

      // These remain as is
      // case s.RealType() =>  TODO: We will represent Reals as floats (?)
      // case s.FunctionType(from, to) =>
      // case s.ArrayType(base) =>
      // case s.BVType(signed, size) =>
      // case s.TypeParameter(id, flags) =>

      case _ => super.transform(tp, env)
    }
  }
}

private[wasmgen] class SymbolsManager {
  import trees._
  import scala.collection.mutable.{Map => MMap}
  val newFunctions: MMap[Identifier, FunDef] = MMap()
  val newRecords: MMap[Identifier, RecordSort] = MMap()

  private val funRecords = MMap[FunctionType, Identifier]()

  def getFunTypeRecord(ft: FunctionType) =
    funRecords.getOrElseUpdate(ft, {
      val fr = new FunPointerSort(FreshIdentifier(ft.asString(PrinterOptions())), ft)
      newRecords += fr.id -> fr
      fr.id
    })

  def getRecord(id: Identifier) = newRecords.get(id)
  def addRecord(r: RecordSort) = newRecords += r.id -> r

  def getFunction(id: Identifier) = newFunctions.get(id)
  def addFunction(fd: FunDef) = newFunctions += fd.id -> fd
}


private [wasmgen] class ExprTransformer
    (manager: SymbolsManager, keepContracts: Boolean, sym0: stainless.trees.Symbols)
    (implicit  sym: trees.Symbols)
  extends Transformer
{
  import t._
  private val StrType = ArrayType(Int8Type())
  private def mkIndex(i: Int) = BVLiteral(false, 32, i)
  def initEnv = sym0

  def transform(fd: s.FunDef): t.FunDef = {
    new t.FunDef(
      transform(fd.id, initEnv),
      fd.tparams map (transform(_, initEnv)),
      fd.params map (transform(_, initEnv)),
      transform(fd.returnType, initEnv),
      transform(fd.fullBody, initEnv),
      fd.flags map (transform(_, initEnv))
    ).copiedFrom(fd)
  }

  override def transform(e: s.Expr, env: Env): Expr = {
    implicit val impEnv = env
    e match {
      // Misc.
      case s.BooleanLiteral(value) =>
        if (value) mkIndex(1) else mkIndex(0)
      case s.UnitLiteral() =>
        mkIndex(0)
      case s.CharLiteral(value) =>
        Int8Literal(value.toByte)
      case s.Annotated(body, flags) =>
        transform(body, env)
      case s.Error(tpe, description) =>
        Sequence(Output(transform(s.StringLiteral(description), env)), NoTree(transform(tpe, env)))
      case me: s.MatchExpr => sym.matchToIfThenElse(transform(me, env))
      case s.Equals(lhs, rhs) =>
        val tl = transform(lhs, env)
        val tr = transform(rhs, env)
        tl.getType match {
          case t.RecordType(record, tps) =>
            val eqFun = sym.getRecord(record).flags.collectFirst{ case HasADTEquality(id) => id }.get
            FunctionInvocation(eqFun, tps, Seq(tl, tr))
          case _ =>
            Equals(tl, tr)  // TODO: This will cover numeric types and arrays
        }

      // Contracts
      case s.Assume(pred, body) =>
        if (keepContracts)
          IfExpr(transform(pred, env), transform(body, env), NoTree(transform(body.getType, env)))
        else
          transform(body, env)
      case s.Require(pred, body) =>
        if (keepContracts)
          IfExpr(transform(pred, env), transform(body, env), NoTree(transform(body.getType, env)))
        else
          transform(body, env)
      case s.Ensuring(body, s.Lambda(s.ValDef(id, tp, _), lbody)) =>
        if (keepContracts) {
          val trV = Variable(id, transform(tp, env), Seq())
          Let(trV.toVal, transform(body, env),
            IfExpr(transform(lbody, env), trV, NoTree(trV.getType))
          )
        } else {
          transform(body, env)
        }
      case s.Assert(pred, error, body) =>
        if (keepContracts)
          IfExpr(
            transform(pred, env),
            transform(body, env),
            Error(transform(body.getType, env), error getOrElse "")
          )
        else transform(body, env)

      // Higher-order
      case s.Application(callee, args) =>
        val tCallee = transform(callee, env)
        val vCallee = Variable.fresh("fun", tCallee.getType)
        Let(vCallee.toVal, tCallee,
          Application(
            RecordSelector(vCallee, funPointerId),
            vCallee +: args.map(transform(_, env))
          )
        )
      case lmd@s.Lambda(params, body) =>
        val funType = transform(lmd.getType, env).asInstanceOf[FunctionType]
        val fv = (s.exprOps.variablesOf(body).map(_.toVal) -- params).toSeq.map(transform(_, env))

        // Make/find a RecordSort for this function type, and one with the specific env.
        val funRecId = manager.getFunTypeRecord(funType)

        val funName = FreshIdentifier("lambda")

        val envIds = fv.map(_.freshen)
        val closureRecord = new ClosureSort(funRecId, envIds)
        manager.addRecord(closureRecord)

        val funRecordType = RecordType(funRecId, Seq())
        val closureType = RecordType(closureRecord.id, Seq())

        val function = {

          val envArg  = ValDef.fresh("env", funRecordType)
          val envArg2 = ValDef.fresh("env", closureType)

          // New function body has to copy environment to local variables
          val extrEnv = fv.zip(envIds).foldRight(transform(body, env)) { case ((v, envId), rest) =>
            Let(v, RecordSelector(envArg2.toVariable, envId.id), rest)
          }

          val fullBody = Let(envArg2, CastDown(envArg.toVariable, closureType), extrEnv)

          val fd = new FunDef(
            FreshIdentifier("lambda"), Seq(),
            envArg +: params.map(transform(_, env)),
            funType.to,
            fullBody,
            Seq(Dynamic)
          )

          manager.addFunction(fd)
          fd
        }

        val closure = {
          CastUp(
            Record(
              closureType,
              FunctionPointer(function.id) +: fv.map(_.toVariable)
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
        // Except constructor fields, we also store the i32 code corresponding to this constructor
        val constrCode = sym.getRecord(id).asInstanceOf[ConstructorSort].code
        val tpe = RecordType(id, tps map (transform(_, env)))
        CastUp(
          Record(tpe, mkIndex(constrCode) +: args.map(transform(_, env))),
          tpe.parent.get
        )
      case s.IsConstructor(expr, id) =>
        // We need to compare the constructor code of given value
        // to the code corresponding to constructor 'id'
        Equals(
          RecordSelector(transform(expr, env), adtCodeID),
          mkIndex(sym.getRecord(id).asInstanceOf[ConstructorSort].code)
        )
      case as@s.ADTSelector(adt, selector) =>
        val s.ADTType(parent, tps) = as.getType
        val childId = sym.childrenOf(parent).find(_.fields.exists(_.id == selector)).get.id
        RecordSelector(
          CastDown(transform(adt, env), RecordType(childId, tps map (transform(_, env)))),
          selector
        )

      // Arrays
      case s.FiniteArray(elems, base) =>
        val arr = Variable.fresh("array", ArrayType(transform(base, env)))
        Let(arr.toVal,
          NewArray(IndexLiteral(elems.length), transform(base, env), None),
          elems.zipWithIndex.map{
            case (elem, index) => ArraySet(arr, IndexLiteral(index), transform(elem, env))
          }.reduceRight(Sequence)
        )
      case s.LargeArray(elems, default, size, base) =>
        val arr = Variable.fresh("array", ArrayType(transform(base, env)))
        Let(arr.toVal,
          NewArray(transform(size, env), transform(base, env), Some( transform(default, env))),
          elems.map{
            case (index, elem) => ArraySet(arr, IndexLiteral(index), transform(elem, env))
          }.reduceRight(Sequence)
        )
      case s.ArrayUpdated(array, index, value) =>
        // TODO: Copy functional arrays or analyze when we don't need to do so
        t.ArraySet(transform(array, env), transform(index, env), transform(value, env))

      // Strings
      case s.StringLiteral(str) =>
        val strV = Variable.fresh(str, StrType)
        Let(strV.toVal, NewArray(IndexLiteral(str.length), ByteType(), None),
          str.zipWithIndex.map{
            case (ch, index) => ArraySet(strV, IndexLiteral(index), Int8Literal(ch.toByte))
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
              NewArray(Plus(ArrayLength(l), ArrayLength(r)), ByteType(), None),
              Sequence(
                ArrayCopy(l, newArray, mkIndex(0), ArrayLength(l)),
                ArrayCopy(r, newArray, ArrayLength(l), Plus(ArrayLength(l), ArrayLength(r)))
              )
            )))
      case s.SubString(expr, start, end) =>
        val startV = Variable.fresh("start", IndexType())
        val endV = Variable.fresh("end", IndexType())
        Let(startV.toVal, transform(start, env),
          Let(endV.toVal, transform(end, env),
            ArrayCopy(
              transform(expr, env),
              NewArray(Minus(endV, startV), ByteType(), None),
              startV,
              endV ) ))

      case s.StringLength(expr) =>
        ArrayLength(transform(expr, env))

      // Tuples
      case s.Tuple(exprs) =>
        transform(s.ADT(
          env.lookup[s.ADTSort](s"Tuple${exprs.size}").id,
          exprs map (_.getType), exprs
        ), env)
      case s.TupleSelect(tuple, index) =>
        val size = tuple.getType.asInstanceOf[s.TupleType].bases.size
        val id = env.lookup[s.ADTSort](s"Tuple$size").constructors(index - 1).id
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
      // case s.IfExpr(cond, thenn, elze) =>
      // case s.FunctionInvocation(id, tps, args) => ???
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
object RecordAbstractor extends inox.transformers.SymbolTransformer with Transformer {
 
  def transform(sort: s.ADTSort, env: Env): (t.RecordADTSort, Seq[t.ConstructorSort]) = {
    val eqId = FreshIdentifier(s"eq${sort.id.name}")

    val parent = new t.RecordADTSort(
      transform(sort.id, env),
      sort.tparams map (transform(_, env)),
      eqId
    ).copiedFrom(sort)

    val children = sort.constructors.zipWithIndex map { case (cons, ind) =>
      new t.ConstructorSort(
        transform(cons.id, env),
        parent.id,
        ind,
        parent.tparams,
        cons.fields.map(transform(_, env))
      ).copiedFrom(cons)
    }

    (parent, children)
  }

  private def mkEquality(
    sort: t.RecordADTSort,
    children: Seq[t.ConstructorSort],
    sortsToEqs: Map[Identifier, Identifier]
  )(implicit syms: t.Symbols): t.FunDef = {
    import t._
    def genEq(e1: Expr, e2: Expr): Expr = e1.getType match {
      case RecordType(id, tps) => FunctionInvocation(sortsToEqs(id), tps, Seq(e1, e2))
      case _ => Equals(e1, e2)
    }
    def cse(child: ConstructorSort)(v1: Variable, v2: Variable) = {
      val ff = child.flattenFields
      val code = ff.head.id
      val fields = ff.tail.map(_.id)
      And(Seq(
        Equals(RecordSelector(v1, code), Int32Literal(child.code)),
        Equals(RecordSelector(v2, code), Int32Literal(child.code))
      ) ++
        fields.map(fld => genEq(RecordSelector(v1, fld), RecordSelector(v2, fld)))
      )
    }
    val dsl = new inox.ast.DSL { val trees: t.type = t }
    dsl.mkFunDef(sortsToEqs(sort.id))(sort.tparams.map(_.id.name): _*)( tps =>
      (
        Seq (
          ValDef(FreshIdentifier("v1"), RecordType(sort.id, tps)),
          ValDef(FreshIdentifier("v2"), RecordType(sort.id, tps)) ),
        BooleanType(),
        { case Seq(v1, v2) => Or(children map (cse(_)(v1, v2))) }
      )
    )
  }

  private def mkTupleSort(size: Int): s.ADTSort = {
    require(size >= 2)
    val dsl = new inox.ast.DSL { val trees: s.type = s }
    val name = FreshIdentifier(s"Tuple$size")
    dsl.mkSort(name)( (1 to size).map(ind => s"T$ind") : _* )( tps =>
      Seq((name,
        tps.zipWithIndex.map { case (tpe, ind) =>
          s.ValDef(FreshIdentifier(s"_${ind+1}"), tpe)
        }
      ))
    )

  }

  def transform(syms0: s.Symbols): t.Symbols = {
    // (0) Make tuple sorts
    val syms = syms0.withSorts((2 to 8).map(mkTupleSort))

    // (1.1) Transform sorts
    val sorts = syms.sorts.values.toSeq.map(transform(_, syms))
    val allSorts = sorts.flatMap(s => s._1 +: s._2).map(s => s.id -> s).toMap

    // (1.2) These are the program types (initial symbols)
    val initSymbols = t.Symbols(allSorts, Map())

    // (2.1) Make equalities for sorts
    val eqsMap = sorts.map(s => s._1.id -> s._1.flags.collectFirst{ case t.HasADTEquality(id) => id }.get).toMap
    val equalities = sorts
      .map { case (sort, constructors) => mkEquality(sort, constructors, eqsMap)(initSymbols)}
      .map(f => f.id -> f)
      .toMap

    // (2.2) Transform functions in program
    val manager = new SymbolsManager
    val tr = new ExprTransformer(manager, keepContracts = true, syms)(initSymbols)
    val funs = syms.functions mapValues tr.transform

    // (3.1) Put it all together
    t.Symbols(
      initSymbols.records ++ manager.newRecords,
      equalities ++ funs ++ manager.newFunctions
    )
  }
}


